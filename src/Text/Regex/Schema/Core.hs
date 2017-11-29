{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Text.Regex.Schema.Core
where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader

import Data.Set.CharSet
import Data.Monoid (Monoid(..), (<>))

import Text.Regex.Schema.StringLike

-- ------------------------------------------------------------

data RE
  = Zero ErrMsg             -- {}
  | Unit                    -- {&epsilon;}
  | Dot                     -- whole Alphabet
  | Syms      CharSet       -- {a,b,c,...}
  | Star      RE Bool   -- r* / r*?   -- True: shortest match
  | Plus      RE Bool   -- r+ / r+?
  | Seq       RE RE -- r1 . r2
  | Or        RE RE -- r1 | r2
  | Isect     RE RE -- r1 & r2
  | Diff      RE RE -- r1 - r2
  | BsubRE    Label
  | EsubRE
--  | SubRE     RE Label  -- submatch
--  | OpenSub   RE Label String  -- TODO: generalize -- open subexpr with string and len of submatch
--  | ClosedSub RE [(Label, String)]  -- TODO: generalize -- list of completely parsed submatches
  deriving (Eq, Ord, Read, Show)

-- instance Show RE where  show = showRegex 0

type ErrMsg = String
type Label  = String

instance Monoid RE where
  mempty  = unit
  mappend = seq'
  mconcat = foldr seq' unit

-- <> is sequ(ence)

-- ----------------------------------------

newtype Context = CX ()

deriving instance Show Context

instance Monoid Context where
  mempty = CX ()
  CX x `mappend` CX y = CX $ x <> y

-- ----------------------------------------

data REX a = REX (Context -> [a])

instance Monad REX where
  return x      = REX $ \ _cx -> [x]

  REX cxf >>= f = REX $ \ cx ->
                       let ys = map f (cxf cx)
                       in
                         concatMap (\ (REX cxf') -> cxf' cx) ys

instance MonadPlus REX where
  mzero         = REX $ const []

  REX cxf1 `mplus` REX cxf2
                = REX $ \ cx -> cxf1 cx ++ cxf2 cx

instance MonadReader Context REX where
  ask           = REX $ \ cx -> [cx]
  local f (REX cxf)
                = REX $ \ cx -> cxf (f cx)

instance Alternative REX where
  empty = mzero
  (<|>) = mplus

instance Applicative REX where
  pure  = return
  (<*>) = ap

instance Functor REX where
  fmap f (REX sf)
                = REX $ \ cx ->
                          let xs = sf cx
                          in map f xs

runREX :: REX a -> Context -> [a]
runREX (REX cxf) = cxf

-- ----------------------------------------

data SubMatches
  = SM { closedSubs :: [(Label, String)] -- TODO: remove doublicates
       , openSubs   :: [(Label, String)]
       }
  deriving Show

emptySubMatches :: SubMatches
emptySubMatches = SM [] []

type RENF = (SubMatches, RE)

toNF' :: SubMatches -> RE -> REX (SubMatches, RE)
toNF' sm re = (\ r -> (sm, r)) <$> toNF re

toNF :: RE -> REX RE
toNF (Or r1 r2)               = toNF r1
                                <|>
                                toNF r2

toNF (Star r shortest)
  | (Star r1 s1) <- r         = toNF (star' (plus' r1 s1) (shortest && s1))
  | shortest                  = return Unit
                                <|>
                                toNF (plus' r True)
  | otherwise                 = toNF (plus' r False)  -- longest match
                                <|>
                                return Unit

toNF (Plus r b)               = toNF (r <> (star' r b))

toNF r0@(Diff r1 r2)          = toNF r1
                                >>=
                                \ r' -> toREX (r' `diff` r2)

toNF r0@(Seq r1 r2)          = case r1 of
  Or r11 r12                 -> toNF (r11 <> r2)
                                <|>
                                toNF (r12 <> r2)
  Star r1 shortest
    | shortest               -> toNF r2
                                <|>
                                toNF (plus' r1 True  <> r2)
    | otherwise              -> toNF (plus' r1 False <> r2) --longest match
                                <|>
                                toNF r2
  Plus r11 b                 -> toNF (r11 <> star' r11 b <> r2)
  Diff r11 r12               -> toNF r11
                                >>=
                                \ r' -> toREX ((r' `diff` r12) <> r2)
  Seq  r11 r12               -> toNF (r11 <> r12 <> r2)
  Syms _                     -> return r0
  Dot                        -> return r0
  Zero _                     -> empty
  Unit                       -> toNF r2
  BsubRE _                   -> return r0   -- must be simplified earlier
  EsubRE                     -> return r0   --   "  "       "       "
  _                          -> error $ "toNF: no NF found for " ++ showRegex 0 r0

toNF (Zero _)                 = empty
toNF r0@Dot                   = return r0
toNF r0@Unit                  = return r0
toNF r0@(Syms _cs)            = return r0

toNF r  = error $ "toNF: no NF found for " ++ showRegex 0 r

-- ----------------------------------------

toREX :: RE -> REX RE
toREX (Zero _) = empty
toREX r        = return r

-- ----------------------------------------
--
-- search for a leading BsubRE's
-- and insertion of label into open submatches

openSubRE :: Tr (SubMatches, RE)
openSubRE =
  evalSubRE isBsub addSub
  where
    isBsub (BsubRE _) = True
    isBsub _          = False

    addSub sm (BsubRE l) = sm {openSubs = (l, "") : openSubs sm}

openSubREs :: Tr (SubMatches, RE)
openSubREs = repeatTr openSubRE

closeSubRE :: Tr (SubMatches, RE)
closeSubRE =
  evalSubRE isEsub closeSub
  where
    isEsub EsubRE = True
    isEsub _      = False

    closeSub sm _ =  SM { closedSubs = cm'
                        , openSubs   = om'
                        }
      where
        (l, s) : om' = openSubs sm
        cm'          = (l, s) : closedSubs sm

-- evaluate action for a leading pseudo regex (BsubRE, EsubRE, ...)
-- and remove it from the re
evalSubRE :: (RE -> Bool) ->
             (SubMatches -> RE -> SubMatches) ->
             Tr (SubMatches, RE)
evalSubRE p sub e@(sm, r) =
  case splitFstRE p r of
    Nothing       -> return (noChange, e)
    Just (r1, r2) -> do r' <- toNF r2
                        return (hasChanged, (sub sm r1, r'))


-- split the leftmost sub regex (BsubRE, EsubRE, ...) from a regex
-- type of re is determined by predicate p

splitFstRE :: (RE -> Bool) -> RE -> Maybe (RE, RE)
splitFstRE p = go
  where
    go r
      | True <- p r        = Just (r, Unit)
    go (Seq r1 r2)
      | True <- p r1       = Just (r1, r2)
    go (Seq  r1 r2)        = (\ (b, r1') -> (b, r1'  <>    r2))
                             <$>
                             go r1
    go (Diff r1 r2)        = (\ (b, r1') -> (b, r1' `diff` r2))
                             <$>
                             go r1
    go _                   = Nothing


-- ----------------------------------------
--
-- smart constructors used in toNF

seq' :: RE -> RE -> RE
seq' r1@(Zero _)   _  = r1
seq' _    r2@(Zero _) = r2
seq' Unit          r2 = r2
seq' r1          Unit = r1
seq' (Seq r11 r12) r2 = seq' r11 (seq' r12 r2)
seq' r1            r2 = Seq r1 r2

diff :: RE -> RE -> RE
diff r1         (Zero _)   = r1
diff r1@(Zero _)      _    = r1
diff Unit             r2
  | nullable r2             = noMatch
diff r1 Unit
  | not (nullable r1)       = r1
diff (Diff r11 r12)   r2   = r11 `diff` (r12 `alt` r2)
diff (Syms cs1) (Syms cs2) = syms (cs1 `diffCS` cs2)
diff Dot        (Syms cs2) = syms (compCS cs2)
diff (Syms cs1) Dot        = noMatch
diff r1 r2
  | r1 == r2                = r1
  | otherwise               = Diff r1 r2

star'                    :: RE -> Bool -> RE
star' (Zero _)       _  = unit                  -- {}* == ()
star' r@Unit         _  = r                     -- ()* == ()
star' (Star r1 _)    s  = star' r1 s
star' (Plus r1 _)    s  = star' r1 s
star' r              s
  | nullable r          = star' (r `diff` Unit)  s
  | otherwise           = Star r s

plus'                   :: RE -> Bool -> RE
plus' r@(Zero _)     _  = r                     -- {}+ == {}
plus' r@Unit         _  = r                     -- ()+ == ()
plus' (Star r1 _)    s  = star' r1 s            -- (r*)+ == r*
plus' (Plus r1 _)    s  = plus' r1 s            -- (r+)+ == r+
plus' r              s
  | nullable r          = star' (r `diff` Unit) s
  | otherwise           = Plus r s

-- ------------------------------------------------------------
--
-- smart constructors for basic RE's

zero :: ErrMsg -> RE
zero = Zero

noMatch :: RE
noMatch = zero "no match"

unit :: RE
unit = Unit

dot :: RE
dot = Dot

syms :: CharSet -> RE
syms = Syms

sym :: Char -> RE
sym = syms . singleCS

symRng :: Char -> Char -> RE
symRng lb ub = syms $ rangeCS lb ub

-- --------------------

subRE :: Label -> RE -> RE
subRE l r = BsubRE l <> r <> EsubRE

{-
openSub :: RE -> Label -> RE
openSub (Or r1 r2) l = openSub r1 l .|. openSub r2 l
openSub r l = OpenSub r l ""

contSub :: RE -> Label -> String -> RE
contSub r@(Zero _)        _ _ = r
contSub (ClosedSub r1 ms) l s = ClosedSub (contSub r1 l s) ms
contSub r                 l s = OpenSub r l s

closedSub :: RE -> [(Label, String)] -> RE
closedSub r@(Zero _)         _  = r
closedSub (ClosedSub r1 ms1) ms = closedSub r1 (ms ++ ms1)
closedSub r ms = ClosedSub r ms
-}
-- --------------------
--
-- smart constructor for sequence

{-
sequ                     :: RE -> RE -> RE
sequ r1@(Zero _)  _      = r1                       -- {}.r  == {}
sequ _ r2@(Zero _)       = r2                       -- r.{}  == {}
sequ Unit r2             = r2                       -- ().r  == r
sequ r1   Unit           = r1                       -- r.()  == r
sequ (Seq r1 r2) r3      = sequ r1 (sequ r2 r3)     -- assoc. of .
sequ (ClosedSub r1 ms) r2= closedSub (sequ r1 r2) ms -- propagate submatches upwards
sequ r1   r2             = Seq r1 r2
-}

-- --------------------
--
-- smart constructor for * and +

star            :: RE -> RE
star r          = star' r False

plus            :: RE -> RE
plus r          = plus' r False

-- shortest match
starSM          :: RE -> RE
starSM r        = star' r False

plusSM          :: RE -> RE
plusSM r        = plus' r False

word            :: String -> RE
word            = foldr (\ a b -> sym a <> b) unit

-- --------------------
--
-- smart constructor for alternative
{-
infixr 2 .|.

(.|.)                   :: RE -> RE -> RE
Zero _    .|. r2        = r2                 -- zero
r1        .|. Zero _    = r1                 -- zero
Or r1 r2  .|. r3        = r1 .|. (r2 .|. r3) -- associativity
r1        .|.  r2       = Or r1 r2
-}
-- --------------------
--
-- smart constructor for intersection

infixr 3 .&.

(.&.)                   :: RE -> RE -> RE
z@(Zero _) .&. _r2      = z                  -- {} n r2 = {}
_r1  .&.  z@(Zero _)    = z                  -- r1 n {} = {}

Star Dot _ .&. r2       = r2                 -- A* n r2 = r2
r1       .&. Star Dot _ = r1                 -- r1 n A* = r1

Isect r1 r2 .&. r3      = r1 .&. (r2 .&. r3) -- associativity
r1 .&. r2               = Isect r1 r2

-- ------------------------------------------------------------

-- simplification rules
--
-- implemented with "smart" constructors
-- not all allgebraic laws concerning sets are realized

-- --------------------

alt                   :: RE -> RE -> RE
alt (Zero _) r2       = r2
alt r1 (Zero _)       = r1

alt (Syms cs1) (Syms cs2) = syms (cs1 `unionCS` cs2)
alt (Syms cs1) Dot        = Dot
alt Dot        (Syms cs2) = Dot
alt r1@(Star Dot _) r2    = r1
alt r1 r2@(Star Dot _)    = r2

alt (Or r1 r2) r3         = alt r1 (alt r2 r3)
                                        -- associativity
alt r1 (Or r21 r22)
    | r1 == r21         = alt r1 r22  -- idempotent
--    | r1 > r21          = alt r21 (alt r1 r22)
                                        -- symmetry
alt r1   r2
    | r1 == r2          = r1            -- idempotent
--    | r1 > r2           = alt r2 r1   -- symmetry
    | otherwise         = Or r1 r2

-- --------------------

isect                   :: RE -> RE -> RE
isect z@(Zero _) _      = z
isect _ z@(Zero _)      = z

isect (Star Dot _) r2   = r2
isect r1 (Star Dot _)   = r1

isect (Isect r1 r2) r3  = isect r1 (isect r2 r3)
                                        -- associativity

isect r1 (Isect r21 r22)
    | r1 == r21         = isect r1 r22  -- idempotent
--    | r1 > r21          = isect r21 (isect r1 r22)
                                        -- symmetry

isect r1   r2
    | r1 == r2          = r1            -- idempotent
--    | r1 > r2           = isect r2 r1   -- symmetry
    | otherwise         = Isect r1 r2

-- --------------------
{-
diff                    :: RE -> RE -> RE
diff r1@(Zero _) r2     = r1
diff r1 (Zero _)        = r1
diff r1   r2
    | r1 === r2         = noMatch
    | otherwise         = Diff r1 r2
-}
-- ------------------------------------------------------------
--
-- equivalence: used for itempotent op's:  a `op` a == a
{-
infix 4 ===

(===) :: RE -> RE -> Bool
Zero  _     === Zero _      = True
Unit        === Unit        = True
Syms  c1    === Syms c2     = c1 == c2
Star  r1 m1 === Star r2 m2  = r1 === r2 && m1 ==  m2
Plus  r1 m1 === Plus r2 m2  = r1 === r2 && m1 ==  m2
Seq   r1 s1 === Seq r2 s2   = r1 === r2 && s1 === s2
Or    r1 s1 === Or r2 s2    = r1 === r2 && s1 === s2
Isect r1 s1 === Isect r2 s2 = r1 === r2 && s1 === s2
Diff  r1 s1 === Diff r2 s2  = r1 === r2 && s1 === s2
SubRE r1 l1 === SubRE r2 l2 = r1 === r2 && l1 ==  l2
_           === _           = False
-}
-- ------------------------------------------------------------
--
-- cases sorted by frequency of operators

nullable                :: RE -> Bool

nullable (Seq r1 r2)    = nullable r1
                          &&
                          nullable r2
nullable (Or r1 r2)     = nullable r1
                          ||
                          nullable r2
nullable (Syms _x)      = False
nullable (Zero _)       = False
nullable  Unit          = True
nullable (Plus  r _)    = nullable r
nullable  Dot           = False
nullable (Star  _ _)    = True
nullable (Isect r1 r2)  = nullable r1
                          &&
                          nullable r2
nullable (Diff  r1 r2)  = nullable r1
                          &&
                          not (nullable r2)
nullable (BsubRE _)     = True
nullable  EsubRE        = True

-- ------------------------------------------------------------

delta :: RE -> Char -> RE

delta z@(Zero _) _a      = z

delta Unit _c            = noMatch

delta Dot  _c            = unit

delta (Syms cs) c
  | c `elemCS` cs        = unit
  | otherwise            = noMatch

delta r0@(Star r s) c
  | s                    = delta r c <> (unit      `alt` plus' r s)
  | otherwise            = delta r c <> (plus' r s `alt` unit  )

delta r0@(Plus r s) c
  | s                    = delta (r <> (unit `alt` r0  )) c
  | otherwise            = delta (r <> (r0   `alt` unit)) c

delta (Seq r1 r2) c
  | nullable r1          = dr1 `alt` dr2
  | otherwise            = dr1
                           where
                             dr1 = delta r1 c <> r2
                             dr2 = delta r2 c

delta (Or r1 r2) c       = delta r1 c
                           `alt`
                           delta r2 c

delta (Isect r1 r2) c    = delta r1 c
                           `isect`
                           delta r2 c

delta (Diff r1 r2) c     = delta r1 c
                           `diff`
                           delta r2 c

delta (BsubRE _) c       = noMatch

delta  EsubRE    c       = noMatch

-- ------------------------------------------------------------

delta' :: RE -> String-> RE

delta' re []       = re
delta' re (c : ws) = delta' (delta re c) ws


match1 :: RE -> String -> Bool

match1 re ws = nullable (delta' re ws)

-- ------------------------------------------------------------
--
-- readable output

showR :: RE -> String
showR = showRegex 6

prio    :: RE -> Int
prio (Zero _)    = 0
prio Unit        = 0
prio Dot         = 0
prio (Syms _)    = 0
prio (Star _ _)  = 1
prio (Plus _ _)  = 1
prio (Seq _ _)   = 2
prio (Isect _ _) = 3
prio (Diff _ _)  = 4
prio (Or _ _)    = 5
prio (BsubRE _)  = 0
prio  EsubRE     = 0

showRegex       :: Int -> RE -> String
showRegex p r
    = par $ (showRegex' r)
    where
    pr  = prio r

    sm True = "?"
    sm _    = ""

    par s
        | pr > p         = "(" ++ s ++ ")"
        | otherwise      = s

    showRegex' (Zero _)      = "{}"
    showRegex' Unit          = "()"
    showRegex' Dot           = "."
    showRegex' (Syms cs)     = showCS cs
    showRegex' (Star r1 s)   = showRegex pr r1
                               ++ "*" ++ sm s
    showRegex' (Plus r1 s)   = showRegex pr r1
                               ++ "+" ++ sm s
    showRegex' (Seq r1 r2)   = showRegex pr r1
                               ++
                               showRegex pr r2
    showRegex' (Or r1 r2)   = showRegex pr r1
                               ++ "|" ++
                               showRegex pr r2
    showRegex' (Isect r1 r2) = showRegex pr r1
                               ++ "&" ++
                               showRegex pr r2
    showRegex' (Diff  r1 r2) = showRegex pr r1
                               ++ "-" ++
                               showRegex pr r2
    showRegex' (BsubRE l)    = "(" ++ l ++ ":"
    showRegex'  EsubRE       = ")"
{-
    showRegex' (SubRE r1 l)  = l ++ ":" ++
                               showRegex pr r1
    showRegex' (OpenSub r1 l s)
                             = l ++ "=" ++ s ++ ":" ++
                               showRegex pr r1
    showRegex' (ClosedSub r1 ms)
                             = show ms ++ ":" ++
                               showRegex pr r1
-}
    showCS cs
      | cs == compCS (stringCS "\n\r")
                             = "."
      | null (tail cs)
        &&
        rng1 (head cs)       = escRng . head $ cs
      | otherwise            = "[" ++ concat cs' ++ "]"
                               where
                                 rng1 (x,y)    = x == y
                                 cs'           = map escRng cs

                                 escRng (x, y)
                                   | x == y      = esc x
                                   | succ x == y = esc x        ++ esc y
                                   | otherwise   = esc x ++ "-" ++ esc y

                                 esc x
                                   | x `elem` "\\-[]{}()*+?.^"
                                                 = '\\':x:""
                                   | x >= ' ' && x <= '~'
                                                 = x:""
                                   | otherwise   = "&#" ++ show (fromEnum x) ++ ";"

-- ------------------------------------------------------------


type Tr a = a -> REX (Changed, a)

type Changed = Bool

hasChanged :: Bool
hasChanged = True

noChange :: Bool
noChange = False

runTr :: Tr a -> a -> REX a
runTr f x = snd <$> f x

idTr :: Tr a
idTr = \ x -> return (noChange, x)

andThen :: Tr a -> Tr a -> Tr a
andThen f g x = do
  (changed1, y) <- f x
  (changed2, z) <- g y
  return (changed1 || changed2, z)

onSuccess :: Tr a -> Tr a -> Tr a
onSuccess f g x = do
  res1@(changed1, y) <- f x
  if changed1
    then
    do
      (_changed2, z) <- g y
      return (hasChanged, z)
    else
      return res1

orElse :: Tr a -> Tr a -> Tr a
orElse f g x = do
  res1@(changed1, _y) <- f x
  if changed1
    then
      return res1
    else
      g x

repeatTr :: Tr a -> Tr a
repeatTr f = f `onSuccess` repeatTr f

-- ------------------------------------------------------------
