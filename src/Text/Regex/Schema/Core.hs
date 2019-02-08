{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Text.Regex.Schema.Core
where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer

import Data.Set.CharSet
import Data.Monoid (Monoid(..), (<>), Any(..))

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
  | SubRE     RE Label String
  | CSub    [(Label, String)]

--  | SubRE     RE Label  -- submatch
--  | OpenSub   RE Label String  -- TODO: generalize -- open subexpr with string and len of submatch
--  | ClosedSub RE [(Label, String)]  -- TODO: generalize -- list of completely parsed submatches
  deriving (Eq, Ord, Read) -- , Show)

instance Show RE where  show = showRegex 0

type ErrMsg = String
type Label  = String

instance Semigroup RE where
  (<>) = seq'

instance Monoid RE where
  mempty  = unit
  mconcat = foldr (<>) unit

-- <> is sequ(ence)

-- ----------------------------------------

newtype Context = CX ()

deriving instance Show Context

instance Semigroup Context where
  CX x <> CX y = CX $ x <> y

instance Monoid Context where
  mempty = CX ()

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
toNF' sm re = (sm,) <$> toNF re

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

toNF (Diff r1 r2)             = toNF r1
                                >>=
                                \ r' -> toREX (r' `diff'` r2)

toNF r0@(Seq r1 r2)          = case r1 of
  Or r11 r12                 -> toNF (r11 <> r2)
                                <|>
                                toNF (r12 <> r2)
  Star r11 shortest
    | shortest               -> toNF r2
                                <|>
                                toNF (plus' r11 True  <> r2)
    | otherwise              -> toNF (plus' r11 False <> r2) --longest match
                                <|>
                                toNF r2
  Plus r11 b                 -> toNF (r11 <> star' r11 b <> r2)
  Diff r11 r12               -> toNF r11
                                >>=
                                \ r' -> toREX ((r' `diff'` r12) <> r2)
  Seq  r11 r12               -> toNF (r11 <> r12 <> r2)
  Syms _                     -> return r0
  Dot                        -> return r0
  Zero _                     -> empty
  Unit                       -> toNF r2
  BsubRE _                   -> return r0   -- must be simplified earlier
  EsubRE                     -> return r0   --   "  "       "       "
  _                          -> return r0

toNF (Zero _)                 = empty
toNF r0@Dot                   = return r0
toNF r0@Unit                  = return r0
toNF r0@(Syms _cs)            = return r0
toNF r0@(BsubRE _)            = return r0
toNF r0@(EsubRE)              = return r0

toNF r  = error $ "toNF: no NF found for " ++ showRegex 0 r

-- ----------------------------------------

toREX :: RE -> REX RE
toREX (Zero _) = empty
toREX r        = return r

-- ----------------------------------------
--
-- smart constructors used in toNF

seq'                    :: RE -> RE -> RE
seq' r1@(Zero _)   _    = r1
seq' _    r2@(Zero _)   = r2
seq' Unit          r2   = r2
seq' r1          Unit   = r1
seq' (CSub ms1) r2
  | CSub ms2 <- r2    = CSub $ ms1 ++ ms2
  | (Seq (CSub ms21) r22) <- r2
                        = CSub (ms1 ++ ms21) `seq` r22
seq' (Seq r11 r12) r2   = seq' r11 (seq' r12 r2)
seq' r1            r2   = Seq r1 r2


alt'                    :: RE -> RE -> RE
alt' (Zero _) r2        = r2
alt' r1 (Zero _)        = r1
alt' (Syms cs1) (Syms cs2)
                        = syms (cs1 `unionCS` cs2)
alt' (Syms _)   Dot     = Dot
alt' Dot     (Syms _)   = Dot
alt' (Or r1 r2) r3      = alt' r1 (alt' r2 r3) -- associativity
alt' r1 r2              = Or r1 r2

-- --------------------

diff'                    :: RE -> RE -> RE
diff' r1        (Zero _) = r1
diff' r1@(Zero _)      _ = r1
diff' Unit            r2
  | nullable r2         = noMatch
diff' r1 Unit
  | not (nullable r1)   = r1
diff' (Diff r11 r12) r2 = r11 `diff'` (r12 `alt'` r2)
diff' (Syms cs1) (Syms cs2)
                        = syms (cs1 `diffCS` cs2)
diff' Dot    (Syms cs2) = syms (compCS cs2)
diff' (Syms _) Dot      = noMatch
diff' r1 r2
  | r1 == r2            = r1
  | otherwise           = Diff r1 r2

-- --------------------

star'                    :: RE -> Bool -> RE
star' (Zero _)       _  = unit                  -- {}* == ()
star' r@Unit         _  = r                     -- ()* == ()
star' (Star r1 _)    s  = star' r1 s
star' (Plus r1 _)    s  = star' r1 s
star' r              s
  | nullable r          = star' (r `diff'` Unit)  s
  | otherwise           = Star r s

plus'                   :: RE -> Bool -> RE
plus' r@(Zero _)     _  = r                     -- {}+ == {}
plus' r@Unit         _  = r                     -- ()+ == ()
plus' (Star r1 _)    s  = star' r1 s            -- (r*)+ == r*
plus' (Plus r1 _)    s  = plus' r1 s            -- (r+)+ == r+
plus' r              s
  | nullable r          = star' (r `diff'` Unit) s
  | otherwise           = Plus r s

-- ------------------------------------------------------------
--
-- exported smart constructor


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

-- smart constructor for * and +

star            :: RE -> RE
star r          = star' r False

plus            :: RE -> RE
plus r          = plus' r False

-- shortest match

starSM          :: RE -> RE
starSM r        = star' r True

plusSM          :: RE -> RE
plusSM r        = plus' r True

word            :: String -> RE
word            = foldr (\ a b -> sym a <> b) unit

-- --------------------

subRE :: Label -> RE -> RE
subRE l r = BsubRE l <> r <> EsubRE

subRE'          :: Label -> RE -> RE
subRE' l r      = SubRE r l ""

cSub            :: Label -> String -> RE
cSub l r        = CSub [(l, r)]

diff            :: RE -> RE -> RE
diff            = diff'
-- diff r1 r2             = diff' r1 (remSubmatches r2)

-- --------------------
--
-- regex visitor

data VisitRE a
  = VRE { vZero     :: ErrMsg -> a
        , vUnit     :: a
        , vDot      :: a
        , vSyms     :: CharSet -> a
        , vStar     :: a -> Bool -> a
        , vPlus     :: a -> Bool -> a
        , vSeq      :: a -> a -> a
        , vOr       :: a -> a -> a
        , vIsect    :: a -> a -> a
        , vDiff     :: a -> a -> a
        , vBsubRE   :: Label -> a
        , vEsubRE   :: a
        , vSubRE    :: a -> Label -> String -> a
        , vCSub     :: [(Label, String)] -> a
        }

visitRE                 :: VisitRE a -> RE -> a
visitRE v               = go
  where
    go (Zero e)         = vZero   v e
    go Unit             = vUnit   v
    go Dot              = vDot    v
    go (Syms cs)        = vSyms   v cs
    go (Star r b)       = vStar   v (go r) b
    go (Plus r b)       = vPlus   v (go r) b
    go (Seq   r1 r2)    = vSeq    v (go r1) (go r2)
    go (Or    r1 r2)    = vOr     v (go r1) (go r2)
    go (Isect r1 r2)    = vIsect  v (go r1) (go r2)
    go (Diff  r1 r2)    = vDiff   v (go r1) (go r2)
    go (BsubRE l)       = vBsubRE v l
    go EsubRE           = vEsubRE v
    go (SubRE r l s)    = vSubRE  v (go r) l s
    go (CSub ms)        = vCSub  v ms
{-# INLINE visitRE #-}

type TransformRE = VisitRE RE

idRE            :: TransformRE
idRE            = VRE
  { vZero       = Zero
  , vUnit       = Unit
  , vDot        = Dot
  , vSyms       = Syms
  , vStar       = Star
  , vPlus       = Plus
  , vSeq        = Seq
  , vOr         = Or
  , vIsect      = Isect
  , vDiff       = Diff
  , vBsubRE     = BsubRE
  , vEsubRE     = EsubRE
  , vSubRE      = SubRE
  , vCSub       = CSub
  }
{-# INLINE idRE #-}

nfRE            :: TransformRE
nfRE            = idRE
  { vStar       = star'
  , vPlus       = plus'
  , vSeq        = (<>)
  , vOr         = alt'
  , vIsect      = isect
  , vDiff       = diff'
  }
{-# INLINE nfRE #-}

simpleRE        :: TransformRE
simpleRE        = nfRE
  { vBsubRE     = const Unit
  , vEsubRE     = Unit
  , vSubRE      = \ r _ _ -> r
  , vCSub       = const Unit
  }
{-# INLINE simpleRE #-}

remSubmatches   :: RE -> RE
remSubmatches   = visitRE simpleRE

type PredicateRE = VisitRE Bool

anyRE           :: PredicateRE
anyRE           = VRE
  { vZero       = const False
  , vUnit       = False
  , vDot        = False
  , vSyms       = const False
  , vStar       = \ r _ -> r
  , vPlus       = \ r _ -> r
  , vSeq        = (||)
  , vOr         = (||)
  , vIsect      = (||)
  , vDiff       = (||)
  , vBsubRE     = const False
  , vEsubRE     = False
  , vSubRE      = \ r _ _ -> r
  , vCSub       = const False
  }
{-# INLINE anyRE #-}

allRE           :: PredicateRE
allRE           = VRE
  { vZero       = const True
  , vUnit       = True
  , vDot        = True
  , vSyms       = const True
  , vStar       = \ r _ -> r
  , vPlus       = \ r _ -> r
  , vSeq        = (&&)
  , vOr         = (&&)
  , vIsect      = (&&)
  , vDiff       = (&&)
  , vBsubRE     = const True
  , vEsubRE     = True
  , vSubRE      = \ r _ _ -> r
  , vCSub       = const True
  }
{-# INLINE allRE #-}

submatchRE      :: PredicateRE
submatchRE      = anyRE
  { vBsubRE     = const True
  , vEsubRE     = True
  , vSubRE      = const . const . const $ True
  , vCSub       = const True
  }
{-# INLINE submatchRE #-}

isSimpleRE      :: RE -> Bool
isSimpleRE      = not . visitRE submatchRE

nullable        :: RE -> Bool
nullable        = visitRE epsilonRE

epsilonRE       :: PredicateRE
epsilonRE       = VRE
  { vZero       = const False
  , vUnit       = True
  , vDot        = False
  , vSyms       = const False
  , vStar       = const . const $ True
  , vPlus       = \ r _ -> r
  , vSeq        = (&&)
  , vOr         = (||)
  , vIsect      = (&&)
  , vDiff       = \ r1 r2 -> r1 && not r2
  , vBsubRE     = const True
  , vEsubRE     = True
  , vSubRE      = \ r _ _ -> r
  , vCSub       = const False
  }
{-# INLINE epsilonRE #-}

isCSub          :: RE -> Bool
isCSub          = visitRE cSubRE

cSubRE          :: PredicateRE
cSubRE          = anyRE
  { vStar       = const . const $ False
  , vPlus       = const . const $ False
  , vSeq        = (&&)
  , vOr         = (||)
  , vIsect      = (&&)
  , vDiff       = (&&)
  , vBsubRE     = const False
  , vEsubRE     = False
  , vSubRE      = const . const . const $ False
  , vCSub       = const True
  }
{-# INLINE cSubRE #-}

-- ------------------------------------------------------------

-- simplification rules
--
-- implemented with "smart" constructors
-- not all allgebraic laws concerning sets are realized

-- --------------------
--
-- exported smart constructor
-- does some more optimizations
-- than the internally used alt'

alt                     :: RE -> RE -> RE
alt r1@(Star Dot _) r2
  | isSimpleRE r2       = r1

alt r1 r2@(Star Dot _)
  | isSimpleRE r1       = r2

alt (Or r1 r2) r3       = alt r1 (alt r2 r3) -- associativity

alt r1 (Or r21 r22)
    | r1 == r21         = alt r1 r22  -- idempotent

alt r1   r2
    | r1 == r2          = r1            -- idempotent

alt r1 r2               = alt' r1 r2

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

-- ------------------------------------------------------------
--
-- cases sorted by frequency of operators
{- done with visitor

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
-}

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
  | (CSub _) <- r1       = r1 <> delta r2 c
  | (CSub _) <- r2       = delta r1 c <> r2
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
                           `diff'`
                           delta r2 c

delta (BsubRE _) _c      = noMatch

delta  EsubRE    _c      = noMatch

delta (SubRE r l s) c
  | (Zero _) <- r'       = r'
  | Unit     <- r'       = cSub l s'
  | otherwise            = SubRE r' l s'
    where
      r' = delta r c
      s' = c : s

delta r0@(CSub _) _     = noMatch

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
prio (Zero _)       = 0
prio Unit           = 0
prio Dot            = 0
prio (Syms _)       = 0
prio (Star _ _)     = 1
prio (Plus _ _)     = 1
prio (Seq _ _)      = 2
prio (Isect _ _)    = 3
prio (Diff _ _)     = 4
prio (Or _ _)       = 5
prio (BsubRE _)     = 0
prio  EsubRE        = 0
prio (SubRE _ _ _)  = 0
prio (CSub _)       = 0

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

    showRegex' (SubRE r1 l s) = l ++ s' ++ ":" ++
                                showRegex pr r1
                                where
                                  s' | null s    = s
                                     | otherwise = "=" ++ s
    showRegex' (CSub ms)      = show ms

{-
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

-- ----------------------------------------
--
-- remove submatch ops BsubRE and EsubRE and
-- add submatches to submatch context

deriveSubREs            :: (SubMatches, RE) -> TrRex (SubMatches, RE)
deriveSubREs            = fixTr $ openSubREs >=> closeSubREs

openSubREs              :: (SubMatches, RE) -> TrRex (SubMatches, RE)
openSubREs              = fixTr $ evalSubRE isBsub addSub
  where
    isBsub (BsubRE _)   = True
    isBsub _            = False

    addSub sm (BsubRE l)= sm {openSubs = (l, "") : openSubs sm}
    addSub _  r         = error $ "openSubRE: illegal RE: " ++ show r

closeSubREs             :: (SubMatches, RE) -> TrRex (SubMatches, RE)
closeSubREs             = fixTr $ evalSubRE isEsub closeSub
  where
    isEsub EsubRE       = True
    isEsub _            = False

    closeSub sm EsubRE  =  SM { closedSubs = cm'
                              , openSubs   = om'
                              }
      where
        (l, s) : om'    = openSubs sm
        cm'             = (l, s) : closedSubs sm
    closeSub _sm r      = error $ "closeSubRE: illegal RE: " ++ show r

-- evaluate action for a leading pseudo regex (BsubRE, EsubRE, ...)
-- and remove it from the re
evalSubRE               :: (RE -> Bool) ->
                           (SubMatches -> RE -> SubMatches) ->
                           (SubMatches, RE) -> TrRex (SubMatches, RE)
evalSubRE p sub e@(sm, r) =
  case splitFstRE p r of
    Nothing             -> return e
    Just (r1, r2)       -> do r' <- liftTrRex $ toNF r2
                              changed (sub sm r1, r')


-- split the leftmost sub regex (BsubRE, EsubRE, ...) from a regex
-- type of re is determined by predicate p
--
-- applied on normalized REs,
-- only Seq and Diff nodes are descended
-- used to get the leftmost primitive RE or pseude RE for submatches
--
-- must be extended when further logical ops, e.g. intersection, are added

splitFstRE          :: (RE -> Bool) -> RE -> Maybe (RE, RE)
splitFstRE p        = go
  where
    go r
      | p r         = Just (r, Unit)

    go (Seq r1 r2)
      | p r1        = Just (r1, r2)

    go (Seq  r1 r2) = second (<> r2) <$> go r1

    go (Diff r1 r2) = (second (`diff'` r2) <$> go r1)
                  --  <|>
                  --  (second (r1 `diff'`) <$> go r2)

    go _            = Nothing

-- ------------------------------------------------------------
--
-- expression transformation combinators
--
-- transformations run in the REX monad,
-- the results are augmented with a boolean indicating
-- whether a transformation step has been applied with success
--
-- expressions can even be deleted by use of mzero from Alternative
-- within the tr-functions
--
-- currently (only) used in evaluating submatch RE's
--
-- this is a writer monad with a boolean

newtype TrRex a = TR (REX (a, Any))

instance Functor TrRex where
  fmap f (TR t) = TR $ first f <$> t

instance Applicative TrRex where
  pure = return
  (<*>) = ap

instance Monad TrRex where
  return x      = TR $ return (x, mempty)
  (TR t1) >>= f = TR $ do (x1, c1)   <- t1
                          let (TR t2) = f x1
                          (x2, c2)   <- t2
                          return (x2, c1 <> c2)

instance MonadWriter Any TrRex where
  writer (x, c) = TR $ return (x, c)
  tell c        = TR $ return ((), c)
  listen (TR t) = TR $ do r@(_x, c) <- t
                          return (r, c)
  pass   (TR t) = TR $ do ((x, f), c) <- t
                          return (x, f c)

changed         :: a -> TrRex a
changed x       = writer (x, Any True)

hasChanged'     :: Any -> Bool
hasChanged'     = getAny

runTrRex        :: TrRex a -> REX (a, Bool)
runTrRex (TR t) = second getAny <$> t

execTrRex       :: TrRex a -> REX a
execTrRex t     = fst <$> runTrRex t

liftTrRex       :: REX a -> TrRex a
liftTrRex m     = TR $ (,mempty) <$> m

-- --------------------
--
-- try a 1. transformation, only when applied
-- with success, apply 2. transformation

onChanged :: (a -> TrRex a) -> (a -> TrRex a) -> a -> TrRex a
onChanged f g x = do
  (y, c) <- listen $ f x
  if hasChanged' c
    then g y
    else return y

-- try 1. transformation, only if no success
-- try 2. transformation on input x

onFailure :: (a -> TrRex a) -> (a -> TrRex a) -> a -> TrRex a
onFailure f g x = do
  (y, c) <- listen $ f x
  if hasChanged' c
    then return y
    else g x

-- apply a transformation until nothing changes anymore
fixTr :: (a -> TrRex a) -> a -> TrRex a
fixTr f = f `onChanged` fixTr f

-- ----------------------------------------

type Tr a = a -> REX (Changed, a)

type Changed = Bool

hasChanged :: Bool
hasChanged = True

noChange :: Bool
noChange = False

-- throw away transformation success flag
runTr :: Tr a -> a -> REX a
runTr f x = snd <$> f x

-- the identity transformation
idTr :: Tr a
idTr = \ x -> return (noChange, x)

-- try 2 transformations in a sequence
-- 2. transformation is always tried independently
-- of success in the 1. transformation
--
-- (>=>)

andThen :: Tr a -> Tr a -> Tr a
andThen f g x = do
  (changed1, y) <- f x
  (changed2, z) <- g y
  return (changed1 || changed2, z)

-- try a 1. transformation, only when applied
-- with success, apply 2. transformation

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

-- try 1. transformation, only if no success
-- try 2. transformation on input x

orElse :: Tr a -> Tr a -> Tr a
orElse f g x = do
  res1@(changed1, _y) <- f x
  if changed1
    then
      return res1
    else
      g x

-- apply a transformation until nothing changes anymore
repeatTr :: Tr a -> Tr a
repeatTr f = f `onSuccess` repeatTr f

-- ------------------------------------------------------------
