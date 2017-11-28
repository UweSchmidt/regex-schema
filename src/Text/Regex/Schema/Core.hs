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
  | SubRE     RE Label  -- submatch
  | OpenSub   RE Label String  -- TODO: generalize -- open subexpr with string and len of submatch
  | ClosedSub RE [(Label, String)]  -- TODO: generalize -- list of completely parsed submatches
  deriving (Read, Show)

-- instance Show RE where  show = showRegex 0

type ErrMsg = String
type Label  = String

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
  mzero         = REX $ \_cx -> []

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
runREX (REX cxf) cx = cxf cx

-- ----------------------------------------

data SubMatches = SM { closedSubs :: [(Label, String)] -- TODO: remove doublicates
                     , openSubs   :: [(Label, String)]
                     }

type RENF = (RE, SubMatches)

toNF :: SubMatches -> RE -> REX RENF
toNF sm re = (\ r -> (r, sm)) <$> nf re
  where
    nf (Zero _)                 = empty
    nf r@Dot                    = return r
    nf r@Unit                   = return r
    nf r@(Syms _cs)             = return r

    nf (Or r1 r2)               = nf r1
                                  <|>
                                  nf r2
    nf (Star r shortest)
      | shortest                = return Unit
                                  <|>
                                  nf (Plus r True)
      | otherwise               = nf (Plus r False)  -- longest match
                                  <|>
                                  return Unit

    nf (Plus r b)               = nf (Seq r (Star r b))

    nf r@(Seq (Syms _) _)       = return r
    nf (Seq (Zero _) _)         = empty
    nf (Seq  Unit    r2)        = nf r2
    nf (Seq (Or  r1 r2) r3)     = nf (Seq r1 r3)
                                  <|>
                                  nf (Seq r2 r3)

    nf (Seq (Star r1 shortest) r2)
      | shortest                = nf r2
                                  <|>
                                  nf (Seq (Plus r1 True) r2)
      | otherwise               = nf (Seq (Plus r1 False) r2) --longest match
                                  <|>
                                  nf r2

    nf (Seq (Plus r1 b) r2)     = nf (Seq r1 (Seq (Star r1 b) r2))
    nf (Seq (Seq r1 r2) r3)     = nf (Seq r1 (Seq r2 r3))

    nf r  = error $ "toNF: no NF found for " ++ showRegex 0 r

{-
toNF Unit                   = return TUnit
toNF Dot                    = return $ TCS allCS Unit
toNF (Syms cs)              = tcs cs Unit

toNF (Seq (Zero _) r2)      = mempty
toNF (Seq Unit r2)          = toNF r2
toNF (Seq (Syms cs) r2)     = return (TCS cs r2)
toNF (Seq (Seq r11 r12) r2) = toNF (Seq r11 (Seq r12 r2))
toNF (Seq (Or  r11 r12) r2) = toNF (Seq r11 r2) <> toNF (Seq r12 r2)
toNF (Seq (SubRE r1 l1) r2) = tSub (toNF r1) l1 "" r2

toNF (Or r1 r2)             = toNF r1 <> toNF r2

toNF (Star r False)         = toNF (Plus r False) <> return TUnit
toNF (Star r True)          = return TUnit <> toNF (Plus r False)
toNF r0@(Plus r b)          = toNF $ Seq r (Star r b)

toNF (SubRE r l)            = tSub (toNF r) l "" Unit

toNF r                      = error $ "No NF for " ++ show r
-}



{-
data Term' m = TUnit
          | TCS CharSet RE        -- charset is not empty
          | TSub (m (Term' m)) Label String RE

nf2nf' :: NF -> NF'
nf2nf' = N3 . map ((\ x -> (x, [])) . t2t')
  where
    t2t' (TSub ts l s r) = TSub (nf2nf' ts) l s r
    t2t' TUnit           = TUnit
    t2t' (TCS cs re)     = TCS cs re

nf'2nf :: NF' -> NF
nf'2nf (N3 ts) = map (t'2t . fst) ts
  where
    t'2t TUnit = TUnit
    t'2t (TCS cs re) = TCS cs re
    t'2t (TSub ts' l s r) = TSub (nf'2nf ts') l s r


tcs :: CharSet -> RE -> NF
tcs cs r
  | nullCS cs = mempty
  | otherwise = return $ TCS cs r

tSub :: NF -> Label -> String -> RE -> NF
tSub [] _ _ _ = []
tSub nf l s r = return $ TSub nf l s r

nullNF :: NF -> Bool
nullNF = any nullT
  where
    nullT (TCS _ _)      = False
    nullT (TUnit)        = True
    nullT (TSub nf _ _ r) = nullNF nf && nullable r

nullNF' :: NF' -> Bool
nullNF' = nullNF . nf'2nf
-}

-- ------------------------------------------------------------
--
-- smart constructors

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
subRE = flip SubRE

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

-- --------------------
--
-- smart constructor for sequence

sequ                     :: RE -> RE -> RE
sequ r1@(Zero _)  _      = r1                       -- {}.r  == {}
sequ _ r2@(Zero _)       = r2                       -- r.{}  == {}
sequ Unit r2             = r2                       -- ().r  == r
sequ r1   Unit           = r1                       -- r.()  == r
sequ (Seq r1 r2) r3      = sequ r1 (sequ r2 r3)     -- assoc. of .
sequ (ClosedSub r1 ms) r2= closedSub (sequ r1 r2) ms -- propagate submatches upwards
sequ r1   r2             = Seq r1 r2

instance Monoid RE where
  mempty  = unit
  mappend = sequ
  mconcat = foldr sequ unit

-- <> is sequ(ence)

word :: String -> RE
word = foldr (\ a b -> sym a <> b) unit

-- --------------------
--
-- smart constructor for * and +

star                     :: RE -> RE
star r                   = star' r False

plus                     :: RE -> RE
plus r                   = plus' r False

-- shortest match
starSM                   :: RE -> RE
starSM r                 = star' r False

plusSM                   :: RE -> RE
plusSM r                 = plus' r False

star'                    :: RE -> Bool -> RE
star' (Zero _)       _  = unit                  -- {}* == ()
star' r@Unit         _  = r                     -- ()* == ()

{- not neccesary during delta eval
star' r@(Star _ s1)  s
  | s1 == s             = r                     -- (r*)* == r*
star' r@(Plus r1 s1) s
  | s1 == s             = Star r1 s1            -- (r+)* == r*
-}

star' r              s  = Star r  s


plus'                   :: RE -> Bool -> RE
plus' r@(Zero _)     _  = r                     -- {}+ == {}
plus' r@Unit         _  = r                     -- ()+ == ()

{- not neccesary during delta eval
plus' r@(Star r1 s1) s
  | s1 == s             = r                     -- (r*)+ == r*
plus' r@(Plus _  s1) s
  | s1 == s             = r                     -- (r+)+ == r+
-}

plus' r              s  = Plus r s

-- --------------------
--
-- smart constructor for alternative

infixr 2 .|.

(.|.)                   :: RE -> RE -> RE
Zero _    .|. r2        = r2                 -- zero
r1        .|. Zero _    = r1                 -- zero
Or r1 r2  .|. r3        = r1 .|. (r2 .|. r3) -- associativity
r1        .|.  r2       = Or r1 r2

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

alt r1@(Star Dot _) r2  = r1
alt r1 r2@(Star Dot _)  = r2

alt (Or r1 r2) r3  = alt r1 (alt r2 r3)
                                        -- associativity
alt r1 (Or r21 r22)
    | r1 === r21         = alt r1 r22  -- idempotent
--    | r1 > r21          = alt r21 (alt r1 r22)
                                        -- symmetry
alt r1   r2
    | r1 === r2          = r1            -- idempotent
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
    | r1 === r21         = isect r1 r22  -- idempotent
--    | r1 > r21          = isect r21 (isect r1 r22)
                                        -- symmetry

isect r1   r2
    | r1 === r2          = r1            -- idempotent
--    | r1 > r2           = isect r2 r1   -- symmetry
    | otherwise         = Isect r1 r2

-- --------------------

diff                    :: RE -> RE -> RE
diff r1@(Zero _) r2     = r1
diff r1 (Zero _)        = r1
diff r1   r2
    | r1 === r2         = noMatch
    | otherwise         = Diff r1 r2

-- ------------------------------------------------------------
--
-- equivalence: used for itempotent op's:  a `op` a == a

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

nullable (SubRE   r _)   = nullable r
nullable (OpenSub r _ _) = nullable r
nullable (ClosedSub r _) = nullable r

-- ------------------------------------------------------------

delta :: RE -> Char -> RE

delta z@(Zero _) _a      = z

delta Unit _c            = noMatch

delta Dot  _c            = unit

delta (Syms cs) c
  | c `elemCS` cs        = unit
  | otherwise            = noMatch

delta r0@(Star r s) c
  | s                    = delta r c <> (unit      .|. plus' r s)
  | otherwise            = delta r c <> (plus' r s .|. unit  )

delta r0@(Plus r s) c
  | s                    = delta (r <> (unit .|. r0  )) c
  | otherwise            = delta (r <> (r0   .|. unit)) c

delta (Seq r1 r2) c
  | nullable r1          = dr1 .|. dr2
  | otherwise            = dr1
                           where
                             dr1 = delta r1 c <> r2
                             dr2 = delta r2 c

delta (Or r1 r2) c       = delta r1 c
                           .|.
                           delta r2 c

delta (Isect r1 r2) c    = delta r1 c
                           ` isect`
                           delta r2 c

delta (Diff r1 r2) c     = delta r1 c
                           `diff`
                           delta r2 c

delta (SubRE r l) c      = delta (openSub r l) c       -- a submatch starts

delta (OpenSub r l s) c
  | nullable r           = closedSub unit [(l, s)]     -- complete match found
                           .|.                         -- or
                           r'                          -- continue parse
  | otherwise            = r'
  where
      r' = contSub (delta r c) l (c : s)

delta (ClosedSub r ms) c = closedSub (delta r c) ms

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
prio (SubRE _ _) = 10
prio (OpenSub _ _ _) = 10
prio (ClosedSub _ _) = 10

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
    showRegex' (SubRE r1 l)  = l ++ ":" ++
                               showRegex pr r1
    showRegex' (OpenSub r1 l s)
                             = l ++ "=" ++ s ++ ":" ++
                               showRegex pr r1
    showRegex' (ClosedSub r1 ms)
                             = show ms ++ ":" ++
                               showRegex pr r1

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
