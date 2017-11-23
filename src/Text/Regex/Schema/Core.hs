module Text.Regex.Schema.Core
where

import Data.Set.CharSet
import Data.Monoid (Monoid(..), (<>))

data RE a = Zero ErrMsg         -- {}
          | Unit                -- {&epsilon;}
          | Dot                 -- whole Alphabet
          | Syms  CharSet       -- {a,b,c,...}
          | Star  (RE a)        -- r*
          | Plus  (RE a)        -- r+
          | Seq   (RE a) (RE a) -- r1 . r2
          | Or    (RE a) (RE a) -- r1 | r2
          | Isect (RE a) (RE a) -- r1 & r2
          | Diff  (RE a) (RE a) -- r1 - r2
            deriving (Eq, Ord, Read, Show)

type RegEx = RE Char

type ErrMsg = String

-- ------------------------------------------------------------
--
-- smart constructors

zero :: ErrMsg -> RE a
zero = Zero

noMatch :: RE a
noMatch = zero "no match"

unit :: RE a
unit = Unit

dot :: RE a
dot = Dot

syms :: CharSet -> RE a
syms = Syms

sym :: Char -> RE a
sym = syms . singleCS

symRng :: Char -> Char -> RE a
symRng lb ub = syms $ rangeCS lb ub

-- --------------------
--
-- smart constructor for sequence

seq'                     :: RE a -> RE a -> RE a
seq' r1@(Zero _)  _      = r1                    -- {}.r  == {}
seq' _ r2@(Zero _)       = r2                    -- r.{}  == {}
seq' Unit r2             = r2                    -- ().r  == r
seq' r1   Unit           = r1                    -- r.()  == r
seq' (Seq r1 r2) r3      = seq' r1 (seq' r2 r3)    -- assoc. of .
seq' r1   r2             = Seq r1 r2

seqs                    :: [RE a] -> RE a
seqs                    = foldr seq' unit

instance Monoid (RE a) where
  mempty  = unit
  mappend = seq'

word :: String -> RE a
word = foldr (\ a b -> seq' (sym a) b) unit

-- --------------------
--
-- smart constructor for * and +

star                    :: RE a -> RE a
star (Zero _)           = unit                  -- {}* == ()
star r@Unit             = r                     -- ()* == ()
star r@(Star _r1)       = r                     -- (r*)* == r*
star r@(Plus r1)        = Star r1               -- (r+)* == r*
star r                  = Star r

plus                    :: RE a -> RE a
plus r@(Zero _)         = r                     -- {}+ == {}
plus r@Unit             = r                     -- ()+ == ()
plus r@(Star r1)        = r                     -- (r*)+ == r*
plus r@(Plus _r1)       = r                     -- (r+)+ == r+
plus r                  = r <> star r           -- r+    == r.r*

-- --------------------
--
-- smart constructor for alternative

infixr .|.

(.|.)                   :: RE a -> RE a -> RE a

Zero _    .|. r2         = r2               -- zero
r1        .|. Zero _     = r1               -- zero
Or r1 r2 .|. r3          = r1 .|. r2 .|. r3 -- associativity
r1        .|.  r2        = Or r1 r2

-- ------------------------------------------------------------

nullable              :: RE a -> Bool

nullable (Zero _)       = False
nullable Unit           = True
nullable Dot            = False
nullable (Syms _x)      = False
nullable (Star _r)      = True
nullable (Plus r)       = nullable r
nullable (Seq r1 r2)    = nullable r1
                          &&
                          nullable r2
nullable (Or r1 r2)    = nullable r1
                          ||
                          nullable r2
nullable (Isect r1 r2)  = nullable r1
                          &&
                          nullable r2
nullable (Diff r1 r2)   = nullable r1
                          &&
                          not (nullable r2)

-- ------------------------------------------------------------

delta :: RE a -> Char -> RE a

delta r@(Zero _) _c = r

delta Unit _c       = noMatch

delta Dot  _c       = Unit

delta (Syms cs) c
  | c `elemCS` cs   = Unit
  | otherwise       = noMatch

delta (Star r) a
    = Seq
      (delta r a)
      (Star r)

delta (Plus r) a
    = delta (Seq r (Star r)) a

delta (Seq r1 r2) a
  | nullable r1 = dr1 .|. dr2
  | otherwise   = dr1
    where
    dr1 = Seq (delta r1 a) r2
    dr2 = delta r2 a

delta (Or r1 r2) a
    = delta r1 a
      .|.
      delta r2 a

delta (Isect r1 r2) a
    = Isect
      (delta r1 a)
      (delta r2 a)

delta (Diff r1 r2) a
    = Diff
      (delta r1 a)
      (delta r2 a)

-- ------------------------------------------------------------

delta' :: RE a -> String-> RE a

delta' re []    = re
delta' re (c : ws) = delta' (delta re c) ws


match :: RE a -> String -> Bool

match re ws = nullable (delta' re ws)

-- ------------------------------------------------------------

-- simplification rules
--
-- implemented with "smart" constructors
-- not all allgebraic laws concerning sets are realized

-- --------------------

alt                   :: RE a -> RE a -> RE a
alt (Zero _) r2       = r2
alt r1 (Zero _)       = r1

alt r1@(Star Dot) r2  = r1
alt r1 r2@(Star Dot)  = r2

alt (Or r1 r2) r3  = alt r1 (alt r2 r3)
                                        -- associativity
alt r1 (Or r21 r22)
    | r1 == r21         = alt r1 r22  -- idempotent
    | r1 > r21          = alt r21 (alt r1 r22)
                                        -- symmetry
alt r1   r2
    | r1 == r2          = r1            -- idempotent
    | r1 > r2           = alt r2 r1   -- symmetry
    | otherwise         = Or r1 r2

-- --------------------

isect                   :: RE a -> RE a -> RE a
isect z@(Zero _) _      = z
isect _ z@(Zero _)      = z

isect (Star Dot) r2     = r2
isect r1 (Star Dot)     = r1

isect (Isect r1 r2) r3  = isect r1 (isect r2 r3)
                                        -- associativity

isect r1 (Isect r21 r22)
    | r1 == r21         = isect r1 r22  -- idempotent
    | r1 > r21          = isect r21 (isect r1 r22)
                                        -- symmetry

isect r1   r2
    | r1 == r2          = r1            -- idempotent
    | r1 > r2           = isect r2 r1   -- symmetry
    | otherwise         = Isect r1 r2

-- --------------------

diff                    :: RE a -> RE a -> RE a
diff r1@(Zero _) r2     = r1
diff r1 (Zero _)        = r1
diff r1 (Star Dot)      = noMatch
diff r1   r2
    | r1 == r2          = noMatch
    | otherwise         = Diff r1 r2

-- ------------------------------------------------------------

delta1 :: RE a -> Char -> RE a

delta1 z@(Zero _) _a  = z

delta1 Unit _c        = noMatch

delta1 Dot  _c        = unit

delta1 (Syms cs) c
  | c `elemCS` cs     = unit
  | otherwise         = noMatch

delta1 (Star r) a
    = delta1 r a
      <>
      star r

delta1 (Plus r) a
    = delta1 (r <> star r) a

delta1 (Seq r1 r2) a
  | nullable r1 = dr1 .|. dr2
  | otherwise   = dr1
    where
    dr1 = delta1 r1 a <> r2
    dr2 = delta1 r2 a

delta1 (Or r1 r2) a
    = delta1 r1 a
      .|.
      delta1 r2 a

delta1 (Isect r1 r2) a
    = isect
      (delta1 r1 a)
      (delta1 r2 a)

delta1 (Diff r1 r2) a
    = diff
      (delta1 r1 a)
      (delta1 r2 a)

-- ------------------------------------------------------------

delta1' :: RE a -> String-> RE a

delta1' re []    = re
delta1' re (c : ws) = delta1' (delta1 re c) ws


match1 :: RE a -> String -> Bool

match1 re ws = nullable (delta1' re ws)

-- ------------------------------------------------------------
--
-- not computable with the similar simple
-- algorithmn as nullable: Isect and Diff are the hard ops

nullable'              :: RE a -> Bool

nullable' (Zero _)  = True
nullable' Unit      = False
nullable' Dot       = False
nullable' (Syms _)  = False
nullable' (Star _r) = False
nullable' (Plus r)  = nullable' r
nullable' (Seq r1 r2)
                = nullable' r1
                  ||
                  nullable' r2
nullable' (Or r1 r2)
                = nullable' r1
                  &&
                  nullable' r2
nullable' (Isect r1 r2)
                = nullable' r1
                  &&
                  nullable' r2

nullable' (Diff r1 (Star Dot))
                = True
nullable' (Diff r1 r2)
  | nullable' r2    = False
  | otherwise   = nullable' r1

-- ------------------------------------------------------------
--
-- readable output

showR :: RegEx -> String
showR = showRegex 6

prio    :: RE a -> Int
prio (Zero _)   = 0
prio Unit       = 0
prio Dot        = 0
prio (Syms _)   = 0
prio (Star _)   = 1
prio (Plus _)   = 1
prio (Seq _ _)  = 2
prio (Isect _ _)= 3
prio (Diff _ _) = 4
prio (Or _ _)  = 5

showRegex       :: Int -> RegEx -> String
showRegex p r
    = par $ (showRegex' r)
    where
    pr  = prio r

    par s
        | pr > p         = "(" ++ s ++ ")"
        | otherwise      = s

    showRegex' (Zero _)      = "{}"
    showRegex' Unit          = "()"
    showRegex' Dot           = "."
    showRegex' (Syms cs)     = showCS cs
    showRegex' (Star r1)     = showRegex pr r1
                               ++ "*"
    showRegex' (Plus r1)     = showRegex pr r1
                               ++ "+"
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
