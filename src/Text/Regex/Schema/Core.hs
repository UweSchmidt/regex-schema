module Text.Regex.Schema.Core
where

import Prelude hiding (seq)

data RE a = Zero ErrMsg         -- {}
          | Unit                -- {&epsilon;}
          | Dot                 -- whole Alphabet
          | Sym   a             -- {a}
          | Star  (RE a)        -- r*
          | Plus  (RE a)        -- r+
          | Seq   (RE a) (RE a) -- r1 . r2
          | Union (RE a) (RE a) -- r1 | r2
          | Isect (RE a) (RE a) -- r1 & r2
          | Diff  (RE a) (RE a) -- r1 - r2
            deriving (Eq, Ord, Read, Show)

type RegEx = RE Char

type ErrMsg = String

-- ------------------------------------------------------------

noMatch :: RE a
noMatch = Zero "no match"

-- ------------------------------------------------------------

nullable              :: RE a -> Bool

nullable (Zero _)       = False
nullable Unit           = True
nullable Dot            = False
nullable (Sym _x)       = False
nullable (Star _r)      = True
nullable (Plus r)       = nullable r
nullable (Seq r1 r2)    = nullable r1
                          &&
                          nullable r2
nullable (Union r1 r2)  = nullable r1
                          ||
                          nullable r2
nullable (Isect r1 r2)  = nullable r1
                          &&
                          nullable r2
nullable (Diff r1 r2)   = nullable r1
                          &&
                          not (nullable r2)

-- ------------------------------------------------------------

delta :: Eq a => RE a -> a -> RE a

delta r@(Zero _) _a = r

delta Unit _a       = noMatch

delta Dot  _a       = Unit

delta (Sym x) a
  | a == x          = Unit
  | otherwise       = noMatch

delta (Star r) a
    = Seq
      (delta r a)
      (Star r)

delta (Plus r) a
    = delta (Seq r (Star r)) a

delta (Seq r1 r2) a
  | nullable r1 = Union dr1 dr2
  | otherwise   = dr1
    where
    dr1 = Seq (delta r1 a) r2
    dr2 = delta r2 a

delta (Union r1 r2) a
    = Union
      (delta r1 a)
      (delta r2 a)

delta (Isect r1 r2) a
    = Isect
      (delta r1 a)
      (delta r2 a)

delta (Diff r1 r2) a
    = Diff
      (delta r1 a)
      (delta r2 a)

-- ------------------------------------------------------------

delta' :: Eq a => RE a -> [a]-> RE a

delta' re []    = re
delta' re (a:w) = delta' (delta re a) w


match :: Eq a => RE a -> [a]-> Bool

match re w = nullable (delta' re w)

-- ------------------------------------------------------------

-- simplification rules
--
-- implemented with "smart" constructors
-- not all allgebraic laws concerning sets are realized

zero                    :: ErrMsg -> RE a
zero                    = Zero

unit                    :: RE a
unit                    = Unit

dot                     :: RE a
dot                     = Dot

sym                     :: a -> RE a
sym a                   = Sym a

word                    :: [a] -> RE a
word                    = foldr (\ a b -> seq (sym a) b) unit

-- --------------------

star                    :: RE a -> RE a
star (Zero _)           = unit                  -- {}* == ()
star r@Unit             = r                     -- ()* == ()
star r@(Star _r1)       = r                     -- (r*)* == r*
star r@(Plus r1)        = Star r1               -- (r+)* == r*
star r                  = Star r

-- --------------------

plus                    :: RE a -> RE a
plus r@(Zero _)         = r                     -- {}+ == {}
plus r@Unit             = r                     -- ()+ == ()
plus r@(Star r1)        = r                     -- (r*)+ == r*
plus r@(Plus _r1)       = r                     -- (r+)+ == r+
plus r                  = seq r (star r)        -- r+    == r.r*

-- --------------------

seq                     :: RE a -> RE a -> RE a
seq r1@(Zero _)  _      = r1                    -- {}.r  == {}
seq _ r2@(Zero _)       = r2                    -- r.{}  == {}
seq Unit r2             = r2                    -- ().r  == r
seq r1   Unit           = r1                    -- r.()  == r
seq (Seq r1 r2) r3      = seq r1 (seq r2 r3)    -- assoc. of .
seq r1   r2             = Seq r1 r2

seqs                    :: [RE a] -> RE a
seqs                    = foldr seq unit

-- --------------------

union                   :: (Eq a, Ord a) => RE a -> RE a -> RE a
union (Zero _) r2       = r2
union r1 (Zero _)       = r1

union r1@(Star Dot) r2  = r1
union r1 r2@(Star Dot)  = r2

union (Union r1 r2) r3  = union r1 (union r2 r3)
                                        -- associativity
union r1 (Union r21 r22)
    | r1 == r21         = union r1 r22  -- idempotent
    | r1 > r21          = union r21 (union r1 r22)
                                        -- symmetry
union r1   r2
    | r1 == r2          = r1            -- idempotent
    | r1 > r2           = union r2 r1   -- symmetry
    | otherwise         = Union r1 r2

-- --------------------

isect                   :: (Eq a, Ord a) => RE a -> RE a -> RE a
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

diff                    :: Eq a => RE a -> RE a -> RE a
diff r1@(Zero _) r2     = r1
diff r1 (Zero _)        = r1
diff r1 (Star Dot)      = noMatch
diff r1   r2
    | r1 == r2          = noMatch
    | otherwise         = Diff r1 r2

-- ------------------------------------------------------------

delta1 :: (Eq a, Ord a) => RE a -> a -> RE a

delta1 z@(Zero _) _a  = z

delta1 Unit _a        = noMatch

delta1 Dot  _a        = unit

delta1 (Sym x) a
  | a == x            = unit
  | otherwise         = noMatch

delta1 (Star r) a
    = seq
      (delta1 r a)
      (star r)

delta1 (Plus r) a
    = delta1 (seq r (star r)) a

delta1 (Seq r1 r2) a
  | nullable r1 = union dr1 dr2
  | otherwise   = dr1
    where
    dr1 = seq (delta1 r1 a) r2
    dr2 = delta1 r2 a

delta1 (Union r1 r2) a
    = union
      (delta1 r1 a)
      (delta1 r2 a)

delta1 (Isect r1 r2) a
    = isect
      (delta1 r1 a)
      (delta1 r2 a)

delta1 (Diff r1 r2) a
    = diff
      (delta1 r1 a)
      (delta1 r2 a)

-- ------------------------------------------------------------

delta1' :: (Eq a, Ord a) => RE a -> [a]-> RE a

delta1' re []    = re
delta1' re (a:w) = delta1' (delta1 re a) w


match1 :: (Eq a, Ord a) => RE a -> [a]-> Bool

match1 re w = nullable (delta1' re w)

-- ------------------------------------------------------------
--
-- not computable with the similar simple
-- algorithmn as nullable: Isect and Diff are the hard ops

empty              :: RE a -> Bool

empty (Zero _)  = True
empty Unit      = False
empty Dot       = False
empty (Sym _x)  = False
empty (Star _r) = False
empty (Plus r)  = empty r
empty (Seq r1 r2)
    = empty r1
      ||
      empty r2
empty (Union r1 r2)
    = empty r1
      &&
      empty r2
empty (Isect r1 r2)     -- !!! incomplete
    = empty r1
      ||
      empty r2

empty (Diff r1 (Star Dot))
    = True
empty (Diff r1 r2)      -- !!! incomplete
    = empty r1

-- ------------------------------------------------------------
--
-- readable output

showR :: RegEx -> String
showR = showRegex 6

prio    :: RE a -> Int
prio (Zero _)   = 0
prio Unit       = 0
prio Dot        = 0
prio (Sym _)    = 0
prio (Star _)   = 1
prio (Plus _)   = 1
prio (Seq _ _)  = 2
prio (Isect _ _)= 3
prio (Diff _ _) = 4
prio (Union _ _)= 5

showRegex       :: Int -> RegEx -> String
showRegex p r
    = par $ (showRegex' r)
    where
    pr  = prio r
    par s
        | pr > p        = "(" ++ s ++ ")"
        | otherwise     = s
    showRegex' (Zero _) = "{}"
    showRegex' Unit     = "()"
    showRegex' Dot      = "."
    showRegex' (Sym a)
        | a `elem` "\\(){}.*+|&-"  = '\\' : [a]
        | otherwise                = [a]
    showRegex' (Star r1)     = showRegex pr r1 ++ "*"
    showRegex' (Plus r1)     = showRegex pr r1 ++ "+"
    showRegex' (Seq r1 r2)   = showRegex pr r1
                               ++ showRegex pr r2
    showRegex' (Union r1 r2) = showRegex pr r1 ++ "|"
                               ++ showRegex pr r2
    showRegex' (Isect r1 r2) = showRegex pr r1 ++ "&"
                               ++ showRegex pr r2
    showRegex' (Diff  r1 r2) = showRegex pr r1 ++ "-"
                               ++ showRegex pr r2

-- ------------------------------------------------------------
