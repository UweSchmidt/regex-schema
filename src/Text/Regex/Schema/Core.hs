module Text.Regex.Schema.Core
where

import Data.Set.CharSet
import Data.Monoid (Monoid(..), (<>))

import Text.Regex.Schema.StringLike

-- ------------------------------------------------------------

data RE a
  = Zero ErrMsg         -- {}
  | Unit                -- {&epsilon;}
  | Dot                 -- whole Alphabet
  | Syms  CharSet       -- {a,b,c,...}
  | Star  (RE a) Bool   -- r* / r*?   -- True: shortest match
  | Plus  (RE a) Bool   -- r+ / r+?
  | Seq   (RE a) (RE a) -- r1 . r2
  | Or    (RE a) (RE a) -- r1 | r2
  | Isect (RE a) (RE a) -- r1 & r2
  | Diff  (RE a) (RE a) -- r1 - r2
  | SubRE Label  (RE a) -- submatch
  deriving (Eq, Ord, Read, Show)

type RegEx = RE Char

type ErrMsg = String
type Label  = String

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

subRE :: Label -> RE a -> RE a
subRE = SubRE

-- --------------------
--
-- smart constructor for sequence

sequ                     :: RE a -> RE a -> RE a
sequ r1@(Zero _)  _      = r1                    -- {}.r  == {}
sequ _ r2@(Zero _)       = r2                    -- r.{}  == {}
sequ Unit r2             = r2                    -- ().r  == r
sequ r1   Unit           = r1                    -- r.()  == r
sequ (Seq r1 r2) r3      = sequ r1 (sequ r2 r3)  -- assoc. of .
sequ r1   r2             = Seq r1 r2

instance Monoid (RE a) where
  mempty  = unit
  mappend = sequ
  mconcat = foldr sequ unit

-- <> is sequ(ence)

word :: String -> RE a
word = foldr (\ a b -> sym a <> b) unit

-- --------------------
--
-- smart constructor for * and +

star                     :: RE a -> RE a
star r                   = star' r False

plus                     :: RE a -> RE a
plus r                   = plus' r False

-- shortest match
starSM                   :: RE a -> RE a
starSM r                 = star' r False

plusSM                   :: RE a -> RE a
plusSM r                 = plus' r False

star'                    :: RE a -> Bool -> RE a
star' (Zero _)       _  = unit                  -- {}* == ()
star' r@Unit         _  = r                     -- ()* == ()

{- not neccesary during delta eval
star' r@(Star _ s1)  s
  | s1 == s             = r                     -- (r*)* == r*
star' r@(Plus r1 s1) s
  | s1 == s             = Star r1 s1            -- (r+)* == r*
-}

star' r              s  = Star r  s


plus'                   :: RE a -> Bool -> RE a
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

(.|.)                   :: RE a -> RE a -> RE a
Zero _    .|. r2        = r2                 -- zero
r1        .|. Zero _    = r1                 -- zero
Or r1 r2  .|. r3        = r1 .|. (r2 .|. r3) -- associativity
r1        .|.  r2       = Or r1 r2

-- --------------------
--
-- smart constructor for intersection

infixr 3 .&.

(.&.)                   :: RE a -> RE a -> RE a
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

alt                   :: RE a -> RE a -> RE a
alt (Zero _) r2       = r2
alt r1 (Zero _)       = r1

alt r1@(Star Dot _) r2  = r1
alt r1 r2@(Star Dot _)  = r2

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

isect (Star Dot _) r2   = r2
isect r1 (Star Dot _)   = r1

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

{- not neccesary during delta eval
diff r1 (Star Dot _)    = noMatch
-}

diff r1   r2
    | r1 == r2          = noMatch
    | otherwise         = Diff r1 r2

-- ------------------------------------------------------------
--
-- cases sorted by frequency of operators

nullable                :: RE a -> Bool

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

nullable (SubRE  l  r1) = nullable r1

-- ------------------------------------------------------------

delta :: RE a -> Char -> RE a

delta z@(Zero _) _a   = z

delta Unit _c         = noMatch

delta Dot  _c         = unit

delta (Syms cs) c
  | c `elemCS` cs     = unit
  | otherwise         = noMatch

delta r0@(Star r s) c
  | s                 = delta r c <> (unit      .|. plus' r s)
  | otherwise         = delta r c <> (plus' r s .|. unit  )

delta r0@(Plus r s) c
  | s                 = delta (r <> (unit .|. r0  )) c
  | otherwise         = delta (r <> (r0   .|. unit)) c

delta (Seq r1 r2) c
  | nullable r1       = dr1 .|. dr2
  | otherwise         = dr1
  where
                  dr1 = delta r1 c <> r2
                  dr2 = delta r2 c

delta (Or r1 r2) c    = delta r1 c
                        .|.
                        delta r2 c

delta (Isect r1 r2) c = delta r1 c
                        ` isect`
                        delta r2 c

delta (Diff r1 r2) c  = delta r1 c
                        `diff`
                        delta r2 c

delta (SubRE l r1) c  = delta r1 c  -- TODO

-- ------------------------------------------------------------

delta' :: RE a -> String-> RE a

delta' re []       = re
delta' re (c : ws) = delta' (delta re c) ws


match1 :: RE a -> String -> Bool

match1 re ws = nullable (delta' re ws)

-- ------------------------------------------------------------
--
-- readable output

showR :: RegEx -> String
showR = showRegex 6

prio    :: RE a -> Int
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

showRegex       :: Int -> RegEx -> String
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
    showRegex' (SubRE lab r1) = lab ++ ":" ++
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
