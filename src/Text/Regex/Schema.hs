module Text.Regex.Schema
where

import Text.Regex.Schema.Core
import Data.Monoid (Monoid(..), (<>))
import Data.List (inits)

import Prelude hiding (seq)

-- ------------------------------------------------------------

-- | a few simple RegExps

a1, b1, aStar, aOrb, ab, a2 :: RE

a1      = sym 'a'
b1      = sym 'b'
aStar   = star a1
aOrb    = alt a1 b1
ab      = Seq a1 b1
a2      = Seq a1 a1

aOrbStar, aStarOrbStar, allWords, allMinusAStar :: RE

aOrbStar        = star aOrb
aStarOrbStar    = star (alt aStar b1)
allWords        = star Dot
allMinusAStar   = diff allWords aStar

repN            :: Int -> RE -> RE
repN n          = foldr (<>) unit . replicate n

worstCase       :: Int -> RE
worstCase n     = repN n (alt a1 unit) <> repN n a1

ccomment        :: RE
ccomment
    = mconcat [ openCmt
              , all `diff` mconcat [all,closeCmt,all]
              , closeCmt
              ]
    where
    all         = star dot
    openCmt     = word "/*"
    closeCmt    = word "*/"

htmlcomment        :: RE
htmlcomment
    = mconcat [ openCmt
              , all `diff` mconcat [all,closeCmt,all]
              , closeCmt
              ]
    where
    all         = star dot
    openCmt     = word "<!--"
    closeCmt    = word "-->"

xmlcomment        :: RE
xmlcomment
    = mconcat [ openCmt
              , allWords `diff` mconcat [allWords, noCmt, allWords]
              , closeCmt
              ]
    where
    allWords    = star dot
    openCmt     = word "<!--"
    closeCmt    = word "-->"
    noCmt       = word "--"


sub1 :: RE
sub1 = mconcat [ unit -- sym 'a'
               , subRE "1" $ plus $ sym 'i'
               , sym 'z'
               ]


testsT mt
    = ( map (mt a1) ["a"]
        ++
        map (mt aStar) ["", "a", "aa"]
        ++
        map (mt allWords) ["", "a", "b", "ab", "aaa"]
        ++
        map (mt allMinusAStar) ["b", "ab", "aba", "bbbb"]
      )
testsF mt
    = ( map (mt a1) ["", "b", "aa"]
        ++
        map (mt aStar) ["b", "ab", "ba"]
        ++
        map (mt allMinusAStar) ["", "a", "aa", "aaa"]
      )
tests mt
    = testsT mt ++ map not (testsF mt)

deltaTests show' d' r w
    = putStr
      . concat
      . map ((++"\n\n") . show')
      . map (d' r)
      . inits $ w

deltaSimple     = deltaTests show  delta'
deltaSimple'    = deltaTests showR delta'
deltaSmart      = deltaTests showR delta'

dt1  = deltaSimple  aStar             "aaaaa"
dt2  = deltaSimple  aStarOrbStar      "aaaaa"
dt3  = deltaSimple  allMinusAStar     "bbbbb"
dt4  = deltaSimple  (worstCase 5)     "aaaaa"

dt1s = deltaSimple' aStar             "aaaaa"
dt2s = deltaSimple' aStarOrbStar      "aaaaa"
dt3s = deltaSimple' allMinusAStar     "bbbbb"
dt4s = deltaSimple' (worstCase 5)     "aaaaa"

ds1  = deltaSmart   aStar             "aaaaa"
ds2  = deltaSmart   aStarOrbStar      "aaaaa"
ds3  = deltaSmart   allMinusAStar     "bbbbb"
ds4  = deltaSmart   (worstCase 5)     "aaaaa"

dsc1 = deltaSmart ccomment "/*+++++++++++++++++++*/"
dsc2 = deltaSmart ccomment "/*********************/"
dsc3 = deltaSmart ccomment "/**/*/"

dsh1 = deltaSmart htmlcomment "<!--xxx-->"
dsh2 = deltaSmart htmlcomment "<!--xxx--xxx-->"
dsh3 = deltaSmart htmlcomment "<!--xxx-->xxx-->"

dsx1 = deltaSmart xmlcomment "<!--xxx-->"
dsx2 = deltaSmart xmlcomment "<!--xxx--xxx-->"
dsx3 = deltaSmart xmlcomment "<!--xxx-->xxx-->"

-- ------------------------------------------------------------

testNF1 :: RE -> [String]
testNF1 r = map (showRegex 99) $ flip runREX mempty $ toNF r

testNF2 :: RE -> [String]
testNF2 r = map (showRegex 99) $ flip runREX mempty $ toNF r >>= toNF

run = flip runREX mempty
