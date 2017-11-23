module Text.Regex.Schema
where

import Text.Regex.Schema.Core
import Data.Monoid (Monoid(..), (<>))
import Data.List (inits)

import Prelude hiding (seq)

-- ------------------------------------------------------------

-- | a few simple RegExps

a1, b1, aStar, aOrb, ab, a2 :: RegEx

a1      = sym 'a'
b1      = sym 'b'
aStar   = Star a1
aOrb    = alt a1 b1
ab      = Seq a1 b1
a2      = Seq a1 a1

aOrbStar, aStarOrbStar, allWords, allMinusAStar :: RegEx

aOrbStar        = star aOrb
aStarOrbStar    = star (alt aStar b1)
allWords        = star Dot
allMinusAStar   = diff allWords aStar

repN            :: Int -> RegEx -> RegEx
repN n          = foldr (<>) unit . replicate n

worstCase       :: Int -> RegEx
worstCase n     = repN n (alt a1 unit) <> repN n a1

ccomment        :: RegEx
ccomment
    = seqs [ openCmt
           , all `diff` (seqs [all,closeCmt,all])
           , closeCmt
           ]
    where
    all         = star dot
    openCmt     = word "/*"
    closeCmt    = word "*/"

htmlcomment        :: RegEx
htmlcomment
    = seqs [ openCmt
           , all `diff` (seqs [all,closeCmt,all])
           , closeCmt
           ]
    where
    all         = star dot
    openCmt     = word "<!--"
    closeCmt    = word "-->"

xmlcomment        :: RegEx
xmlcomment
    = seqs [ openCmt
           , all `diff` (seqs [all,noCmt,all])
           , closeCmt
           ]
    where
    all         = star dot
    openCmt     = word "<!--"
    closeCmt    = word "-->"
    noCmt       = word "--"



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
deltaSmart      = deltaTests showR delta1'

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
