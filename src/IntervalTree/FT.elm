module IntervalTree.FT exposing (IntervalTree)

import FingerTree exposing (FingerTree, Ops)


ops : Ops a Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


type alias IntervalTree a =
    FingerTree a Int
