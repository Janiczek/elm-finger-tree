module Array.FT exposing (Array)

import FingerTree exposing (FingerTree, Ops)


ops : Ops a Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


type alias Array a =
    FingerTree a Int
