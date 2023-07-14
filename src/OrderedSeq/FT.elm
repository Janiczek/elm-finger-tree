module OrderedSeq.FT exposing (OrderedSeq)

import FingerTree exposing (FingerTree, Ops)


ops : Ops a Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


type alias OrderedSeq a =
    FingerTree a Int
