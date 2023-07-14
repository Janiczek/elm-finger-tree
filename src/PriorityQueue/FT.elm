module PriorityQueue.FT exposing (MaxPriorityQueue)

import FingerTree exposing (FingerTree, Ops)


ops : Ops a Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


type alias MaxPriorityQueue a =
    FingerTree a Int
