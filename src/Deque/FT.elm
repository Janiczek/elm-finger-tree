module Deque.FT exposing (Deque)

import FingerTree exposing (FingerTree, Ops)


ops : Ops a Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


type alias Deque a =
    FingerTree a Int
