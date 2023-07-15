module Array.FT exposing
    ( Array
    , length
    )

import FingerTree as FT exposing (FingerTree, Ops)
import FingerTree.Node as Node
import Helpers exposing (impossible)


type Array a
    = A (FingerTree a Int)


ops : Ops a Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


{-| Get the length of the array.

O(1)

-}
length : Array a -> Int
length (A array) =
    FT.annotation ops array


splitAt : Int -> Array a -> ( Array a, Array a )
splitAt i (A xs) =
    FT.split ops (\n -> i < n) xs
        |> Tuple.mapBoth A A


getAt : Int -> Array a -> a
getAt i (A xs) =
    case FT.splitTree ops (\n -> i < n) 0 xs of
        -- TODO actually check this.. what if i == 10000000?
        Nothing ->
            impossible "Never happens!"

        Just ( _, x, _ ) ->
            Node.unwrap x
