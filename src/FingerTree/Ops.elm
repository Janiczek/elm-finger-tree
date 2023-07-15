module FingerTree.Ops exposing (Ops)

{-|

@docs Ops

-}


{-| Monoidal operations on the elements of the Finger Tree and their
annotations.
-}
type alias Ops e ann =
    { empty : ann
    , add : ann -> ann -> ann
    , fromElement : e -> ann
    }
