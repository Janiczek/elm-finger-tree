module FingerTree.Node exposing
    ( Node(..)
    , annotation
    , compact
    , node2
    , node3
    , toList
    , unwrap
    )

import FingerTree.Ops as Ops exposing (Ops)
import Helpers exposing (impossible)


type Node e ann
    = Tip e ann
    | Node2 ann (Node e ann) (Node e ann)
    | Node3 ann (Node e ann) (Node e ann) (Node e ann)


unwrap : Node e ann -> e
unwrap node =
    case node of
        Tip e _ ->
            e

        _ ->
            impossible "Proven not to happen in the Isabelle paper"


compact : Ops e ann -> List (Node e ann) -> List (Node e ann)
compact ops nodes =
    let
        go : List (Node e ann) -> List (Node e ann) -> List (Node e ann)
        go todos acc =
            case todos of
                [] ->
                    acc

                [ a ] ->
                    a :: acc

                [ a, b ] ->
                    node2 ops a b :: acc

                [ a, b, c ] ->
                    node3 ops a b c :: acc

                [ a, b, c, d ] ->
                    node2 ops c d :: node2 ops a b :: acc

                a :: b :: c :: rest ->
                    go rest (node3 ops a b c :: acc)
    in
    go nodes []
        |> List.reverse


{-| A way to construct Node2 while calculating the annotation correctly.
-}
node2 : Ops e ann -> Node e ann -> Node e ann -> Node e ann
node2 { add } n1 n2 =
    let
        ann : ann
        ann =
            add
                (annotation n1)
                (annotation n2)
    in
    Node2 ann n1 n2


{-| A way to construct Node3 while calculating the annotation correctly.
-}
node3 : Ops e ann -> Node e ann -> Node e ann -> Node e ann -> Node e ann
node3 { add } n1 n2 n3 =
    let
        ann : ann
        ann =
            add
                (annotation n1)
                (add
                    (annotation n2)
                    (annotation n3)
                )
    in
    Node3 ann n1 n2 n3


annotation : Node e ann -> ann
annotation node =
    -- Named `gmn` in the Isabelle implementation.
    case node of
        Tip _ ann ->
            ann

        Node2 ann _ _ ->
            ann

        Node3 ann _ _ _ ->
            ann


toList : Node e ann -> List e
toList node =
    case node of
        Tip e _ ->
            [ e ]

        Node2 _ n1 n2 ->
            toList n1 ++ toList n2

        Node3 _ n1 n2 n3 ->
            toList n1 ++ toList n2 ++ toList n3
