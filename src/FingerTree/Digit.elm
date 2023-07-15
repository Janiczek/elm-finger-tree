module FingerTree.Digit exposing
    ( Digit(..)
    , annotation
    , fromNode
    , fromNodes
    , split
    , toList
    , toNodes
    )

import FingerTree.Node as Node exposing (Node(..))
import FingerTree.Ops as Ops exposing (Ops)


type Digit e ann
    = D1 (Node e ann)
    | D2 (Node e ann) (Node e ann)
    | D3 (Node e ann) (Node e ann) (Node e ann)
    | D4 (Node e ann) (Node e ann) (Node e ann) (Node e ann)


annotation : Ops e ann -> Digit e ann -> ann
annotation { add } digit =
    -- Named `gmd` in the Isabelle implementation.
    case digit of
        D1 n1 ->
            Node.annotation n1

        D2 n1 n2 ->
            add
                (Node.annotation n1)
                (Node.annotation n2)

        D3 n1 n2 n3 ->
            add
                (Node.annotation n1)
                (add
                    (Node.annotation n2)
                    (Node.annotation n3)
                )

        D4 n1 n2 n3 n4 ->
            add
                (Node.annotation n1)
                (add
                    (Node.annotation n2)
                    (add
                        (Node.annotation n3)
                        (Node.annotation n4)
                    )
                )


fromNode : Node e ann -> Digit e ann
fromNode node =
    case node of
        Tip e ann ->
            D1 (Tip e ann)

        Node2 _ n1 n2 ->
            D2 n1 n2

        Node3 _ n1 n2 n3 ->
            D3 n1 n2 n3


toList : Digit e ann -> List e
toList digit =
    case digit of
        D1 n1 ->
            Node.toList n1

        D2 n1 n2 ->
            Node.toList n1 ++ Node.toList n2

        D3 n1 n2 n3 ->
            Node.toList n1 ++ Node.toList n2 ++ Node.toList n3

        D4 n1 n2 n3 n4 ->
            Node.toList n1 ++ Node.toList n2 ++ Node.toList n3 ++ Node.toList n4


toNodes : Digit e ann -> List (Node e ann)
toNodes digit =
    case digit of
        D1 n1 ->
            [ n1 ]

        D2 n1 n2 ->
            [ n1, n2 ]

        D3 n1 n2 n3 ->
            [ n1, n2, n3 ]

        D4 n1 n2 n3 n4 ->
            [ n1, n2, n3, n4 ]


fromNodes : List (Node e ann) -> Maybe (Digit e ann)
fromNodes es =
    case es of
        [ e1 ] ->
            Just (D1 e1)

        [ e1, e2 ] ->
            Just (D2 e1 e2)

        [ e1, e2, e3 ] ->
            Just (D3 e1 e2 e3)

        [ e1, e2, e3, e4 ] ->
            Just (D4 e1 e2 e3 e4)

        _ ->
            Nothing


split :
    Ops e ann
    -> (ann -> Bool)
    -> ann
    -> Digit e ann
    -> ( List (Node e ann), Node e ann, List (Node e ann) )
split ops pred i digit =
    case digit of
        D1 n1 ->
            ( [], n1, [] )

        D2 n1 n2 ->
            let
                ii : ann
                ii =
                    ops.add i (Node.annotation n1)
            in
            if pred ii then
                ( [], n1, [ n2 ] )

            else
                split ops pred ii (D1 n2)
                    |> (\( l, x, r ) -> ( n1 :: l, x, r ))

        D3 n1 n2 n3 ->
            let
                ii : ann
                ii =
                    ops.add i (Node.annotation n1)
            in
            if pred ii then
                ( [], n1, [ n2, n3 ] )

            else
                split ops pred ii (D2 n2 n3)
                    |> (\( l, x, r ) -> ( n1 :: l, x, r ))

        D4 n1 n2 n3 n4 ->
            let
                ii : ann
                ii =
                    ops.add i (Node.annotation n1)
            in
            if pred ii then
                ( [], n1, [ n2, n3, n4 ] )

            else
                split ops pred ii (D3 n2 n3 n4)
                    |> (\( l, x, r ) -> ( n1 :: l, x, r ))
