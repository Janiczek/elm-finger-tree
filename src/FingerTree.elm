module FingerTree exposing
    ( FingerTree, Ops
    , empty, singleton, fromList, initialize
    , toList
    , foldl, foldr
    , equals
    , isEmpty, count
    , member
    , leftUncons, rightUncons
    , head, tail, headR, tailR
    , split, partition
    , leftCons, rightCons, append
    , takeUntil, dropUntil
    , reverse
    , map, filter, filterMap
    , structuralInvariant
    -- TODO some of these will be only useful in FingerTree.Array etc.
    -- TODO repeat
    -- TODO range
    -- TODO indexedMap
    -- TODO all
    -- TODO any
    -- TODO maximum
    -- TODO minimum
    -- TODO sum
    -- TODO product
    -- TODO concat
    -- TODO concatMap
    -- TODO intersperse
    -- TODO map2
    -- TODO map3
    -- TODO map4
    -- TODO map5
    -- TODO sort
    -- TODO sortBy
    -- TODO sortWith
    -- TODO take
    -- TODO drop
    -- TODO unzip
    )

{-| Finger trees:
<https://en.wikipedia.org/wiki/Finger_tree>

Original paper:
<https://www.cs.ox.ac.uk/ralf.hinze/publications/FingerTrees.pdf>

This implementation is ported from:
<https://www.isa-afp.org/entries/Finger-Trees.html>
<https://www.isa-afp.org/browser_info/current/AFP/Finger-Trees/document.pdf>


## FingerTree

@docs FingerTree, Ops


## Creation

@docs empty, singleton, fromList, initialize


## Conversion

@docs toList
@docs foldl, foldr


## Query

@docs equals
@docs isEmpty, count
@docs member
@docs leftUncons, rightUncons
@docs head, tail, headR, tailR
@docs split, partition


## Update

@docs leftCons, rightCons, append
@docs takeUntil, dropUntil
@docs reverse
@docs map, filter, filterMap


## Testing

@docs structuralInvariant

-}


type Node e a
    = Tip e a
    | Node2 a (Node e a) (Node e a)
    | Node3 a (Node e a) (Node e a) (Node e a)


type Digit e a
    = D1 (Node e a)
    | D2 (Node e a) (Node e a)
    | D3 (Node e a) (Node e a) (Node e a)
    | D4 (Node e a) (Node e a) (Node e a) (Node e a)


{-| A Finger Tree structure.

The `e` (short for "element") is the data you want the tree to hold.

The `a` (short for "annotation") is a measure. For example, for a Deque this
would be an Int; each element would have measure 1, and recursive internal
nodes would each have measure of the sum of the items inside.

-}
type FingerTree e a
    = Empty
    | Single (Node e a)
    | Deep a (Digit e a) (FingerTree e a) (Digit e a)


{-| Monoidal operations on the elements of the Finger Tree and their
annotations.
-}
type alias Ops e a =
    { empty : a
    , add : a -> a -> a
    , fromElement : e -> a
    }


nodeAnnotation : Node e a -> a
nodeAnnotation node =
    -- Named `gmn` in the Isabelle implementation.
    case node of
        Tip _ a ->
            a

        Node2 a _ _ ->
            a

        Node3 a _ _ _ ->
            a


digitAnnotation : Ops e a -> Digit e a -> a
digitAnnotation { add } digit =
    -- Named `gmd` in the Isabelle implementation.
    case digit of
        D1 n1 ->
            nodeAnnotation n1

        D2 n1 n2 ->
            add
                (nodeAnnotation n1)
                (nodeAnnotation n2)

        D3 n1 n2 n3 ->
            add
                (nodeAnnotation n1)
                (add
                    (nodeAnnotation n2)
                    (nodeAnnotation n3)
                )

        D4 n1 n2 n3 n4 ->
            add
                (nodeAnnotation n1)
                (add
                    (nodeAnnotation n2)
                    (add
                        (nodeAnnotation n3)
                        (nodeAnnotation n4)
                    )
                )


{-| Sum of annotations of all elements of a Finger Tree.

O(1)

-}
annotation : Ops e a -> FingerTree e a -> a
annotation ops tree =
    -- Named `gmft` in the Isabelle implementation.
    case tree of
        Empty ->
            ops.empty

        Single n ->
            nodeAnnotation n

        Deep a _ _ _ ->
            a


{-| The Isabelle implementation used this to prove correctness;
we use it to property-test the port.
-}
structuralInvariant : Ops e a -> FingerTree e a -> Bool
structuralInvariant ops tree =
    -- Named `ft-invar` in the Isabelle implementation.
    isLevelNTree 0 tree && isMeasuredTree ops tree


isLevelNNode : Int -> Node e a -> Bool
isLevelNNode n node =
    case ( n, node ) of
        ( 0, Tip _ _ ) ->
            True

        ( _, Node2 _ n1 n2 ) ->
            isLevelNNode (n - 1) n1
                && isLevelNNode (n - 1) n2

        ( _, Node3 _ n1 n2 n3 ) ->
            isLevelNNode (n - 1) n1
                && isLevelNNode (n - 1) n2
                && isLevelNNode (n - 1) n3

        _ ->
            False


isLevelNDigit : Int -> Digit e a -> Bool
isLevelNDigit n digit =
    case digit of
        D1 n1 ->
            isLevelNNode n n1

        D2 n1 n2 ->
            isLevelNNode n n1
                && isLevelNNode n n2

        D3 n1 n2 n3 ->
            isLevelNNode n n1
                && isLevelNNode n n2
                && isLevelNNode n n3

        D4 n1 n2 n3 n4 ->
            isLevelNNode n n1
                && isLevelNNode n n2
                && isLevelNNode n n3
                && isLevelNNode n n4


isLevelNTree : Int -> FingerTree e a -> Bool
isLevelNTree n tree =
    case tree of
        Empty ->
            True

        Single node ->
            isLevelNNode n node

        Deep _ l m r ->
            isLevelNTree (n + 1) m
                && isLevelNDigit n l
                && isLevelNDigit n r


isMeasuredNode : Ops e a -> Node e a -> Bool
isMeasuredNode ({ add } as ops) node =
    case node of
        Tip _ _ ->
            True

        Node2 a n1 n2 ->
            isMeasuredNode ops n1
                && isMeasuredNode ops n2
                && (a
                        == add
                            (nodeAnnotation n1)
                            (nodeAnnotation n2)
                   )

        Node3 a n1 n2 n3 ->
            isMeasuredNode ops n1
                && isMeasuredNode ops n2
                && isMeasuredNode ops n3
                && (a
                        == add
                            (nodeAnnotation n1)
                            (add
                                (nodeAnnotation n2)
                                (nodeAnnotation n3)
                            )
                   )


isMeasuredDigit : Ops e a -> Digit e a -> Bool
isMeasuredDigit ops digit =
    case digit of
        D1 n1 ->
            isMeasuredNode ops n1

        D2 n1 n2 ->
            isMeasuredNode ops n1
                && isMeasuredNode ops n2

        D3 n1 n2 n3 ->
            isMeasuredNode ops n1
                && isMeasuredNode ops n2
                && isMeasuredNode ops n3

        D4 n1 n2 n3 n4 ->
            isMeasuredNode ops n1
                && isMeasuredNode ops n2
                && isMeasuredNode ops n3
                && isMeasuredNode ops n4


isMeasuredTree : Ops e a -> FingerTree e a -> Bool
isMeasuredTree ({ add } as ops) tree =
    case tree of
        Empty ->
            True

        Single n ->
            isMeasuredNode ops n

        Deep a l m r ->
            isMeasuredTree ops m
                && isMeasuredDigit ops l
                && isMeasuredDigit ops r
                && (a
                        == add
                            (digitAnnotation ops l)
                            (add
                                (annotation ops m)
                                (digitAnnotation ops r)
                            )
                   )


nodeToList : Node e a -> List e
nodeToList node =
    case node of
        Tip e _ ->
            [ e ]

        Node2 _ n1 n2 ->
            nodeToList n1 ++ nodeToList n2

        Node3 _ n1 n2 n3 ->
            nodeToList n1 ++ nodeToList n2 ++ nodeToList n3


digitToList : Digit e a -> List e
digitToList digit =
    case digit of
        D1 n1 ->
            nodeToList n1

        D2 n1 n2 ->
            nodeToList n1 ++ nodeToList n2

        D3 n1 n2 n3 ->
            nodeToList n1 ++ nodeToList n2 ++ nodeToList n3

        D4 n1 n2 n3 n4 ->
            nodeToList n1 ++ nodeToList n2 ++ nodeToList n3 ++ nodeToList n4


{-| Convert a FingerTree to a list.

O(n)

-}
toList : FingerTree e a -> List e
toList tree =
    case tree of
        Empty ->
            []

        Single n ->
            nodeToList n

        Deep _ l m r ->
            digitToList l ++ toList m ++ digitToList r


{-| The empty Finger Tree.

O(1)

-}
empty : FingerTree e a
empty =
    Empty


{-| A singleton Finger Tree.

O(1)

-}
singleton : Ops e a -> e -> FingerTree e a
singleton ops e =
    Single (Tip e (ops.fromElement e))


{-| Compare two Finger Trees for equality.

Using `==` for Finger Trees is not reliable, since there are multiple
representations for the same conceptual value.

-}
equals : FingerTree e a -> FingerTree e a -> Bool
equals tree1 tree2 =
    toList tree1 == toList tree2


{-| Append a node at the left end.
-}
leftConsNode : Ops e a -> Node e a -> FingerTree e a -> FingerTree e a
leftConsNode ops newNode tree =
    -- Recursively we append a node, if the digit is full we push down a Node3
    case tree of
        Empty ->
            Single newNode

        Single n1 ->
            deep ops (D1 newNode) Empty (D1 n1)

        Deep _ (D1 n1) m r ->
            deep ops (D2 newNode n1) m r

        Deep _ (D2 n1 n2) m r ->
            deep ops (D3 newNode n1 n2) m r

        Deep _ (D3 n1 n2 n3) m r ->
            deep ops (D4 newNode n1 n2 n3) m r

        Deep _ (D4 n1 n2 n3 n4) m r ->
            deep ops (D2 newNode n1) (leftConsNode ops (node3 ops n2 n3 n4) m) r


{-| Append a node at the left end.
-}
rightConsNode : Ops e a -> Node e a -> FingerTree e a -> FingerTree e a
rightConsNode ops newNode tree =
    -- Recursively we append a node, if the digit is full we push down a Node3
    case tree of
        Empty ->
            Single newNode

        Single n1 ->
            deep ops (D1 n1) Empty (D1 newNode)

        Deep _ l m (D1 n1) ->
            deep ops l m (D2 n1 newNode)

        Deep _ l m (D2 n1 n2) ->
            deep ops l m (D3 n1 n2 newNode)

        Deep _ l m (D3 n1 n2 n3) ->
            deep ops l m (D4 n1 n2 n3 newNode)

        Deep _ l m (D4 n1 n2 n3 n4) ->
            deep ops l (rightConsNode ops (node3 ops n1 n2 n3) m) (D2 n4 newNode)


{-| A way to construct Deep while calculating the annotation correctly.
-}
deep : Ops e a -> Digit e a -> FingerTree e a -> Digit e a -> FingerTree e a
deep ({ add } as ops) l m r =
    let
        ann : a
        ann =
            add
                (digitAnnotation ops l)
                (add
                    (annotation ops m)
                    (digitAnnotation ops r)
                )
    in
    Deep ann l m r


{-| A way to construct Node2 while calculating the annotation correctly.
-}
node2 : Ops e a -> Node e a -> Node e a -> Node e a
node2 { add } n1 n2 =
    let
        ann : a
        ann =
            add
                (nodeAnnotation n1)
                (nodeAnnotation n2)
    in
    Node2 ann n1 n2


{-| A way to construct Node3 while calculating the annotation correctly.
-}
node3 : Ops e a -> Node e a -> Node e a -> Node e a -> Node e a
node3 { add } n1 n2 n3 =
    let
        ann : a
        ann =
            add
                (nodeAnnotation n1)
                (add
                    (nodeAnnotation n2)
                    (nodeAnnotation n3)
                )
    in
    Node3 ann n1 n2 n3


{-| Append element at the left end.

O(log(n)), O(1) amortized

-}
leftCons : Ops e a -> e -> FingerTree e a -> FingerTree e a
leftCons ops e tree =
    leftConsNode ops (Tip e (ops.fromElement e)) tree


{-| Append element at the right end.

O(log(n)), O(1) amortized

-}
rightCons : Ops e a -> e -> FingerTree e a -> FingerTree e a
rightCons ops e tree =
    rightConsNode ops (Tip e (ops.fromElement e)) tree


{-| Convert list to a Finger Tree.

O(n log(n)), O(n) amortized

-}
fromList : Ops e a -> List e -> FingerTree e a
fromList ops list =
    List.foldr
        (\e acc -> leftCons ops e acc)
        Empty
        list


digitToTree : Ops e a -> Digit e a -> FingerTree e a
digitToTree ops digit =
    case digit of
        D1 n1 ->
            Single n1

        D2 n1 n2 ->
            deep ops (D1 n1) Empty (D1 n2)

        D3 n1 n2 n3 ->
            deep ops (D2 n1 n2) Empty (D1 n3)

        D4 n1 n2 n3 n4 ->
            deep ops (D2 n1 n2) Empty (D2 n3 n4)


nodeToDigit : Node e a -> Digit e a
nodeToDigit node =
    case node of
        Tip e a ->
            D1 (Tip e a)

        Node2 _ n1 n2 ->
            D2 n1 n2

        Node3 _ n1 n2 n3 ->
            D3 n1 n2 n3


digitToNodes : Digit e a -> List (Node e a)
digitToNodes digit =
    case digit of
        D1 n1 ->
            [ n1 ]

        D2 n1 n2 ->
            [ n1, n2 ]

        D3 n1 n2 n3 ->
            [ n1, n2, n3 ]

        D4 n1 n2 n3 n4 ->
            [ n1, n2, n3, n4 ]


{-| Detach the leftmost node.

Called `viewLn` in the Isabelle implementation.

-}
leftmostNode : Ops e a -> FingerTree e a -> Maybe ( Node e a, FingerTree e a )
leftmostNode ops tree =
    case tree of
        Empty ->
            Nothing

        Single n1 ->
            Just ( n1, Empty )

        Deep _ (D2 n1 n2) m r ->
            Just ( n1, deep ops (D1 n2) m r )

        Deep _ (D3 n1 n2 n3) m r ->
            Just ( n1, deep ops (D2 n2 n3) m r )

        Deep _ (D4 n1 n2 n3 n4) m r ->
            Just ( n1, deep ops (D3 n2 n3 n4) m r )

        Deep _ (D1 n1) m r ->
            case leftmostNode ops m of
                Nothing ->
                    Just ( n1, digitToTree ops r )

                Just ( n2, m2 ) ->
                    Just ( n1, deep ops (nodeToDigit n2) m2 r )


{-| Detach the right node.

Called `viewRn` in the Isabelle implementation.

-}
rightmostNode : Ops e a -> FingerTree e a -> Maybe ( Node e a, FingerTree e a )
rightmostNode ops tree =
    case tree of
        Empty ->
            Nothing

        Single n1 ->
            Just ( n1, Empty )

        Deep _ l m (D2 n1 n2) ->
            Just ( n2, deep ops l m (D1 n1) )

        Deep _ l m (D3 n1 n2 n3) ->
            Just ( n3, deep ops l m (D2 n1 n2) )

        Deep _ l m (D4 n1 n2 n3 n4) ->
            Just ( n4, deep ops l m (D3 n1 n2 n3) )

        Deep _ l m (D1 n1) ->
            case rightmostNode ops m of
                Nothing ->
                    Just ( n1, digitToTree ops l )

                Just ( n2, m2 ) ->
                    Just ( n1, deep ops l m2 (nodeToDigit n2) )


{-| Detach the leftmost element.

O(log(n)), O(1) amortized

-}
leftUncons : Ops e a -> FingerTree e a -> Maybe ( ( e, a ), FingerTree e a )
leftUncons ops tree =
    case leftmostNode ops tree of
        Nothing ->
            Nothing

        Just ( Tip e a, t ) ->
            Just ( ( e, a ), t )

        Just _ ->
            -- This is not obvious to me: do we never encounter Node2 and Node3?
            -- I guess this is where we lean on the Isabelle proofs :shrug:
            Nothing


{-| Detach the rightmost element.

O(log(n)), O(1) amortized

-}
rightUncons : Ops e a -> FingerTree e a -> Maybe ( ( e, a ), FingerTree e a )
rightUncons ops tree =
    case rightmostNode ops tree of
        Nothing ->
            Nothing

        Just ( Tip e a, t ) ->
            Just ( ( e, a ), t )

        Just _ ->
            -- This is not obvious to me: do we never encounter Node2 and Node3?
            -- I guess this is where we lean on the Isabelle proofs :shrug:
            Nothing


{-| Check whether the tree is empty.

O(1)

-}
isEmpty : FingerTree e a -> Bool
isEmpty tree =
    tree == Empty


{-| Get the leftmost element.

O(log(n))

-}
head : Ops e a -> FingerTree e a -> Maybe ( e, a )
head ops tree =
    leftUncons ops tree
        |> Maybe.map Tuple.first


{-| Get all but the leftmost element.

O(log(n))

-}
tail : Ops e a -> FingerTree e a -> Maybe (FingerTree e a)
tail ops tree =
    leftUncons ops tree
        |> Maybe.map Tuple.second


{-| Get the rightmost element.

O(log(n))

-}
headR : Ops e a -> FingerTree e a -> Maybe ( e, a )
headR ops tree =
    rightUncons ops tree
        |> Maybe.map Tuple.first


{-| Get all but the rightmost element.

O(log(n))

-}
tailR : Ops e a -> FingerTree e a -> Maybe (FingerTree e a)
tailR ops tree =
    rightUncons ops tree
        |> Maybe.map Tuple.second


leftConsNodes : Ops e a -> List (Node e a) -> FingerTree e a -> FingerTree e a
leftConsNodes ops nodes tree =
    List.foldr (leftConsNode ops) tree nodes


rightConsNodes : Ops e a -> List (Node e a) -> FingerTree e a -> FingerTree e a
rightConsNodes ops nodes tree =
    List.foldl (rightConsNode ops) tree nodes


compactNodes : Ops e a -> List (Node e a) -> List (Node e a)
compactNodes ops nodes =
    let
        go : List (Node e a) -> List (Node e a) -> List (Node e a)
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


append3 : Ops e a -> FingerTree e a -> List (Node e a) -> FingerTree e a -> FingerTree e a
append3 ops l xs r =
    case ( l, r ) of
        ( Empty, _ ) ->
            leftConsNodes ops xs r

        ( _, Empty ) ->
            rightConsNodes ops xs l

        ( Single x, _ ) ->
            leftConsNode ops x (leftConsNodes ops xs r)

        ( _, Single x ) ->
            rightConsNode ops x (rightConsNodes ops xs l)

        ( Deep _ l1 m1 r1, Deep _ l2 m2 r2 ) ->
            deep ops
                l1
                (append3 ops
                    m1
                    (compactNodes ops
                        (digitToNodes r1
                            ++ xs
                            ++ digitToNodes l2
                        )
                    )
                    m2
                )
                r2


{-| Concatenate two Finger Trees.

O(log(m+n))

-}
append : Ops e a -> FingerTree e a -> FingerTree e a -> FingerTree e a
append ops t1 t2 =
    append3 ops t1 [] t2


deepL : Ops e a -> Maybe (Digit e a) -> FingerTree e a -> Digit e a -> FingerTree e a
deepL ops l m r =
    case l of
        Nothing ->
            case leftmostNode ops m of
                Nothing ->
                    digitToTree ops r

                Just ( a, m2 ) ->
                    deep ops (nodeToDigit a) m2 r

        Just ll ->
            deep ops ll m r


deepR : Ops e a -> Digit e a -> FingerTree e a -> Maybe (Digit e a) -> FingerTree e a
deepR ops l m r =
    case r of
        Nothing ->
            case rightmostNode ops m of
                Nothing ->
                    digitToTree ops l

                Just ( a, m2 ) ->
                    deep ops l m2 (nodeToDigit a)

        Just rr ->
            deep ops l m rr


{-| Split a Finger Tree at a point where the predicate on the accumulated
annotation of the prefix changes from 'False' to 'True'.

O(log(min(i,n-i)))

For predictable results, ensure there is only one such point, ie. that
the predicate is monotonic.

-}
split :
    Ops e a
    -> (a -> Bool)
    -> FingerTree e a
    -> ( FingerTree e a, FingerTree e a )
split ops pred tree =
    if isEmpty tree then
        ( Empty, Empty )

    else if pred (annotation ops tree) then
        case splitTree ops pred ops.empty tree of
            Nothing ->
                ( Empty, Empty )

            Just ( l, ( e, _ ), r ) ->
                ( l, leftCons ops e r )

    else
        ( tree, Empty )


{-| Given a monotonic predicate, returns the largest prefix that doesn't satisfy
the predicate.

O(log(min(i,n-i)))

-}
takeUntil : Ops e a -> (a -> Bool) -> FingerTree e a -> FingerTree e a
takeUntil ops pred tree =
    split ops pred tree
        |> Tuple.first


{-| Given a monotonic predicate, returns the rest after removing the largest
prefix that doesn't satisfy the predicate.

O(log(min(i,n-i)))

-}
dropUntil : Ops e a -> (a -> Bool) -> FingerTree e a -> FingerTree e a
dropUntil ops pred tree =
    split ops pred tree
        |> Tuple.second


splitTree : Ops e a -> (a -> Bool) -> a -> FingerTree e a -> Maybe ( FingerTree e a, ( e, a ), FingerTree e a )
splitTree ops pred i tree =
    case tree of
        Empty ->
            Nothing

        Single n ->
            unwrapNode n
                |> Maybe.map (\( e, a ) -> ( Empty, ( e, a ), Empty ))

        Deep _ l m r ->
            let
                vl : a
                vl =
                    ops.add i (digitAnnotation ops l)
            in
            if pred vl then
                let
                    ( ll, x, rr ) =
                        splitDigit ops pred i l
                in
                Maybe.map2
                    (\lll ( e, a ) ->
                        ( digitToTree ops lll
                        , ( e, a )
                        , deepL ops rr m r
                        )
                    )
                    ll
                    (unwrapNode x)

            else
                let
                    vm : a
                    vm =
                        ops.add vl (annotation ops m)
                in
                if pred vm then
                    case splitTree ops pred vl m of
                        Nothing ->
                            Nothing

                        Just ( ml, ( e, a ), mr ) ->
                            splitNode ops pred (ops.add vl (annotation ops ml)) (Tip e a)
                                |> Maybe.map
                                    (\( ll, x, rr ) ->
                                        ( deepR ops l ml ll
                                        , x
                                        , deepL ops rr mr r
                                        )
                                    )

                else
                    let
                        ( ll, x, rr ) =
                            splitDigit ops pred vm r
                    in
                    Maybe.map2
                        (\rrr ( e, a ) ->
                            ( deepR ops l m ll
                            , ( e, a )
                            , digitToTree ops rrr
                            )
                        )
                        rr
                        (unwrapNode x)


unwrapNode : Node e a -> Maybe ( e, a )
unwrapNode node =
    case node of
        Tip e a ->
            Just ( e, a )

        _ ->
            Nothing


splitNode : Ops e a -> (a -> Bool) -> a -> Node e a -> Maybe ( Maybe (Digit e a), ( e, a ), Maybe (Digit e a) )
splitNode ops pred i node =
    case node of
        Tip e a ->
            Just ( Nothing, ( e, a ), Nothing )

        Node2 _ n1 n2 ->
            let
                va : a
                va =
                    ops.add i (nodeAnnotation n1)
            in
            if pred va then
                unwrapNode n1
                    |> Maybe.map (\( e, a ) -> ( Nothing, ( e, a ), Just (D1 n2) ))

            else
                unwrapNode n2
                    |> Maybe.map (\( e, a ) -> ( Just (D1 n1), ( e, a ), Nothing ))

        Node3 _ n1 n2 n3 ->
            let
                va : a
                va =
                    ops.add i (nodeAnnotation n1)
            in
            if pred va then
                unwrapNode n1
                    |> Maybe.map (\( e, a ) -> ( Nothing, ( e, a ), Just (D2 n2 n3) ))

            else
                let
                    vb : a
                    vb =
                        ops.add va (nodeAnnotation n2)
                in
                if pred vb then
                    unwrapNode n2
                        |> Maybe.map (\( e, a ) -> ( Just (D1 n1), ( e, a ), Just (D1 n3) ))

                else
                    unwrapNode n3
                        |> Maybe.map (\( e, a ) -> ( Just (D2 n1 n2), ( e, a ), Nothing ))


splitDigit : Ops e a -> (a -> Bool) -> a -> Digit e a -> ( Maybe (Digit e a), Node e a, Maybe (Digit e a) )
splitDigit ops pred i digit =
    case digit of
        D1 n1 ->
            ( Nothing, n1, Nothing )

        D2 n1 n2 ->
            let
                va : a
                va =
                    ops.add i (nodeAnnotation n1)
            in
            if pred va then
                ( Nothing, n1, Just (D1 n2) )

            else
                ( Just (D1 n1), n2, Nothing )

        D3 n1 n2 n3 ->
            let
                va : a
                va =
                    ops.add i (nodeAnnotation n1)
            in
            if pred va then
                ( Nothing, n1, Just (D2 n2 n3) )

            else
                let
                    vb : a
                    vb =
                        ops.add va (nodeAnnotation n2)
                in
                if pred vb then
                    ( Just (D1 n1), n2, Just (D1 n3) )

                else
                    ( Just (D2 n1 n2), n3, Nothing )

        D4 n1 n2 n3 n4 ->
            let
                va : a
                va =
                    ops.add i (nodeAnnotation n1)
            in
            if pred va then
                ( Nothing, n1, Just (D3 n2 n3 n4) )

            else
                let
                    vb : a
                    vb =
                        ops.add va (nodeAnnotation n2)
                in
                if pred vb then
                    ( Just (D1 n1), n2, Just (D2 n3 n4) )

                else
                    let
                        vc : a
                        vc =
                            ops.add vb (nodeAnnotation n3)
                    in
                    if pred vc then
                        ( Just (D2 n1 n2), n3, Just (D1 n4) )

                    else
                        ( Just (D3 n1 n2 n3), n4, Nothing )


foldlNode : (e -> s -> s) -> s -> Node e a -> s
foldlNode fn init node =
    case node of
        Tip e _ ->
            fn e init

        Node2 _ n1 n2 ->
            foldlNode fn (foldlNode fn init n1) n2

        Node3 _ n1 n2 n3 ->
            foldlNode fn (foldlNode fn (foldlNode fn init n1) n2) n3


foldrNode : (e -> s -> s) -> s -> Node e a -> s
foldrNode fn init node =
    case node of
        Tip e _ ->
            fn e init

        Node2 _ n1 n2 ->
            foldrNode fn (foldrNode fn init n2) n1

        Node3 _ n1 n2 n3 ->
            foldrNode fn (foldrNode fn (foldrNode fn init n3) n2) n1


foldlDigit : (e -> s -> s) -> s -> Digit e a -> s
foldlDigit fn init digit =
    case digit of
        D1 n1 ->
            foldlNode fn init n1

        D2 n1 n2 ->
            foldlNode fn (foldlNode fn init n1) n2

        D3 n1 n2 n3 ->
            foldlNode fn (foldlNode fn (foldlNode fn init n1) n2) n3

        D4 n1 n2 n3 n4 ->
            foldlNode fn (foldlNode fn (foldlNode fn (foldlNode fn init n1) n2) n3) n4


foldrDigit : (e -> s -> s) -> s -> Digit e a -> s
foldrDigit fn init digit =
    case digit of
        D1 n1 ->
            foldrNode fn init n1

        D2 n1 n2 ->
            foldrNode fn (foldrNode fn init n2) n1

        D3 n1 n2 n3 ->
            foldrNode fn (foldrNode fn (foldrNode fn init n3) n2) n1

        D4 n1 n2 n3 n4 ->
            foldrNode fn (foldrNode fn (foldrNode fn (foldrNode fn init n4) n3) n2) n1


{-| Fold with function from the left.
-}
foldl : (e -> s -> s) -> s -> FingerTree e a -> s
foldl fn init tree =
    case tree of
        Empty ->
            init

        Single n ->
            foldlNode fn init n

        Deep _ l m r ->
            foldlDigit fn (foldl fn (foldlDigit fn init l) m) r


{-| Fold with function from the right.
-}
foldr : (e -> s -> s) -> s -> FingerTree e a -> s
foldr fn init tree =
    case tree of
        Empty ->
            init

        Single n ->
            foldrNode fn init n

        Deep _ l m r ->
            foldrDigit fn (foldr fn (foldrDigit fn init r) m) l


countNode : Node e a -> Int
countNode node =
    case node of
        Tip _ _ ->
            1

        Node2 _ n1 n2 ->
            countNode n1 + countNode n2

        Node3 _ n1 n2 n3 ->
            countNode n1 + countNode n2 + countNode n3


countDigit : Digit e a -> Int
countDigit digit =
    case digit of
        D1 n1 ->
            countNode n1

        D2 n1 n2 ->
            countNode n1 + countNode n2

        D3 n1 n2 n3 ->
            countNode n1 + countNode n2 + countNode n3

        D4 n1 n2 n3 n4 ->
            countNode n1 + countNode n2 + countNode n3 + countNode n4


{-| Return the number of elements.
-}
count : FingerTree e a -> Int
count tree =
    case tree of
        Empty ->
            0

        Single n ->
            countNode n

        Deep _ l m r ->
            countDigit l + count m + countDigit r


{-| Reverse a Finger Tree.

O(n)

-}
reverse : Ops e a -> FingerTree e a -> FingerTree e a
reverse ops tree =
    reverseTree ops identity tree


reverseTree : Ops e a2 -> (a1 -> a2) -> FingerTree e a1 -> FingerTree e a2
reverseTree ops fn tree =
    case tree of
        Empty ->
            Empty

        Single n ->
            Single (reverseNode ops fn n)

        Deep _ l m r ->
            deep
                ops
                (reverseDigit ops fn r)
                (reverseTree ops fn m)
                (reverseDigit ops fn l)


reverseDigit : Ops e a2 -> (a1 -> a2) -> Digit e a1 -> Digit e a2
reverseDigit ops fn digit =
    case digit of
        D1 n1 ->
            D1 (reverseNode ops fn n1)

        D2 n1 n2 ->
            D2
                (reverseNode ops fn n2)
                (reverseNode ops fn n1)

        D3 n1 n2 n3 ->
            D3
                (reverseNode ops fn n3)
                (reverseNode ops fn n2)
                (reverseNode ops fn n1)

        D4 n1 n2 n3 n4 ->
            D4
                (reverseNode ops fn n4)
                (reverseNode ops fn n3)
                (reverseNode ops fn n2)
                (reverseNode ops fn n1)


reverseNode : Ops e a2 -> (a1 -> a2) -> Node e a1 -> Node e a2
reverseNode ops fn node =
    case node of
        Tip e n ->
            Tip e (fn n)

        Node2 _ n1 n2 ->
            node2 ops
                (reverseNode ops fn n2)
                (reverseNode ops fn n1)

        Node3 _ n1 n2 n3 ->
            node3 ops
                (reverseNode ops fn n3)
                (reverseNode ops fn n2)
                (reverseNode ops fn n1)


{-| Filter out certain values while transforming the rest.
`filterMap` calls `fn` on each value and only keeps the `Just` results.
-}
filterMap : Ops e2 a2 -> (e1 -> Maybe e2) -> FingerTree e1 a1 -> FingerTree e2 a2
filterMap ops fn tree =
    foldr
        (\x acc ->
            case fn x of
                Nothing ->
                    acc

                Just xx ->
                    leftCons ops xx acc
        )
        empty
        tree


{-| Keep elements that satisfy the test.
-}
filter : Ops e a -> (e -> Bool) -> FingerTree e a -> FingerTree e a
filter ops pred tree =
    foldr
        (\x acc ->
            if pred x then
                leftCons ops x acc

            else
                acc
        )
        empty
        tree


{-| Apply a function to every element of a list.
-}
map : Ops e2 a2 -> (e1 -> e2) -> FingerTree e1 a1 -> FingerTree e2 a2
map ops fn tree =
    case tree of
        Empty ->
            Empty

        Single n ->
            Single (mapNode ops fn n)

        Deep _ l m r ->
            deep
                ops
                (mapDigit ops fn l)
                (map ops fn m)
                (mapDigit ops fn r)


mapNode : Ops e2 a2 -> (e1 -> e2) -> Node e1 a1 -> Node e2 a2
mapNode ops fn node =
    case node of
        Tip e1 _ ->
            let
                e2 : e2
                e2 =
                    fn e1
            in
            Tip e2 (ops.fromElement e2)

        Node2 _ n1 n2 ->
            node2 ops
                (mapNode ops fn n1)
                (mapNode ops fn n2)

        Node3 _ n1 n2 n3 ->
            node3 ops
                (mapNode ops fn n1)
                (mapNode ops fn n2)
                (mapNode ops fn n3)


mapDigit : Ops e2 a2 -> (e1 -> e2) -> Digit e1 a1 -> Digit e2 a2
mapDigit ops fn digit =
    case digit of
        D1 n1 ->
            D1 (mapNode ops fn n1)

        D2 n1 n2 ->
            D2
                (mapNode ops fn n1)
                (mapNode ops fn n2)

        D3 n1 n2 n3 ->
            D3
                (mapNode ops fn n1)
                (mapNode ops fn n2)
                (mapNode ops fn n3)

        D4 n1 n2 n3 n4 ->
            D4
                (mapNode ops fn n1)
                (mapNode ops fn n2)
                (mapNode ops fn n3)
                (mapNode ops fn n4)


{-| Partition a Finger Tree based on some test. The first Finger Tree contains
all values that satisfy the test, and the second list contains all the value that
do not.
-}
partition : Ops e a -> (e -> Bool) -> FingerTree e a -> ( FingerTree e a, FingerTree e a )
partition ops pred tree =
    foldr
        (\x ( yays, nays ) ->
            if pred x then
                ( leftCons ops x yays, nays )

            else
                ( yays, leftCons ops x nays )
        )
        ( empty, empty )
        tree


{-| Figure out whether the FingerTree contains a value.
-}
member : e -> FingerTree e a -> Bool
member e tree =
    case tree of
        Empty ->
            False

        Single n ->
            memberNode e n

        Deep _ l m r ->
            memberDigit e l || member e m || memberDigit e r


memberNode : e -> Node e a -> Bool
memberNode e node =
    case node of
        Tip e1 _ ->
            e == e1

        Node2 _ e1 e2 ->
            memberNode e e1 || memberNode e e2

        Node3 _ e1 e2 e3 ->
            memberNode e e1 || memberNode e e2 || memberNode e e3


memberDigit : e -> Digit e a -> Bool
memberDigit e digit =
    case digit of
        D1 n1 ->
            memberNode e n1

        D2 n1 n2 ->
            memberNode e n1 || memberNode e n2

        D3 n1 n2 n3 ->
            memberNode e n1 || memberNode e n2 || memberNode e n3

        D4 n1 n2 n3 n4 ->
            memberNode e n1 || memberNode e n2 || memberNode e n3 || memberNode e n4


{-| Initialize an array. `initialize n f` creates an array of length `n` with the
element at index `i` initialized to the result of `(f i)`.

The numbers `i` will be in the range `0..(n-1)`.

-}
initialize : Ops e a -> Int -> (Int -> e) -> FingerTree e a
initialize ops n toElement =
    List.foldl
        (\i acc -> rightCons ops (toElement i) acc)
        empty
        (List.range 0 (n - 1))
