module FingerTree exposing
    ( FingerTree, Ops
    , empty, singleton, fromList, initialize, repeat
    , toList
    , foldl, foldr
    , equals
    , isEmpty, count
    , member, all, any
    , leftUncons, rightUncons
    , head, tail, headR, tailR
    , split, partition
    , annotation
    , leftCons, rightCons, append
    , takeUntil, dropUntil
    , reverse
    , map, filter, filterMap, indexedMap
    , structuralInvariant
    -- TODO some of these will be only useful in FingerTree.Array etc.
    -- TODO range
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

@docs empty, singleton, fromList, initialize, repeat


## Conversion

@docs toList
@docs foldl, foldr


## Query

@docs equals
@docs isEmpty, count
@docs member, all, any
@docs leftUncons, rightUncons
@docs head, tail, headR, tailR
@docs split, partition
@docs annotation


## Update

@docs leftCons, rightCons, append
@docs takeUntil, dropUntil
@docs reverse
@docs map, filter, filterMap, indexedMap


## Testing

@docs structuralInvariant

-}


{-| A Finger Tree structure.

The `e` (short for "element") is the data you want the tree to hold.

The `a` (short for "annotation") is a measure. For example, for a Deque this
would be an Int; each element would have measure 1, and recursive internal
nodes would each have measure of the sum of the items inside.

-}
type FingerTree e ann
    = Empty
    | Single (Node e ann)
    | Deep ann (Digit e ann) (FingerTree e ann) (Digit e ann)


type Digit e ann
    = D1 (Node e ann)
    | D2 (Node e ann) (Node e ann)
    | D3 (Node e ann) (Node e ann) (Node e ann)
    | D4 (Node e ann) (Node e ann) (Node e ann) (Node e ann)


type Node e ann
    = Tip e ann
    | Node2 ann (Node e ann) (Node e ann)
    | Node3 ann (Node e ann) (Node e ann) (Node e ann)


{-| Monoidal operations on the elements of the Finger Tree and their
annotations.
-}
type alias Ops e ann =
    { empty : ann
    , add : ann -> ann -> ann
    , fromElement : e -> ann
    }


nodeAnnotation : Node e ann -> ann
nodeAnnotation node =
    -- Named `gmn` in the Isabelle implementation.
    case node of
        Tip _ ann ->
            ann

        Node2 ann _ _ ->
            ann

        Node3 ann _ _ _ ->
            ann


digitAnnotation : Ops e ann -> Digit e ann -> ann
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
annotation : Ops e ann -> FingerTree e ann -> ann
annotation ops tree =
    -- Named `gmft` in the Isabelle implementation.
    case tree of
        Empty ->
            ops.empty

        Single n ->
            nodeAnnotation n

        Deep ann _ _ _ ->
            ann


{-| The Isabelle implementation used this to prove correctness;
we use it to property-test the port.
-}
structuralInvariant : Ops e ann -> FingerTree e ann -> Bool
structuralInvariant ops tree =
    -- Named `ft-invar` in the Isabelle implementation.
    isLevelNTree 0 tree && isMeasuredTree ops tree


isLevelNNode : Int -> Node e ann -> Bool
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


isLevelNDigit : Int -> Digit e ann -> Bool
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


isLevelNTree : Int -> FingerTree e ann -> Bool
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


isMeasuredNode : Ops e ann -> Node e ann -> Bool
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


isMeasuredDigit : Ops e ann -> Digit e ann -> Bool
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


isMeasuredTree : Ops e ann -> FingerTree e ann -> Bool
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


nodeToList : Node e ann -> List e
nodeToList node =
    case node of
        Tip e _ ->
            [ e ]

        Node2 _ n1 n2 ->
            nodeToList n1 ++ nodeToList n2

        Node3 _ n1 n2 n3 ->
            nodeToList n1 ++ nodeToList n2 ++ nodeToList n3


digitToList : Digit e ann -> List e
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
toList : FingerTree e ann -> List e
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
empty : FingerTree e ann
empty =
    Empty


{-| A singleton Finger Tree.

O(1)

-}
singleton : Ops e ann -> e -> FingerTree e ann
singleton ops e =
    Single (Tip e (ops.fromElement e))


{-| Compare two Finger Trees for equality.

Using `==` for Finger Trees is not reliable, since there are multiple
representations for the same conceptual value.

-}
equals : FingerTree e ann -> FingerTree e ann -> Bool
equals tree1 tree2 =
    toList tree1 == toList tree2


{-| Append a node at the left end.
-}
leftConsNode : Ops e ann -> Node e ann -> FingerTree e ann -> FingerTree e ann
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
rightConsNode : Ops e ann -> Node e ann -> FingerTree e ann -> FingerTree e ann
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
deep : Ops e ann -> Digit e ann -> FingerTree e ann -> Digit e ann -> FingerTree e ann
deep ({ add } as ops) l m r =
    let
        ann : ann
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
node2 : Ops e ann -> Node e ann -> Node e ann -> Node e ann
node2 { add } n1 n2 =
    let
        ann : ann
        ann =
            add
                (nodeAnnotation n1)
                (nodeAnnotation n2)
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
leftCons : Ops e ann -> e -> FingerTree e ann -> FingerTree e ann
leftCons ops e tree =
    leftConsNode ops (Tip e (ops.fromElement e)) tree


{-| Append element at the right end.

O(log(n)), O(1) amortized

-}
rightCons : Ops e ann -> e -> FingerTree e ann -> FingerTree e ann
rightCons ops e tree =
    rightConsNode ops (Tip e (ops.fromElement e)) tree


rightConsAll : Ops e ann -> List e -> FingerTree e ann -> FingerTree e ann
rightConsAll ops es tree =
    List.foldl (rightCons ops) tree es


{-| Convert list to a Finger Tree.

O(n log(n)), O(n) amortized

-}
fromList : Ops e ann -> List e -> FingerTree e ann
fromList ops list =
    List.foldr
        (\e acc -> leftCons ops e acc)
        Empty
        list


digitToTree : Ops e ann -> Maybe (Digit e ann) -> FingerTree e ann
digitToTree ops digit =
    case digit of
        Nothing ->
            Empty

        Just digit_ ->
            case digit_ of
                D1 n1 ->
                    Single n1

                D2 n1 n2 ->
                    deep ops (D1 n1) Empty (D1 n2)

                D3 n1 n2 n3 ->
                    deep ops (D2 n1 n2) Empty (D1 n3)

                D4 n1 n2 n3 n4 ->
                    deep ops (D2 n1 n2) Empty (D2 n3 n4)


nodeToDigit : Node e ann -> Digit e ann
nodeToDigit node =
    case node of
        Tip e ann ->
            D1 (Tip e ann)

        Node2 _ n1 n2 ->
            D2 n1 n2

        Node3 _ n1 n2 n3 ->
            D3 n1 n2 n3


digitToNodes : Digit e ann -> List (Node e ann)
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
leftmostNode : Ops e ann -> FingerTree e ann -> Maybe ( Node e ann, FingerTree e ann )
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
                    Just ( n1, digitToTree ops (Just r) )

                Just ( n2, m2 ) ->
                    Just ( n1, deep ops (nodeToDigit n2) m2 r )


{-| Detach the right node.

Called `viewRn` in the Isabelle implementation.

-}
rightmostNode : Ops e ann -> FingerTree e ann -> Maybe ( Node e ann, FingerTree e ann )
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
                    Just ( n1, digitToTree ops (Just l) )

                Just ( n2, m2 ) ->
                    Just ( n1, deep ops l m2 (nodeToDigit n2) )


{-| Detach the leftmost element.

O(log(n)), O(1) amortized

-}
leftUncons : Ops e ann -> FingerTree e ann -> Maybe ( e, FingerTree e ann )
leftUncons ops tree =
    leftmostNode ops tree
        |> Maybe.map (Tuple.mapFirst nodeUnwrap)


{-| Detach the rightmost element.

O(log(n)), O(1) amortized

-}
rightUncons : Ops e ann -> FingerTree e ann -> Maybe ( e, FingerTree e ann )
rightUncons ops tree =
    rightmostNode ops tree
        |> Maybe.map (Tuple.mapFirst nodeUnwrap)


{-| Check whether the tree is empty.

O(1)

-}
isEmpty : FingerTree e ann -> Bool
isEmpty tree =
    tree == Empty


{-| Get the leftmost element.

O(log(n))

-}
head : Ops e ann -> FingerTree e ann -> Maybe e
head ops tree =
    leftUncons ops tree
        |> Maybe.map Tuple.first


{-| Get all but the leftmost element.

O(log(n))

-}
tail : Ops e ann -> FingerTree e ann -> Maybe (FingerTree e ann)
tail ops tree =
    leftUncons ops tree
        |> Maybe.map Tuple.second


{-| Get the rightmost element.

O(log(n))

-}
headR : Ops e ann -> FingerTree e ann -> Maybe e
headR ops tree =
    rightUncons ops tree
        |> Maybe.map Tuple.first


{-| Get all but the rightmost element.

O(log(n))

-}
tailR : Ops e ann -> FingerTree e ann -> Maybe (FingerTree e ann)
tailR ops tree =
    rightUncons ops tree
        |> Maybe.map Tuple.second


leftConsNodes : Ops e ann -> List (Node e ann) -> FingerTree e ann -> FingerTree e ann
leftConsNodes ops nodes tree =
    List.foldr (leftConsNode ops) tree nodes


rightConsNodes : Ops e ann -> List (Node e ann) -> FingerTree e ann -> FingerTree e ann
rightConsNodes ops nodes tree =
    List.foldl (rightConsNode ops) tree nodes


compactNodes : Ops e ann -> List (Node e ann) -> List (Node e ann)
compactNodes ops nodes =
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


append3 : Ops e ann -> FingerTree e ann -> List (Node e ann) -> FingerTree e ann -> FingerTree e ann
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
append : Ops e ann -> FingerTree e ann -> FingerTree e ann -> FingerTree e ann
append ops t1 t2 =
    append3 ops t1 [] t2


toDigit : List (Node e ann) -> Maybe (Digit e ann)
toDigit es =
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


deepL :
    Ops e ann
    -> List (Node e ann)
    -> FingerTree e ann
    -> Digit e ann
    -> FingerTree e ann
deepL ops l m r =
    case toDigit l of
        Nothing ->
            case leftmostNode ops m of
                Nothing ->
                    rightConsAll ops (digitToList r) Empty

                Just ( a, mm ) ->
                    deep ops (nodeToDigit a) mm r

        Just ll ->
            deep ops ll m r


deepR :
    Ops e ann
    -> Digit e ann
    -> FingerTree e ann
    -> List (Node e ann)
    -> FingerTree e ann
deepR ops l m r =
    case toDigit r of
        Nothing ->
            case rightmostNode ops m of
                Nothing ->
                    rightConsAll ops (digitToList l) Empty

                Just ( a, mm ) ->
                    deep ops l mm (nodeToDigit a)

        Just rr ->
            deep ops l m rr


{-| Split a Finger Tree at a point where the predicate on the accumulated
annotation of the prefix changes from 'False' to 'True'.

O(log(min(i,n-i)))

For predictable results, ensure there is only one such point, ie. that
the predicate is monotonic.

LOW-LEVEL WARNING:

Note this predicate works on the annotations (measures), not on the values!
What this annotation is is specific to the given Finger Tree usage, and is what
allows efficient operations for eg. random access or the priority queue behaviour.

-}
split :
    Ops e ann
    -> (ann -> Bool)
    -> FingerTree e ann
    -> ( FingerTree e ann, FingerTree e ann )
split ops pred tree =
    if isEmpty tree then
        ( Empty, Empty )

    else if pred ops.empty then
        ( Empty, tree )

    else if pred (annotation ops tree) then
        case splitTree ops pred ops.empty tree of
            Nothing ->
                impossible "Proven not to happen in the `isEmpty tree` condition above. We just can't forward that guarantee into the splitTree function without unergonomic new types."

            Just ( l, x, r ) ->
                ( l, leftConsNode ops x r )

    else
        ( tree, Empty )


impossible : String -> a
impossible reason =
    let
        overflowTheStack : Int -> Int
        overflowTheStack x =
            1 + overflowTheStack x

        _ =
            overflowTheStack 0
    in
    impossible reason


{-| Given a monotonic predicate, returns the largest prefix that doesn't satisfy
the predicate.

O(log(min(i,n-i)))

-}
takeUntil : Ops e ann -> (ann -> Bool) -> FingerTree e ann -> FingerTree e ann
takeUntil ops pred tree =
    split ops pred tree
        |> Tuple.first


{-| Given a monotonic predicate, returns the rest after removing the largest
prefix that doesn't satisfy the predicate.

O(log(min(i,n-i)))

-}
dropUntil : Ops e ann -> (ann -> Bool) -> FingerTree e ann -> FingerTree e ann
dropUntil ops pred tree =
    split ops pred tree
        |> Tuple.second


splitTree :
    Ops e ann
    -> (ann -> Bool)
    -> ann
    -> FingerTree e ann
    -> Maybe ( FingerTree e ann, Node e ann, FingerTree e ann )
splitTree ops pred i tree =
    case tree of
        Empty ->
            Nothing

        Single e ->
            Just ( Empty, e, Empty )

        Deep _ l m r ->
            let
                vl : ann
                vl =
                    ops.add i (digitAnnotation ops l)
            in
            if pred vl then
                let
                    ( ll, x, rr ) =
                        splitDigit ops pred i l
                in
                Just
                    ( rightConsNodes ops ll Empty
                    , x
                    , deepL ops rr m r
                    )

            else
                let
                    vm : ann
                    vm =
                        ops.add vl (annotation ops m)
                in
                if pred vm then
                    case splitTreeAlias ops pred vl m of
                        Nothing ->
                            Nothing

                        Just ( ml, xs, mr ) ->
                            splitDigit ops pred (ops.add vl (annotation ops ml)) (nodeToDigit xs)
                                |> (\( ll, x, rr ) ->
                                        Just
                                            ( deepR ops l ml ll
                                            , x
                                            , deepL ops rr mr r
                                            )
                                   )

                else
                    splitDigit ops pred vm r
                        |> (\( ll, x, rr ) ->
                                Just
                                    ( deepR ops l m ll
                                    , x
                                    , rightConsNodes ops rr Empty
                                    )
                           )


splitTreeAlias : Ops e ann -> (ann -> Bool) -> ann -> FingerTree e ann -> Maybe ( FingerTree e ann, Node e ann, FingerTree e ann )
splitTreeAlias =
    splitTree


nodeUnwrap : Node e ann -> e
nodeUnwrap node =
    case node of
        Tip e _ ->
            e

        _ ->
            impossible "Proven not to happen in the Isabelle paper"


splitDigit : Ops e ann -> (ann -> Bool) -> ann -> Digit e ann -> ( List (Node e ann), Node e ann, List (Node e ann) )
splitDigit ops pred i digit =
    case digit of
        D1 n1 ->
            ( [], n1, [] )

        D2 n1 n2 ->
            let
                ii : ann
                ii =
                    ops.add i (nodeAnnotation n1)
            in
            if pred ii then
                ( [], n1, [ n2 ] )

            else
                splitDigit ops pred ii (D1 n2)
                    -- TODO is this e1::l correct or should it have been l++e1?
                    |> (\( l, x, r ) -> ( n1 :: l, x, r ))

        D3 n1 n2 n3 ->
            let
                ii : ann
                ii =
                    ops.add i (nodeAnnotation n1)
            in
            if pred ii then
                ( [], n1, [ n2, n3 ] )

            else
                splitDigit ops pred ii (D2 n2 n3)
                    -- TODO is this e1::l correct or should it have been l++e1?
                    |> (\( l, x, r ) -> ( n1 :: l, x, r ))

        D4 n1 n2 n3 n4 ->
            let
                ii : ann
                ii =
                    ops.add i (nodeAnnotation n1)
            in
            if pred ii then
                ( [], n1, [ n2, n3, n4 ] )

            else
                splitDigit ops pred ii (D3 n2 n3 n4)
                    -- TODO is this e1::l correct or should it have been l++e1?
                    |> (\( l, x, r ) -> ( n1 :: l, x, r ))


foldlNode : (e -> s -> s) -> s -> Node e ann -> s
foldlNode fn init node =
    case node of
        Tip e _ ->
            fn e init

        Node2 _ n1 n2 ->
            foldlNode fn (foldlNode fn init n1) n2

        Node3 _ n1 n2 n3 ->
            foldlNode fn (foldlNode fn (foldlNode fn init n1) n2) n3


foldrNode : (e -> s -> s) -> s -> Node e ann -> s
foldrNode fn init node =
    case node of
        Tip e _ ->
            fn e init

        Node2 _ n1 n2 ->
            foldrNode fn (foldrNode fn init n2) n1

        Node3 _ n1 n2 n3 ->
            foldrNode fn (foldrNode fn (foldrNode fn init n3) n2) n1


foldlDigit : (e -> s -> s) -> s -> Digit e ann -> s
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


foldrDigit : (e -> s -> s) -> s -> Digit e ann -> s
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
foldl : (e -> s -> s) -> s -> FingerTree e ann -> s
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
foldr : (e -> s -> s) -> s -> FingerTree e ann -> s
foldr fn init tree =
    case tree of
        Empty ->
            init

        Single n ->
            foldrNode fn init n

        Deep _ l m r ->
            foldrDigit fn (foldr fn (foldrDigit fn init r) m) l


countNode : Node e ann -> Int
countNode node =
    case node of
        Tip _ _ ->
            1

        Node2 _ n1 n2 ->
            countNode n1 + countNode n2

        Node3 _ n1 n2 n3 ->
            countNode n1 + countNode n2 + countNode n3


countDigit : Digit e ann -> Int
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
count : FingerTree e ann -> Int
count tree =
    case tree of
        Empty ->
            0

        Single n ->
            countNode n

        Deep _ l m r ->
            countDigit l + count m + countDigit r


{-| Reverse ann Finger Tree.

O(n)

-}
reverse : Ops e ann -> FingerTree e ann -> FingerTree e ann
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
filter : Ops e ann -> (e -> Bool) -> FingerTree e ann -> FingerTree e ann
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


{-| Apply a function to every element of a list and its index.
-}
indexedMap : Ops e2 a2 -> (Int -> e1 -> e2) -> FingerTree e1 a1 -> FingerTree e2 a2
indexedMap ops fn tree =
    indexedMapTree ops fn 0 tree
        |> Tuple.first


indexedMapTree : Ops e2 a2 -> (Int -> e1 -> e2) -> Int -> FingerTree e1 a1 -> ( FingerTree e2 a2, Int )
indexedMapTree ops fn i0 tree =
    case tree of
        Empty ->
            ( Empty, i0 )

        Single n ->
            let
                ( n_, i1 ) =
                    indexedMapNode ops fn i0 n
            in
            ( Single n_, i1 )

        Deep _ l m r ->
            let
                ( l_, i1 ) =
                    indexedMapDigit ops fn i0 l

                ( m_, i2 ) =
                    indexedMapTree ops fn i1 m

                ( r_, i3 ) =
                    indexedMapDigit ops fn i2 r
            in
            ( deep ops l_ m_ r_, i3 )


indexedMapNode : Ops e2 a2 -> (Int -> e1 -> e2) -> Int -> Node e1 a1 -> ( Node e2 a2, Int )
indexedMapNode ops fn i0 node =
    case node of
        Tip e _ ->
            let
                e_ =
                    fn i0 e
            in
            ( Tip e_ (ops.fromElement e_)
            , i0 + 1
            )

        Node2 _ n1 n2 ->
            let
                ( n1_, i1 ) =
                    indexedMapNode ops fn i0 n1

                ( n2_, i2 ) =
                    indexedMapNode ops fn i1 n2
            in
            ( node2 ops n1_ n2_, i2 )

        Node3 _ n1 n2 n3 ->
            let
                ( n1_, i1 ) =
                    indexedMapNode ops fn i0 n1

                ( n2_, i2 ) =
                    indexedMapNode ops fn i1 n2

                ( n3_, i3 ) =
                    indexedMapNode ops fn i2 n3
            in
            ( node3 ops n1_ n2_ n3_, i3 )


indexedMapDigit : Ops e2 a2 -> (Int -> e1 -> e2) -> Int -> Digit e1 a1 -> ( Digit e2 a2, Int )
indexedMapDigit ops fn i0 digit =
    case digit of
        D1 n1 ->
            let
                ( n1_, i1 ) =
                    indexedMapNode ops fn i0 n1
            in
            ( D1 n1_, i1 )

        D2 n1 n2 ->
            let
                ( n1_, i1 ) =
                    indexedMapNode ops fn i0 n1

                ( n2_, i2 ) =
                    indexedMapNode ops fn i1 n2
            in
            ( D2 n1_ n2_, i2 )

        D3 n1 n2 n3 ->
            let
                ( n1_, i1 ) =
                    indexedMapNode ops fn i0 n1

                ( n2_, i2 ) =
                    indexedMapNode ops fn i1 n2

                ( n3_, i3 ) =
                    indexedMapNode ops fn i2 n3
            in
            ( D3 n1_ n2_ n3_, i3 )

        D4 n1 n2 n3 n4 ->
            let
                ( n1_, i1 ) =
                    indexedMapNode ops fn i0 n1

                ( n2_, i2 ) =
                    indexedMapNode ops fn i1 n2

                ( n3_, i3 ) =
                    indexedMapNode ops fn i2 n3

                ( n4_, i4 ) =
                    indexedMapNode ops fn i3 n4
            in
            ( D4 n1_ n2_ n3_ n4_, i4 )


{-| Partition a Finger Tree based on some test. The first Finger Tree contains
all values that satisfy the test, and the second list contains all the value that
do not.
-}
partition : Ops e ann -> (e -> Bool) -> FingerTree e ann -> ( FingerTree e ann, FingerTree e ann )
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
member : e -> FingerTree e ann -> Bool
member e tree =
    case tree of
        Empty ->
            False

        Single n ->
            memberNode e n

        Deep _ l m r ->
            memberDigit e l || member e m || memberDigit e r


memberNode : e -> Node e ann -> Bool
memberNode e node =
    case node of
        Tip e1 _ ->
            e == e1

        Node2 _ e1 e2 ->
            memberNode e e1 || memberNode e e2

        Node3 _ e1 e2 e3 ->
            memberNode e e1 || memberNode e e2 || memberNode e e3


memberDigit : e -> Digit e ann -> Bool
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
initialize : Ops e ann -> Int -> (Int -> e) -> FingerTree e ann
initialize ops n toElement =
    List.foldl
        (\i acc -> rightCons ops (toElement i) acc)
        empty
        (List.range 0 (n - 1))


{-| Repeat an element n times.
-}
repeat : Ops e ann -> Int -> e -> FingerTree e ann
repeat ops n el =
    List.repeat n el
        |> fromList ops


{-| Check if all values in the Finger Tree satisfy the predicate.

Returns True when used with an empty list.

-}
all : (e -> Bool) -> FingerTree e ann -> Bool
all pred tree =
    case tree of
        Empty ->
            True

        Single n ->
            allNode pred n

        Deep _ l m r ->
            allDigit pred l && all pred m && allDigit pred r


allNode : (e -> Bool) -> Node e ann -> Bool
allNode pred node =
    case node of
        Tip e _ ->
            pred e

        Node2 _ n1 n2 ->
            allNode pred n1 && allNode pred n2

        Node3 _ n1 n2 n3 ->
            allNode pred n1 && allNode pred n2 && allNode pred n3


allDigit : (e -> Bool) -> Digit e ann -> Bool
allDigit pred digit =
    case digit of
        D1 n1 ->
            allNode pred n1

        D2 n1 n2 ->
            allNode pred n1 && allNode pred n2

        D3 n1 n2 n3 ->
            allNode pred n1 && allNode pred n2 && allNode pred n3

        D4 n1 n2 n3 n4 ->
            allNode pred n1 && allNode pred n2 && allNode pred n3 && allNode pred n4


{-| Check if any values in the Finger Tree satisfy the predicate.

Returns False when used with an empty list.

-}
any : (e -> Bool) -> FingerTree e ann -> Bool
any pred tree =
    case tree of
        Empty ->
            True

        Single n ->
            anyNode pred n

        Deep _ l m r ->
            anyDigit pred l || any pred m || anyDigit pred r


anyNode : (e -> Bool) -> Node e ann -> Bool
anyNode pred node =
    case node of
        Tip e _ ->
            pred e

        Node2 _ n1 n2 ->
            anyNode pred n1 || anyNode pred n2

        Node3 _ n1 n2 n3 ->
            anyNode pred n1 || anyNode pred n2 || anyNode pred n3


anyDigit : (e -> Bool) -> Digit e ann -> Bool
anyDigit pred digit =
    case digit of
        D1 n1 ->
            anyNode pred n1

        D2 n1 n2 ->
            anyNode pred n1 || anyNode pred n2

        D3 n1 n2 n3 ->
            anyNode pred n1 || anyNode pred n2 || anyNode pred n3

        D4 n1 n2 n3 n4 ->
            anyNode pred n1 || anyNode pred n2 || anyNode pred n3 || anyNode pred n4
