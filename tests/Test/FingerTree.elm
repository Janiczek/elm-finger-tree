module Test.FingerTree exposing (suite)

import Expect
import FingerTree exposing (FingerTree)
import Fuzz exposing (Fuzzer)
import Test exposing (Test)


ops : FingerTree.Ops Int Int
ops =
    { empty = 0
    , add = (+)
    , fromElement = \_ -> 1
    }


fingerTreeFuzzer : Fuzzer (FingerTree Int Int)
fingerTreeFuzzer =
    Fuzz.map (FingerTree.fromList ops) (Fuzz.list Fuzz.int)


fingerTreeCreationRecipe : Fuzzer ( CreateVia, List UpdateVia )
fingerTreeCreationRecipe =
    Fuzz.pair
        (Fuzz.oneOf
            [ Fuzz.constant Empty
            , Fuzz.map Singleton Fuzz.int
            , Fuzz.map FromList (Fuzz.list Fuzz.int)
            , Fuzz.map InitializeTimesThreeMod7 Fuzz.int
            ]
        )
        (Fuzz.list
            (Fuzz.oneOf
                [ Fuzz.map LeftCons Fuzz.int
                , Fuzz.map RightCons Fuzz.int
                , Fuzz.map AppendLeft fingerTreeFuzzer
                , Fuzz.map AppendRight fingerTreeFuzzer
                , Fuzz.map TakeUntilNth Fuzz.int
                , Fuzz.map DropUntilNth Fuzz.int
                , Fuzz.constant Reverse
                , Fuzz.map MapTimes Fuzz.int
                , Fuzz.map FilterLessThan Fuzz.int
                , Fuzz.map2 FilterMapTimesLessThan Fuzz.int Fuzz.int
                ]
            )
        )


type CreateVia
    = Empty
    | Singleton Int
    | FromList (List Int)
    | InitializeTimesThreeMod7 Int


type UpdateVia
    = LeftCons Int
    | RightCons Int
    | AppendLeft (FingerTree Int Int)
    | AppendRight (FingerTree Int Int)
    | TakeUntilNth Int
    | DropUntilNth Int
    | Reverse
    | MapTimes Int
    | FilterLessThan Int
    | FilterMapTimesLessThan Int Int


create : CreateVia -> FingerTree Int Int
create via =
    case via of
        Empty ->
            FingerTree.empty

        Singleton n ->
            FingerTree.singleton ops n

        FromList ns ->
            FingerTree.fromList ops ns

        InitializeTimesThreeMod7 n ->
            FingerTree.initialize ops n (\i -> (i * 3) |> modBy 7)


update : UpdateVia -> FingerTree Int Int -> FingerTree Int Int
update via tree =
    case via of
        LeftCons n ->
            FingerTree.leftCons ops n tree

        RightCons n ->
            FingerTree.rightCons ops n tree

        AppendLeft left ->
            FingerTree.append ops left tree

        AppendRight right ->
            FingerTree.append ops tree right

        TakeUntilNth n ->
            FingerTree.takeUntil ops (\x -> x > n) tree

        DropUntilNth n ->
            FingerTree.dropUntil ops (\x -> x > n) tree

        Reverse ->
            FingerTree.reverse ops tree

        MapTimes n ->
            FingerTree.map ops ((*) n) tree

        FilterLessThan n ->
            FingerTree.filter ops (\x -> x < n) tree

        FilterMapTimesLessThan k n ->
            FingerTree.filterMap ops
                (\x ->
                    if x < n then
                        Just (x * k)

                    else
                        Nothing
                )
                tree


suite : Test
suite =
    Test.concat
        [ Test.fuzz fingerTreeCreationRecipe "FingerTree constructed via any combination of operations survives toList/fromList roundtrip" <|
            \( createVia, updates ) ->
                let
                    created : FingerTree Int Int
                    created =
                        List.foldl
                            update
                            (create createVia)
                            updates

                    converted : FingerTree Int Int
                    converted =
                        created
                            |> FingerTree.toList
                            |> FingerTree.fromList ops
                in
                converted
                    |> FingerTree.equals created
                    |> Expect.equal True
                    |> Expect.onFail
                        ("""Didn't survive toList/fromList roundtrip!

Before toList/fromList:

  {BEFORE}

After toList/fromList:

  {AFTER}
"""
                            |> String.replace "{BEFORE}" (Debug.toString created)
                            |> String.replace "{AFTER}" (Debug.toString converted)
                        )
        , Test.fuzz fingerTreeFuzzer "structuralInvariant" <|
            \tree ->
                FingerTree.structuralInvariant ops tree
                    |> Expect.equal True
                    |> Expect.onFail "Didn't hold structural invariant!"
        , Test.fuzz fingerTreeFuzzer "count == toList/length" <|
            \tree ->
                FingerTree.count tree
                    |> Expect.equal
                        (tree
                            |> FingerTree.toList
                            |> List.length
                        )
        , Test.test "empty/count == 0" <|
            \() ->
                FingerTree.empty
                    |> FingerTree.count
                    |> Expect.equal 0
        , Test.fuzz Fuzz.int "singleton/toList == [x]" <|
            \n ->
                FingerTree.singleton ops n
                    |> FingerTree.toList
                    |> Expect.equalLists [ n ]
        , Test.fuzz (Fuzz.list Fuzz.int) "fromList/toList == id" <|
            \ns ->
                FingerTree.fromList ops ns
                    |> FingerTree.toList
                    |> Expect.equalLists ns
        , Test.fuzz fingerTreeFuzzer "foldl :: [] == toList/reverse" <|
            \tree ->
                tree
                    |> FingerTree.foldl (::) []
                    |> Expect.equalLists
                        (tree
                            |> FingerTree.toList
                            |> List.reverse
                        )
        , Test.fuzz fingerTreeFuzzer "foldr :: [] == toList" <|
            \tree ->
                tree
                    |> FingerTree.foldr (::) []
                    |> Expect.equalLists (FingerTree.toList tree)
        , Test.test "foldl :: []" <|
            \() ->
                FingerTree.singleton ops 2
                    |> FingerTree.leftCons ops 1
                    |> FingerTree.rightCons ops 3
                    |> FingerTree.foldl (::) []
                    |> Expect.equalLists [ 3, 2, 1 ]
        , Test.test "foldr :: []" <|
            \() ->
                FingerTree.singleton ops 2
                    |> FingerTree.leftCons ops 1
                    |> FingerTree.rightCons ops 3
                    |> FingerTree.foldr (::) []
                    |> Expect.equalLists [ 1, 2, 3 ]
        , Test.test "empty/isEmpty" <|
            \() ->
                FingerTree.empty
                    |> FingerTree.isEmpty
                    |> Expect.equal True
                    |> Expect.onFail "empty wasn't empty!"
        , Test.fuzz fingerTreeFuzzer "count>0 / not isEmpty" <|
            \tree ->
                case FingerTree.count tree of
                    0 ->
                        FingerTree.isEmpty tree
                            |> Expect.equal True
                            |> Expect.onFail "Tree with count 0 wasn't empty!"

                    _ ->
                        FingerTree.isEmpty tree
                            |> Expect.equal False
                            |> Expect.onFail "Tree with count non-0 was empty!"
        , Test.fuzz fingerTreeFuzzer "leftUncons/leftCons" <|
            \tree ->
                case FingerTree.leftUncons ops tree of
                    Nothing ->
                        Expect.pass

                    Just ( e, tree2 ) ->
                        FingerTree.leftCons ops e tree2
                            |> FingerTree.toList
                            |> Expect.equalLists (FingerTree.toList tree)
        , Test.fuzz fingerTreeFuzzer "rightUncons/rightCons" <|
            \tree ->
                case FingerTree.rightUncons ops tree of
                    Nothing ->
                        Expect.pass

                    Just ( e, tree2 ) ->
                        FingerTree.rightCons ops e tree2
                            |> FingerTree.toList
                            |> Expect.equalLists (FingerTree.toList tree)
        , Test.fuzz2 Fuzz.int fingerTreeFuzzer "head/leftCons" <|
            \x tree ->
                FingerTree.leftCons ops x tree
                    |> FingerTree.head ops
                    |> Expect.equal (Just x)
        , Test.fuzz fingerTreeFuzzer "head/List.head" <|
            \tree ->
                FingerTree.head ops tree
                    |> Expect.equal
                        (tree
                            |> FingerTree.toList
                            |> List.head
                        )
        , Test.fuzz2 Fuzz.int (Fuzz.list Fuzz.int) "tail" <|
            \x xs ->
                FingerTree.fromList ops (x :: xs)
                    |> FingerTree.tail ops
                    |> Maybe.map FingerTree.toList
                    |> Expect.equal (Just xs)
        , Test.fuzz2 Fuzz.int fingerTreeFuzzer "headR/rightCons" <|
            \x tree ->
                FingerTree.rightCons ops x tree
                    |> FingerTree.headR ops
                    |> Expect.equal (Just x)
        , Test.fuzz fingerTreeFuzzer "headR/List.last" <|
            \tree ->
                FingerTree.headR ops tree
                    |> Expect.equal
                        (tree
                            |> FingerTree.toList
                            |> List.reverse
                            |> List.head
                        )
        , Test.fuzz2 Fuzz.int (Fuzz.list Fuzz.int) "tailR" <|
            \x xs ->
                FingerTree.fromList ops (xs ++ [ x ])
                    |> FingerTree.tailR ops
                    |> Maybe.map FingerTree.toList
                    |> Expect.equal (Just xs)
        , Test.fuzz fingerTreeFuzzer "split (0,+,const 1) (x >= 5) -> left has 5 items" <|
            \tree ->
                if FingerTree.count tree >= 5 then
                    tree
                        |> FingerTree.split ops (\a -> a >= 5)
                        |> Tuple.first
                        |> FingerTree.count
                        |> Expect.equal 5

                else
                    Expect.pass
        , Test.only <|
            Test.test "split example" <|
                \() ->
                    [ 10, 20, 30, 40, 50, 60, 70, 80, 90, 100 ]
                        |> FingerTree.fromList ops
                        |> FingerTree.split ops (\a -> a >= 5)
                        |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                        |> Expect.equal ( [ 10, 20, 30, 40, 50 ], [ 60, 70, 80, 90, 100 ] )
        , Test.test "split empty" <|
            \() ->
                FingerTree.empty
                    |> FingerTree.split ops (\a -> a >= 5)
                    |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                    |> Expect.equal ( [], [] )
        , Test.test "split always-false" <|
            \() ->
                List.range 1 10
                    |> FingerTree.fromList ops
                    |> FingerTree.split ops (always False)
                    |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                    |> Expect.equal ( List.range 1 10, [] )
        , Test.test "split always-true" <|
            \() ->
                List.range 1 10
                    |> FingerTree.fromList ops
                    |> FingerTree.split ops (always True)
                    |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                    |> Expect.equal ( [], List.range 1 10 )
        , Test.test "split single item into False (left) bucket" <|
            \() ->
                FingerTree.fromList ops [ 10 ]
                    |> FingerTree.split ops (always False)
                    |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                    |> Expect.equal ( [ 10 ], [] )
        , Test.test "split single item into True (right) bucket" <|
            \() ->
                FingerTree.fromList ops [ 10 ]
                    |> FingerTree.split ops (always True)
                    |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                    |> Expect.equal ( [], [ 10 ] )
        , Test.fuzz2 Fuzz.int fingerTreeFuzzer "leftCons/left append singleton" <|
            \n tree ->
                tree
                    |> FingerTree.leftCons ops n
                    |> FingerTree.toList
                    |> Expect.equalLists
                        (FingerTree.append ops
                            (FingerTree.singleton ops n)
                            tree
                            |> FingerTree.toList
                        )
        , Test.fuzz2 Fuzz.int fingerTreeFuzzer "rightCons/right append singleton" <|
            \n tree ->
                tree
                    |> FingerTree.rightCons ops n
                    |> FingerTree.toList
                    |> Expect.equalLists
                        (FingerTree.append ops
                            tree
                            (FingerTree.singleton ops n)
                            |> FingerTree.toList
                        )
        , Test.test "leftCons" <|
            \() ->
                FingerTree.fromList ops [ 2, 3 ]
                    |> FingerTree.leftCons ops 1
                    |> FingerTree.toList
                    |> Expect.equalLists [ 1, 2, 3 ]
        , Test.test "rightCons" <|
            \() ->
                FingerTree.fromList ops [ 1, 2 ]
                    |> FingerTree.rightCons ops 3
                    |> FingerTree.toList
                    |> Expect.equalLists [ 1, 2, 3 ]
        , Test.fuzz2 fingerTreeFuzzer fingerTreeFuzzer "append" <|
            \left right ->
                FingerTree.append ops left right
                    |> FingerTree.toList
                    |> Expect.equalLists
                        (FingerTree.toList left ++ FingerTree.toList right)
        , Test.todo "takeUntil"
        , Test.todo "dropUntil"
        , Test.fuzz fingerTreeFuzzer "reverse/toList/List.reverse" <|
            \tree ->
                tree
                    |> FingerTree.reverse ops
                    |> FingerTree.toList
                    |> Expect.equalLists
                        (tree
                            |> FingerTree.toList
                            |> List.reverse
                        )
        , Test.fuzz (Fuzz.list Fuzz.int) "filterMap" <|
            \xs ->
                let
                    fn : Int -> Maybe Int
                    fn x =
                        if x > 3 then
                            Just (x * 5)

                        else
                            Nothing
                in
                xs
                    |> FingerTree.fromList ops
                    |> FingerTree.filterMap ops fn
                    |> FingerTree.toList
                    |> Expect.equalLists (List.filterMap fn xs)
        , Test.fuzz (Fuzz.list Fuzz.int) "filter" <|
            \xs ->
                xs
                    |> FingerTree.fromList ops
                    |> FingerTree.filter ops (\x -> x > 3)
                    |> FingerTree.toList
                    |> Expect.equalLists (List.filter (\x -> x > 3) xs)
        , Test.fuzz (Fuzz.list Fuzz.int) "map" <|
            \xs ->
                xs
                    |> FingerTree.fromList ops
                    |> FingerTree.map ops ((+) 1)
                    |> FingerTree.toList
                    |> Expect.equalLists (List.map ((+) 1) xs)
        , Test.fuzz (Fuzz.list Fuzz.int) "partition" <|
            \xs ->
                xs
                    |> FingerTree.fromList ops
                    |> FingerTree.partition ops (modBy 2 >> (==) 0)
                    |> Tuple.mapBoth FingerTree.toList FingerTree.toList
                    |> Expect.equal (List.partition (modBy 2 >> (==) 0) xs)
        , Test.fuzz2 Fuzz.int (Fuzz.list Fuzz.int) "member" <|
            \x xs ->
                xs
                    |> FingerTree.fromList ops
                    |> FingerTree.member x
                    |> Expect.equal (List.member x xs)
                    |> Expect.onFail "Membership didn't agree with a list"
        , Test.fuzz (Fuzz.intRange 0 20) "initialize/List.range" <|
            \n ->
                FingerTree.initialize ops n identity
                    |> FingerTree.toList
                    |> Expect.equalLists (List.range 0 (n - 1))
        , Test.fuzz (Fuzz.intRange 0 20) "initialize *2/List.range" <|
            \n ->
                FingerTree.initialize ops n ((*) 2)
                    |> FingerTree.toList
                    |> Expect.equalLists
                        (List.range 0 (n - 1)
                            |> List.map ((*) 2)
                        )
        ]
