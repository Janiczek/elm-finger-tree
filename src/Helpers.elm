module Helpers exposing (impossible)


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
