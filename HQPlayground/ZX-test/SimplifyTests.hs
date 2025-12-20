module SimplifyTests (tests) where
import HQP.ZX.Syntax
import HQP.ZX.Simplify
import Algebra.Graph.Undirected
import Test.Tasty
import Test.Tasty.HUnit

tests::TestTree
tests =
    testGroup "Simplification tests"
        [ mergeSpiderTests
        , removeSimpleSpiderTests
        ]

mergeSpiderTests :: TestTree
mergeSpiderTests =
    testGroup "Merge spider tests"
    [
        testCase "Merging path of reds" $
            mergeRedSpiders  (path
                [ Node 0 $ Green $ PiHalves 2
                , Node 1 $ Red $ PiHalves 2
                , Node 2 $ Red $ PiHalves 1
                , Node 3 $ Red $ PiHalves 2
                , Node 4 $ Green $ PiHalves 2 ])
            @?= (path 
                [ Node 0 $ Green $ PiHalves 2
                , Node 3 $ Red $ PiHalves 1 -- Id 1, 2, 3 could all be correct.
                , Node 4 $ Green $ PiHalves 2 ]),
        testCase "Merging paths in distinct regions" $
            mergeRedSpiders  (path
                [ Node 0 $ Green $ PiHalves 2
                , Node 1 $ Red $ PiHalves 2
                , Node 2 $ Red $ PiHalves 2
                , Node 3 $ Green $ PiHalves 2
                , Node 4 $ Red $ PiHalves 1
                , Node 5 $ Red $ PiHalves 1
                , Node 6 $ Green $ PiHalves 2 ])
            @?= (path 
                [ Node 0 $ Green $ PiHalves 2
                , Node 1 $ Red 0
                , Node 3 $ Green $ PiHalves 2
                , Node 4 $ Red $ PiHalves 2
                , Node 6 $ Green $ PiHalves 2 ]),
        testCase "Merging non paths" $
            mergeRedSpiders  (edges -- TODO: Find a more readable way to construct these test cases
                [ (Node 0 $ Green $ PiHalves 2, Node 1 $ Red $ PiHalves 1)
                , (Node 0 $ Green $ PiHalves 2, Node 2 $ Red $ PiHalves 2)
                , (Node 1 $ Red $ PiHalves 1, Node 2 $ Red $ PiHalves 2)
                , (Node 1 $ Red $ PiHalves 1, Node 3 $ Green $ PiHalves 2) 
                , (Node 2 $ Red $ PiHalves 2, Node 3 $ Green $ PiHalves 2) ])
            @?= (edges 
                [ (Node 0 $ Green $ PiHalves 2, Node 1 $ Red $ PiHalves 3)
                , (Node 1 $ Red $ PiHalves 3, Node 3 $ Green $ PiHalves 2) ])
    ]

removeSimpleSpiderTests :: TestTree
removeSimpleSpiderTests =
    testGroup "Remove simple spider tests"
    [
        testCase "Removing single zero phase simple spider" $
            removeSimpleSpiders  (path
                [ Node 0 $ Green $ PiHalves 2
                , Node 1 $ Red 0
                , Node 2 $ Green $ PiHalves 2 ])
            @?= (path 
                [ Node 0 $ Green $ PiHalves 2
                , Node 2 $ Green $ PiHalves 2 ]),
        testCase "Removing multiple zero phase simple spiders" $
            removeSimpleSpiders  (path
                [ Node 0 $ Green $ PiHalves 2
                , Node 1 $ Red 0
                , Node 2 $ Green 0])
            @?= (path 
                [ Node 0 $ Green $ PiHalves 2 ])
    ]