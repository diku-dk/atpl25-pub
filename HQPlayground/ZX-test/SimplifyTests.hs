module SimplifyTests (tests) where
import HQP.ZX.Syntax
import HQP.ZX.Simplify
import Algebra.Graph.Undirected
import Test.Tasty
import Test.Tasty.HUnit

simplifySuccessfully :: (ZXDiagram -> ZXDiagram) -> TestName -> ZXDiagram -> ZXDiagram -> TestTree
simplifySuccessfully simplifier name input expected = testCase name $ simplifier input @?= expected

tests::TestTree
tests =
    testGroup "Simplification tests"
        [ mergeSpiderTests
        ]


mergeSpiderTests :: TestTree
mergeSpiderTests =
    testGroup "Merge spider tests"
    [
        testCase "Merging path of reds between two greens collapses into green-red-green" $
            mergeReds  (path
                [ Node 0 $ Green (PiHalves 2)
                , Node 1 $ Red (PiHalves 2)
                , Node 2 $ Red (PiHalves 2)
                , Node 3 $ Red (PiHalves 2)
                , Node 4 $ Red (PiHalves 2)
                , Node 5 $ Green (PiHalves 2) ])
            @?= (path 
                [ Node 0 $ Green (PiHalves 2)
                , Node 1 $ Red (PiHalves 0)
                , Node 5 $ Green (PiHalves 2) ]),
        testCase "Merging in distinct regions" $
            mergeReds  (path
                [ Node 0 $ Green (PiHalves 2)
                , Node 1 $ Red (PiHalves 2)
                , Node 2 $ Red (PiHalves 2)
                , Node 3 $ Green (PiHalves 2)
                , Node 4 $ Red (PiHalves 1)
                , Node 5 $ Red (PiHalves 1)
                , Node 6 $ Green (PiHalves 2) ])
            @?= (path 
                [ Node 0 $ Green (PiHalves 2)
                , Node 1 $ Red (PiHalves 0)
                , Node 3 $ Green (PiHalves 2)
                , Node 4 $ Red (PiHalves 2)
                , Node 6 $ Green (PiHalves 2) ])
    ]