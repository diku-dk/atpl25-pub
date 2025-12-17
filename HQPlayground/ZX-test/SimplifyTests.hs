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
            mergeReds  (path [Node 0 $ Green pi,Node 1 $ Red pi,Node 2 $ Red pi,Node 3 $ Red pi,Node 4 $ Red pi,Node 5 $ Green pi])
            @?= (path [Node 0 $ Green pi,Node 1 $ Red (4*pi),Node 5 $ Green pi])
    ]