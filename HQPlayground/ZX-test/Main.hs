import Test.Tasty
import ConverterTests
import SimplifyTests


main :: IO ()
main = defaultMain $ testGroup "ZX tests" [SimplifyTests.tests,ConverterTests.tests]