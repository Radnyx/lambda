module Main where
import Test.Tasty (defaultMain)

import qualified LFUnitTests


main :: IO ()
main = defaultMain LFUnitTests.unitTests