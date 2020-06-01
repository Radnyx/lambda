module Main where
import Test.Tasty (defaultMain)

import LF
import LFParser
import qualified LFUnitTests

main :: IO ()
main = defaultMain LFUnitTests.unitTests