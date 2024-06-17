import qualified StructureTest.TestBase as TB
import qualified StructureTest.BackwardRule as BR

import qualified Data.Time as TIME
import qualified Data.Text as T

test :: [T.Text]
test = BR.ngList

main :: IO()
main = do
  start <- TIME.getCurrentTime
  putStr $ let ngLst = BR.ngList in if null ngLst then "passed" else ("Failed: " ++ (T.unpack $ T.intercalate (T.pack ", ") ngLst))
  end <- TIME.getCurrentTime
  putStrLn $ " with " ++ (show $TIME.diffUTCTime end start)