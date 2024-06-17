{-# LANGUAGE OverloadedStrings #-}
import qualified StructureTest.BackwardRules.Membership as Membership
import qualified StructureTest.BackwardRules.PiElim as PiElim
import qualified StructureTest.BackwardRules.PiIntro as PiIntro

import qualified Data.Time as TIME
import qualified Data.Text as T

test :: [(T.Text,Bool)]
test = Membership.ngList ++ PiElim.ngList ++ PiIntro.ngList

main :: IO()
main = do
  start <- TIME.getCurrentTime
  putStr $ if null (filter (not . snd) test) then ("passed: " ++ (T.unpack $ T.intercalate (T.pack ", ") $(fst.unzip) $filter snd test)) else ("Failed: " ++ (T.unpack $ T.intercalate (T.pack ", ") $(fst.unzip) $filter (not.snd) test))
  end <- TIME.getCurrentTime
  putStrLn $ " with " ++ (show $TIME.diffUTCTime end start)