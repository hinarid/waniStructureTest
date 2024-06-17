{-# LANGUAGE OverloadedStrings #-}
module StructureTest.BackwardRules.TestBase (
  -- sigs
  man,entity,love,taro,
  sigDef,
  test
)
where
import qualified DTS.UDTTdeBruijn as UDdB
import qualified DTS.Prover.Wani.BackwardRule as BR
import qualified DTS.Prover.Wani.WaniBase as WB 
import qualified DTS.QueryTypes as QT
import qualified Interface.Tree as UDT

import qualified DTS.Prover.Wani.Arrowterm as A
import qualified Data.Maybe as M
import qualified Data.Text as T

man = A.aCon "man"
entity = A.aCon "entity"
love = A.aCon "love"
taro = A.aCon "taro"

sigDef :: A.SAEnv
sigDef = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]

test :: BR.Rule -> A.SAEnv -> A.AEnv -> (Maybe BR.ProofTerm) -> BR.ProofType -> (Maybe (UDT.Tree QT.DTTrule A.AJudgment)) -> A.AJudgment -> [BR.SubGoal] -> T.Text -> (T.Text,Bool)
test rule sig var maybeTerm targetType expectedTree expectedDside expectedSubgoals errorMessage =
  let goal = BR.Goal sig var maybeTerm [targetType]
      subgoalsets = fst $ rule goal
  in case filter (\subgoalset -> expectedTree == (BR.treeFromSubGoalSet subgoalset)) subgoalsets of
    [target] -> 
      let
        tree = case BR.treeFromSubGoalSet target of Just t -> t
        subgoals = BR.subGoalsFromSubGoalSet target
        dside = BR.dsideFromSubGoalSet target
      in if and [(expectedDside == dside),(all (\subgoal -> any (==subgoal) expectedSubgoals) subgoals)] then (errorMessage,True) else (errorMessage,False)
    _ -> (T.concat ["no match tree in ",errorMessage],False)