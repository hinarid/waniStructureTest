{-# LANGUAGE OverloadedStrings #-}
module StructureTest.BackwardRules.TestBase (
  -- * sigs
  man,entity,love,taro,
  -- * defaults
  sigDef,
  -- * function
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

-- | default signature \(\text{taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type}\)
sigDef :: A.SAEnv
sigDef = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]

test :: 
  BR.Rule -- ^ deduce rule
    -> A.SAEnv -- ^ sig
    -> A.AEnv -- ^ var
    -> (Maybe BR.ProofTerm) -- ^ `M.Nothing` is used for deduce, (`M.Just` term) is used for typecheck
    -> BR.ProofType -- ^ arrowterm to be proved
    -> (Maybe (UDT.Tree QT.DTTrule A.AJudgment)) -- ^ if the rule is piElim or membership, you should set this parameter
    -> A.AJudgment -- ^ expected downSide
    -> [BR.SubGoal] -- ^ expected subgoals
    -> T.Text -- ^ given text for label (ex. "memberhip", "piIntroTypeCheck1")
    -> (T.Text,Bool) -- ^ (message, whether if expected subgoalset is found)
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