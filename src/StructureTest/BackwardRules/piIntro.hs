{-# LANGUAGE OverloadedStrings #-}
module StructureTest.BackwardRules.PiIntro (
  ngList
)
where
import qualified DTS.Prover.Wani.BackwardRule as BR
import qualified DTS.QueryTypes as QT
import qualified Interface.Tree as UDT
import qualified DTS.UDTTdeBruijn as UDdB

import qualified StructureTest.BackwardRules.TestBase as TB

import qualified DTS.Prover.Wani.Arrowterm as A
import qualified Data.Maybe as M
import qualified Data.Text as T

ngList :: [(T.Text,Bool)]
ngList = [piIntroDeduce1]

{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3)
x:Entity -> man(x)
--}
piIntroDeduce1 :: (T.Text,Bool)
piIntroDeduce1 = 
  let sig = TB.sigDef
      var = [ A.ArrowApp TB.man (A.aVar 1), A.ArrowApp TB.man (A.aVar 1), TB.entity ,  TB.entity, A.ArrowApp TB.man TB.taro]
      targetType = A.Arrow [TB.entity] (A.ArrowApp TB.man (A.aVar 0))
      (hyp,con) = case targetType of A.Arrow l t -> (l,t)
      goal = BR.Goal sig var  M.Nothing [targetType]
      [target] = fst $ BR.piIntro goal
      tree = case BR.treeFromSubGoalSet target of Just t -> t
      subgoals = BR.subGoalsFromSubGoalSet target
      dside = BR.dsideFromSubGoalSet target
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var (M.Just $ targetType) [A.aType, A.Conclusion UDdB.Kind]
            substLst1Expected = []
            clue1Expected = ([],M.Nothing)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig (hyp ++ var) M.Nothing [con]
            substLst2Expected = []
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.betaReduce $ A.addLam (length hyp) (A.aVar (-2))) targetType
  in TB.test (BR.piIntro) sig var M.Nothing targetType M.Nothing dsideExpected [subgoal1Expected,subgoal2Expected] "piIntroDeduce1"
