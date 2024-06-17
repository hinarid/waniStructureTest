{-# LANGUAGE OverloadedStrings #-}
module StructureTest.BackwardRule (
  ngList
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

ngList :: [T.Text]
ngList = M.catMaybes [membership, piElimDeduce1,piElimTypecheck1,piElimTypecheck2,piElimDeduce2,piIntroDeduce1]

man = A.aCon "man"
entity = A.aCon "entity"
love = A.aCon "love"
taro = A.aCon "taro"

test :: BR.Rule -> A.SAEnv -> A.AEnv -> (Maybe BR.ProofTerm) -> BR.ProofType -> (Maybe (UDT.Tree QT.DTTrule A.AJudgment)) -> A.AJudgment -> [BR.SubGoal] -> T.Text -> M.Maybe T.Text
test rule sig var maybeTerm targetType expectedTree expectedDside expectedSubgoals errorMessage =
  let goal = BR.Goal sig var maybeTerm [targetType]
      subgoalsets = fst $ rule goal
      [target] = filter (\subgoalset -> expectedTree == (BR.treeFromSubGoalSet subgoalset)) subgoalsets
      tree = case BR.treeFromSubGoalSet target of Just t -> t
      subgoals = BR.subGoalsFromSubGoalSet target
      dside = BR.dsideFromSubGoalSet target
  in if and [(expectedDside == dside),(all (\subgoal -> any (==subgoal) expectedSubgoals) subgoals)] then M.Nothing else M.Just errorMessage

{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3), v6: [y1:entity,y2:man(y1)]-> love (taro)(y1)
[y1:entity,y2:man(y1)]-> love (taro)(y1)
--}
membership :: M.Maybe T.Text
membership =
  let targetFunctionType = A.Arrow [(A.ArrowApp man (A.aVar 0)),entity] ((A.ArrowApp (A.ArrowApp love taro) (A.aVar 1)))
      sig = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]
      var = [ targetFunctionType, A.ArrowApp (man) (A.aVar 1), A.ArrowApp man (A.aVar 1), entity ,  entity, A.ArrowApp man taro]
      targetType = targetFunctionType
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      dsideExpected = A.AJudgment sig var (A.aVar 0) targetType
  in test (BR.membership) sig var M.Nothing targetType (M.Just treeExpected) dsideExpected [] "membership"

{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3), v6: [y1:entity,y2:man(y1)]-> love (taro)(y1)
love(taro)(v3)
--}
piElimDeduce1 :: M.Maybe T.Text
piElimDeduce1 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp man (A.aVar 0)),entity] ((A.ArrowApp (A.ArrowApp love taro) (A.aVar 1)))
      sig = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]
      var = [ targetFunctionType, A.ArrowApp (man) (A.aVar 1), A.ArrowApp man (A.aVar 1), entity ,  entity, A.ArrowApp man taro]
      targetType = A.ArrowApp (A.ArrowApp love taro) (A.aVar 3)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var M.Nothing [entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp man (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.ArrowApp love taro) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var M.Nothing [A.ArrowApp man (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar (-1)) ) (A.aVar (-2)) ) targetType
  in test (BR.piElim) sig var M.Nothing targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected] "piElimDeduce1'"

piElimTypecheck1 :: M.Maybe T.Text
piElimTypecheck1 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp man (A.aVar 0)),entity] ((A.ArrowApp (A.ArrowApp love taro) (A.aVar 1)))
      sig = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]
      var = [ targetFunctionType, A.ArrowApp (man) (A.aVar 1), A.ArrowApp man (A.aVar 1), entity ,  entity, A.ArrowApp man taro]
      targetType = A.ArrowApp (A.ArrowApp love taro) (A.aVar 3)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var (M.Just $ A.aVar 3) [entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp man (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.ArrowApp love taro) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var (M.Just $ A.aVar 1) [A.ArrowApp man (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3) ) (A.aVar 1) ) targetType
  in test (BR.piElim) sig var (M.Just (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3)) (A.aVar 1))) targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected] "piElimDTypeCheck1'"


{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3), v6: [y1:entity,y2:man(y1)]-> love (v2)(y1)
love(v2)(v3)
--}

piElimTypecheck2 :: M.Maybe T.Text
piElimTypecheck2 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp man (A.aVar 0)),entity] ((A.ArrowApp (A.ArrowApp love (A.aVar 5)) (A.aVar 1)))
      sig = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]
      var = [ targetFunctionType, A.ArrowApp (man) (A.aVar 1), A.ArrowApp man (A.aVar 1), entity ,  entity, A.ArrowApp man taro]
      targetType = A.ArrowApp (A.ArrowApp love (A.aVar 4)) (A.aVar 3)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var (M.Just $ A.aVar 3) [entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp man (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.ArrowApp love (A.aVar 4)) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var (M.Just $ A.aVar 1) [A.ArrowApp man (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3) ) (A.aVar 1) ) targetType
  in test (BR.piElim) sig var (M.Just (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3)) (A.aVar 1))) targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected] "piElimTypeCheck2"
    


{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3), v6:entity -> type , v7: [ y0:entity, y1:var 1(var 0),y2:entity ->type,y3:entity,y4:var 4(var 0)] => var 2(var 4) 
man(v2)
--}
piElimDeduce2 :: M.Maybe T.Text
piElimDeduce2 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp (A.aVar 4) (A.aVar 0)),entity,(A.Arrow [entity] A.aType),(A.ArrowApp (A.aVar 1) (A.aVar 0)),entity] (A.ArrowApp (A.aVar 2) (A.aVar 4))
      sig = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]
      var = [ targetFunctionType,A.Arrow [entity] A.aType, A.ArrowApp (man) (A.aVar 1), A.ArrowApp man (A.aVar 1), entity ,  entity, A.ArrowApp man taro]
      targetType = A.ArrowApp man (A.aVar 5)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var M.Nothing [entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp (A.aVar 1) (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.aVar (-3)) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var M.Nothing [A.ArrowApp (A.aVar 1) (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      subgoal3Expected = 
        let goal3Expected  = BR.Goal sig var M.Nothing [A.Arrow [entity] (A.aType)]
            substLst3Expected = []
            clue3Expected = 
              let clueForArg = []
                  clueForRes = M.Just ((A.ArrowApp (A.aVar (-1)) (A.aVar 1)),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal3Expected substLst3Expected clue3Expected
      subgoal4Expected = 
        let goal4Expected = BR.Goal sig var M.Nothing [entity]
            substLst4Expected = []
            clue4Expected = ([(A.ArrowApp (A.aVar 4) (A.aVar (-1)),A.aVar (-2))],M.Nothing)
        in BR.SubGoal goal4Expected substLst4Expected clue4Expected
      subgoal5Expected = 
        let goal5Expected  = BR.Goal sig var M.Nothing [A.ArrowApp (A.aVar 1) (A.aVar (-4))]
            substLst5Expected = [BR.SubstSet [] (A.aVar (-4))]
            clue5Expected = ([],M.Nothing)
        in BR.SubGoal goal5Expected substLst5Expected clue5Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.ArrowApp (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar (-1))) (A.aVar (-2)) ) (A.aVar (-3))) (A.aVar (-4))) (A.aVar (-5))) targetType
  in test (BR.piElim) sig var M.Nothing targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected,subgoal3Expected,subgoal4Expected,subgoal5Expected] "piDeduce2"

{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3)
x:Entity -> man(x)
--}
piIntroDeduce1 :: M.Maybe T.Text
piIntroDeduce1 = 
  let sig = [(("man"),A.Arrow [entity] A.aType),(("love"),A.Arrow [entity,entity] (A.aType)),(("taro"),entity),(("entity"),A.aType)]
      var = [ A.ArrowApp (man) (A.aVar 1), A.ArrowApp man (A.aVar 1), entity ,  entity, A.ArrowApp man taro]
      targetType = A.Arrow [entity] (A.ArrowApp man (A.aVar 0))
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
  in test (BR.piIntro) sig var M.Nothing targetType M.Nothing dsideExpected [subgoal1Expected,subgoal2Expected] "piIntroDeduce1"
    
    -- if and [(dsideExpected == dside),(all (\subgoal -> any (==subgoal) [subgoal1Expected,subgoal2Expected]) subgoals)] then M.Nothing else M.Just "piIntroDeduce1"

