{-# LANGUAGE OverloadedStrings #-}
module StructureTest.BackwardRules.PiElim (
  ngList
)
where
import qualified DTS.Prover.Wani.BackwardRule as BR
import qualified DTS.QueryTypes as QT
import qualified Interface.Tree as UDT

import qualified StructureTest.BackwardRules.TestBase as TB

import qualified DTS.Prover.Wani.Arrowterm as A
import qualified Data.Maybe as M
import qualified Data.Text as T

ngList :: [(T.Text,Bool)]
ngList = [piElimDeduce1,piElimTypecheck1,piElimTypecheck2,piElimDeduce2]

{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man (taro), v2:entity, v3: entity, v4: man (v2), v5: man (v3), v6: [y1:entity,y2:man (y1)]-> love (taro)(y1)
love(taro)(v3)
--}
piElimDeduce1 :: (T.Text,Bool)
piElimDeduce1 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp TB.man (A.aVar 0)),TB.entity] ((A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar 1)))
      sig = TB.sigDef
      var = [ targetFunctionType, A.ArrowApp (TB.man) (A.aVar 1), A.ArrowApp TB.man (A.aVar 1), TB.entity ,  TB.entity, A.ArrowApp TB.man TB.taro]
      targetType = A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar 3)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var M.Nothing [TB.entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp TB.man (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var M.Nothing [A.ArrowApp TB.man (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar (-1)) ) (A.aVar (-2)) ) targetType
  in TB.test (BR.piElim) sig var M.Nothing targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected] "piElimDeduce1"

piElimTypecheck1 :: (T.Text,Bool)
piElimTypecheck1 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp TB.man (A.aVar 0)),TB.entity] ((A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar 1)))
      sig = TB.sigDef
      var = [ targetFunctionType, A.ArrowApp (TB.man) (A.aVar 1), A.ArrowApp TB.man (A.aVar 1), TB.entity , TB.entity, A.ArrowApp TB.man TB.taro]
      targetType = A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar 3)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var (M.Just $ A.aVar 3) [TB.entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp TB.man (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var (M.Just $ A.aVar 1) [A.ArrowApp TB.man (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3) ) (A.aVar 1) ) targetType
  in TB.test (BR.piElim) sig var (M.Just (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3)) (A.aVar 1))) targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected] "piElimDTypeCheck1"


{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man (taro), v2:entity, v3: entity, v4: man (v2), v5: man (v3), v6: [y1:entity,y2:man (y1)]-> love (v2)(y1)
love(v2)(v3)
--}

piElimTypecheck2 :: (T.Text,Bool)
piElimTypecheck2 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp TB.man (A.aVar 0)),TB.entity] ((A.ArrowApp (A.ArrowApp TB.love (A.aVar 5)) (A.aVar 1)))
      sig = TB.sigDef
      var = [ targetFunctionType, A.ArrowApp (TB.man) (A.aVar 1), A.ArrowApp TB.man (A.aVar 1), TB.entity , TB.entity, A.ArrowApp TB.man TB.taro]
      targetType = A.ArrowApp (A.ArrowApp TB.love (A.aVar 4)) (A.aVar 3)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var (M.Just $ A.aVar 3) [TB.entity]
            substLst1Expected = []
            clue1Expected = 
              let clueForArg = [(A.ArrowApp TB.man (A.aVar (-1)),A.aVar (-2))]
                  clueForRes = M.Just ((A.ArrowApp (A.ArrowApp TB.love (A.aVar 4)) (A.aVar (-1))),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal1Expected substLst1Expected clue1Expected
      subgoal2Expected = 
        let goal2Expected = BR.Goal sig var (M.Just $ A.aVar 1) [A.ArrowApp TB.man (A.aVar (-1))]
            substLst2Expected = [BR.SubstSet [] (A.aVar (-1))]
            clue2Expected = ([],M.Nothing)
        in BR.SubGoal goal2Expected substLst2Expected clue2Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3) ) (A.aVar 1) ) targetType
  in TB.test (BR.piElim) sig var (M.Just (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar 3)) (A.aVar 1))) targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected] "piElimTypeCheck2"
    


{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man (taro), v2:entity, v3: entity, v4: man (v2), v5: man (v3), v6:TB.entity -> type , v7: [ y0:entity, y1:var 1(var 0),y2:TB.entity ->type,y3:entity,y4:var 4(var 0)] => var 2(var 4) 
man (v2)
--}
piElimDeduce2 :: (T.Text,Bool)
piElimDeduce2 = 
  let targetFunctionType = A.Arrow [(A.ArrowApp (A.aVar 4) (A.aVar 0)),TB.entity,(A.Arrow [TB.entity] A.aType),(A.ArrowApp (A.aVar 1) (A.aVar 0)),TB.entity] (A.ArrowApp (A.aVar 2) (A.aVar 4))
      sig = TB.sigDef
      var = [ targetFunctionType,A.Arrow [TB.entity] A.aType, A.ArrowApp (TB.man) (A.aVar 1), A.ArrowApp TB.man (A.aVar 1), TB.entity , TB.entity, A.ArrowApp TB.man TB.taro]
      targetType = A.ArrowApp TB.man (A.aVar 5)
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      subgoal1Expected = 
        let goal1Expected  = BR.Goal sig var M.Nothing [TB.entity]
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
        let goal3Expected  = BR.Goal sig var M.Nothing [A.Arrow [TB.entity] (A.aType)]
            substLst3Expected = []
            clue3Expected = 
              let clueForArg = []
                  clueForRes = M.Just ((A.ArrowApp (A.aVar (-1)) (A.aVar 1)),targetType)
              in (clueForArg,clueForRes)
        in BR.SubGoal goal3Expected substLst3Expected clue3Expected
      subgoal4Expected = 
        let goal4Expected = BR.Goal sig var M.Nothing [TB.entity]
            substLst4Expected = []
            clue4Expected = ([(A.ArrowApp (A.aVar 4) (A.aVar (-1)),A.aVar (-2))],M.Nothing)
        in BR.SubGoal goal4Expected substLst4Expected clue4Expected
      subgoal5Expected = 
        let goal5Expected  = BR.Goal sig var M.Nothing [A.ArrowApp (A.aVar 1) (A.aVar (-4))]
            substLst5Expected = [BR.SubstSet [] (A.aVar (-4))]
            clue5Expected = ([],M.Nothing)
        in BR.SubGoal goal5Expected substLst5Expected clue5Expected
      dsideExpected = A.AJudgment sig var (A.ArrowApp (A.ArrowApp (A.ArrowApp (A.ArrowApp (A.ArrowApp (A.aVar 0) (A.aVar (-1))) (A.aVar (-2)) ) (A.aVar (-3))) (A.aVar (-4))) (A.aVar (-5))) targetType
  in TB.test (BR.piElim) sig var M.Nothing targetType (M.Just treeExpected) dsideExpected [subgoal1Expected,subgoal2Expected,subgoal3Expected,subgoal4Expected,subgoal5Expected] "piDeduce2"
