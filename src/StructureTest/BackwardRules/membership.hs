{-# LANGUAGE OverloadedStrings #-}
module StructureTest.BackwardRules.Membership (
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
ngList = [membership]

{-- 
taro:entity,love:[u1:entity,u2:entity]->type,man:[t1:entity]->type,entity:type, 
v1: man(taro), v2:entity, v3: entity, v4: man(v2), v5: man(v3), v6: [y1:entity,y2:man(y1)]-> love (taro)(y1)
[y1:entity,y2:man(y1)]-> love (taro)(y1)
--}
membership :: (T.Text,Bool)
membership =
  let targetFunctionType = A.Arrow [(A.ArrowApp TB.man (A.aVar 0)),TB.entity] ((A.ArrowApp (A.ArrowApp TB.love TB.taro) (A.aVar 1)))
      sig = TB.sigDef
      var = [ targetFunctionType, A.ArrowApp (TB.man) (A.aVar 1), A.ArrowApp TB.man (A.aVar 1), TB.entity , TB.entity, A.ArrowApp TB.man TB.taro]
      targetType = targetFunctionType
      treeExpected = UDT.Tree QT.Var (A.AJudgment sig var (A.aVar 0) (A.shiftIndices targetFunctionType 1 0)) []
      dsideExpected = A.AJudgment sig var (A.aVar 0) targetType
  in TB.test (BR.membership) sig var M.Nothing targetType (M.Just treeExpected) dsideExpected [] "membership"