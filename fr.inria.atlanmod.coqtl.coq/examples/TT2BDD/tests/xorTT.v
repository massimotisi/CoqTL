(********************************************************************
	@name Coq declarations for model
	@date 2020/11/16 17:27:43
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import examples.TT2BDD.TT.


Definition InputModel : Model TTMetamodel_EObject TTMetamodel_ELink :=
	(Build_Model
		(
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable "1147258851_TruthTable" "" "Test"))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1691538257_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1368594774_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "626742236_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1931444790_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "158453976_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "2011482127_InputPort" "" "b")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1800659519_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "459848100_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "726281927_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "577405636_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1335505684_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "992768706_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "2145970759_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port OutputPortEClass (BuildOutputPort "905735620_OutputPort" "" "s")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1447499999_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "891095110_InputPort" "" "a")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "500772834_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1226204845_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "393040818_Cell" "" true))) :: 
		nil)
		(
		(Build_TTMetamodel_ELink TruthTablePortsEReference (BuildTruthTablePorts  (BuildTruthTable "1147258851_TruthTable" "" "Test") ( (Build_Abstract_Port InputPortEClass  (BuildInputPort "891095110_Port" "" "a") ) ::  (Build_Abstract_Port InputPortEClass  (BuildInputPort "2011482127_Port" "" "b") ) ::  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "905735620_Port" "" "s") ) :: nil ))) ::
		(Build_TTMetamodel_ELink TruthTableRowsEReference (BuildTruthTableRows  (BuildTruthTable "1147258851_TruthTable" "" "Test") ( (BuildRow "2145970759_Row" "") ::  (BuildRow "500772834_Row" "") ::  (BuildRow "1335505684_Row" "") ::  (BuildRow "158453976_Row" "") :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1691538257_Cell" "" false)  (BuildRow "500772834_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1691538257_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "2011482127_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1368594774_Cell" "" false)  (BuildRow "158453976_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1368594774_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "891095110_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "626742236_Cell" "" false)  (BuildRow "2145970759_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "626742236_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "905735620_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1931444790_Cell" "" true)  (BuildRow "2145970759_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1931444790_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "2011482127_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "158453976_Row" "")  (BuildTruthTable "1147258851_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "158453976_Row" "") ( (BuildCell "1368594774_Cell" "" false) ::  (BuildCell "726281927_Cell" "" true) ::  (BuildCell "1447499999_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1800659519_Cell" "" false)  (BuildRow "500772834_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1800659519_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "891095110_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "459848100_Cell" "" false)  (BuildRow "500772834_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "459848100_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "905735620_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "726281927_Cell" "" true)  (BuildRow "158453976_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "726281927_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "2011482127_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "577405636_Cell" "" true)  (BuildRow "2145970759_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "577405636_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "891095110_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1335505684_Row" "")  (BuildTruthTable "1147258851_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1335505684_Row" "") ( (BuildCell "992768706_Cell" "" true) ::  (BuildCell "1226204845_Cell" "" false) ::  (BuildCell "393040818_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "992768706_Cell" "" true)  (BuildRow "1335505684_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "992768706_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "891095110_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "2145970759_Row" "")  (BuildTruthTable "1147258851_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "2145970759_Row" "") ( (BuildCell "577405636_Cell" "" true) ::  (BuildCell "1931444790_Cell" "" true) ::  (BuildCell "626742236_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1447499999_Cell" "" true)  (BuildRow "158453976_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1447499999_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "905735620_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "500772834_Row" "")  (BuildTruthTable "1147258851_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "500772834_Row" "") ( (BuildCell "1800659519_Cell" "" false) ::  (BuildCell "1691538257_Cell" "" false) ::  (BuildCell "459848100_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1226204845_Cell" "" false)  (BuildRow "1335505684_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1226204845_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "2011482127_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "393040818_Cell" "" true)  (BuildRow "1335505684_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "393040818_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "905735620_Port" "" "s") ))) ::
		nil)
	).