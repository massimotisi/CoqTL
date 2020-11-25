Require Import String.
Open Scope string_scope.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.Model.
Require Import core.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import examples.TT2BDD.TT.
Require Import examples.TT2BDD.BDDv2.

Require Import examples.TT2BDD.tests.xorTT.


Definition TransformTruthTable (lE: LocatedElement): option bddMetamodel_EObject :=
    match lE with
    | Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable  id _ name) => Some (Build_bddMetamodel_EObject BDDEClass (BuildBDD id name))
    | _ => None
    end.

Definition TransformPort (lE : LocatedElement) : option bddMetamodel_EObject :=
    match (TTMetamodel_LocatedElement_DownCast TT.PortEClass lE) with
    | Some abstractPort => 
        match abstractPort with
        | TT.Build_Abstract_Port TT.InputPortEClass (TT.BuildInputPort id _ name) => Some (Build_bddMetamodel_EObject PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort id name))) 
        | TT.Build_Abstract_Port TT.OutputPortEClass (TT.BuildOutputPort id _ name) => Some (Build_bddMetamodel_EObject PortEClass (Build_Abstract_Port OutputPortEClass (BuildOutputPort id name))) 
        end
    | None => None
    end.

Definition TransformRow (lE: LocatedElement) : option bddMetamodel_EObject :=
    match lE with
    | Build_Abstract_LocatedElement RowEClass (BuildRow  id _) => Some (Build_bddMetamodel_EObject TreeEClass (Build_Abstract_Tree LeafEClass (BuildLeaf id )))
    | _ => None
    end.

Definition TransformCell (lE: LocatedElement) : option bddMetamodel_EObject :=
    match TTMetamodel_LocatedElement_DownCast CellEClass lE with
    | Some cell =>
        match Cell_getPort cell InputModel with
        | Some abstractPort => 
            match abstractPort with
            | TT.Build_Abstract_Port TT.OutputPortEClass _ => Some (Build_bddMetamodel_EObject AssignmentEClass (BuildAssignment (Cell_getId cell) (Cell_getValue cell))) 
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end.
    
Definition TransformEObject (o : TTMetamodel_EObject) : option bddMetamodel_EObject :=
    match (TTMetamodel_toEClass LocatedElementEClass o) with
    | Some locatedElement => 
        match locatedElement with
        | Build_Abstract_LocatedElement TruthTableEClass _ => TransformTruthTable locatedElement
        | Build_Abstract_LocatedElement TT.PortEClass _ => TransformPort locatedElement
        | Build_Abstract_LocatedElement RowEClass _ => TransformRow locatedElement
        | Build_Abstract_LocatedElement CellEClass _ => TransformCell locatedElement
        | Build_Concrete_LocatedElement _ _  =>  None
        end
    | None => None
    end.

Fixpoint TransformAllEObjects (l : list TTMetamodel_EObject) : list bddMetamodel_EObject :=
    match l with
    | nil => nil
    | h :: t => 
        match TransformEObject h with
        | Some eObject => eObject :: (TransformAllEObjects t)
        | None => (TransformAllEObjects t)
        end
    end.

Definition TT2BDD_baseobjects (tt : Model TTMetamodel_EObject TTMetamodel_ELink)
    : Model bddMetamodel_EObject bddMetamodel_ELink :=
    (Build_Model
        (
            TransformAllEObjects (allModelElements tt)
        )
        (
			nil
        )
    ).

Fixpoint GetTruthTable (l : list TTMetamodel_EObject) : option TruthTable := 
    match l with 
    | nil => None
    | h :: t => 
        match (TTMetamodel_toEClass LocatedElementEClass h) with
        | Some locatedElement => 
            match locatedElement with
            | Build_Abstract_LocatedElement TruthTableEClass retTT => Some retTT
            | _  => (GetTruthTable t)
            end
        | None => (GetTruthTable t)
        end
    end
    .
Eval compute in GetTruthTable (allModelElements ( InputModel)).



Inductive MyTree : Set :=
  | MySubtree : (*portId*) string -> (*name*) string -> (*forZero*) MyTree -> (*forOne*) MyTree -> MyTree
  | MyLeaf : (*name*) string -> (*assignments*) list Assignment -> MyTree
  .

Fixpoint IterInputPorts (ports : list TT.Port) (subTreeName : string) : MyTree :=
    match ports with 
    | nil => MyLeaf "" nil
    | abstractPort :: t => 
        match abstractPort with
        | TT.Build_Abstract_Port TT.InputPortEClass (TT.BuildInputPort inputPortId _ inputPortName) => MySubtree inputPortId (subTreeName++inputPortName) (IterInputPorts t (subTreeName++inputPortName++"0")) (IterInputPorts t (subTreeName++inputPortName++"1"))
        | _ => IterInputPorts t subTreeName
        end
    end.

Definition CellsPortHasId (portId : string) (tt : TTModel) (cell : Cell) : bool :=
    match Cell_getPort cell tt with 
    | None => false
    | Some port => eqb (TT.Port_getId port) portId
    end
.

Definition RowGetCellForPortId (row : Row) (tt : TTModel) (portId : string) : option Cell := 
    match Row_getCells row tt with
    | None => None
    | Some l => 
        match filter (CellsPortHasId portId tt) l with
        | nil => None
        | h :: t => Some h
        end
    end
.

Definition RowMatchesValueForPort (portId : string) (value : bool) (tt : TTModel) (row : Row) : bool := 
    match RowGetCellForPortId row tt portId with 
    | None => false
    | Some cell => Bool.eqb (Cell_getValue cell) value
    end
.


Definition ReduceMatchingRows (matchingRows : option (list Row)) (portId : string) (value : bool) (tt : TTModel) : option (list Row) := 
    match matchingRows with
    | None => None
    | Some l => 
        match filter (RowMatchesValueForPort portId value tt) l with
        | nil => None
        | l => Some l
        end
    end
.

Fixpoint AssignmentListFromRowOutputPorts (ports : list TT.Port) (row : Row) (tt : TTModel) : list Assignment :=
    match ports with 
    | nil => nil
    | abstractPort :: tail => 
        match abstractPort with
        | TT.Build_Abstract_Port TT.OutputPortEClass (TT.BuildOutputPort outputPortId _ _) => 
            match RowGetCellForPortId row tt outputPortId with 
            | None => AssignmentListFromRowOutputPorts tail row tt
            | Some cell => (BuildAssignment (Cell_getId cell) (Cell_getValue cell)) :: AssignmentListFromRowOutputPorts tail row tt
            end
        | _ => AssignmentListFromRowOutputPorts tail row tt
        end
    end
.


Fixpoint FillMyTreeLeaves (myTree : MyTree) (ports : list TT.Port) (subTreeName : string) (matchingRows : option (list Row)) (tt : TTModel) : MyTree :=
    match myTree with 
    | MySubtree portId name forZero forOne => 
        MySubtree portId name (FillMyTreeLeaves forZero ports (name++"0") (ReduceMatchingRows matchingRows portId false tt) tt) (FillMyTreeLeaves forOne ports (name++"1") (ReduceMatchingRows matchingRows portId true tt) tt)
    | MyLeaf name _ => 
        match matchingRows with
        | None => MyLeaf subTreeName nil
        | Some nil => MyLeaf subTreeName nil
        | Some (row::_) => MyLeaf subTreeName (AssignmentListFromRowOutputPorts ports row tt)
        end 
    end
.

Fixpoint IterOutputPorts (myTree : MyTree) (ports : list TT.Port) (subTreeName : string) : MyTree :=
    match ports with 
    | nil => MyLeaf "" nil
    | abstractPort :: t => 
        match abstractPort with
        | TT.Build_Abstract_Port TT.OutputPortEClass (TT.BuildOutputPort outputPortId _ outputPortName) => MyLeaf (subTreeName++outputPortName) nil
        | _ =>  match myTree with 
                | MySubtree portId name forZero forOne => MySubtree portId name (IterOutputPorts forZero t (name++"0")) (IterOutputPorts forOne t (name++"1"))
                | myLeaf => myLeaf
                end
        end
    end.

Definition deOptionTruthTable (o : option TruthTable) : TruthTable := 
    match o with
    | Some myTruthTable => myTruthTable
    | None => BuildTruthTable "" "" ""
    end
.

Definition deOptionList (t : Type) (o : option (list t)) : list t := 
    match o with
    | Some l => l
    | None => nil
    end
.
    
(*
Eval compute in 
    deOptionList TT.Port (
        TruthTable_getPorts (
            deOptionTruthTable (
                GetTruthTable (
                    allModelElements (InputModel)
                )
            )
        ) InputModel
    )
.
*)

(*Eval compute in IterInputPorts (
    deOptionList TT.Port (
        TruthTable_getPorts (
            deOptionTruthTable (
                GetTruthTable (
                    allModelElements (InputModel)
                )
            )
        ) InputModel
    ))
    ""
.
*)

Eval compute in IterOutputPorts (IterInputPorts (
    deOptionList TT.Port (
        TruthTable_getPorts (
            deOptionTruthTable (
                GetTruthTable (
                    allModelElements (InputModel)
                )
            )
        ) InputModel
    ))
    "") (
        deOptionList TT.Port (
            TruthTable_getPorts (
                deOptionTruthTable (
                    GetTruthTable (
                        allModelElements (InputModel)
                    )
                )
            ) InputModel
        )) ""
.


Eval compute in FillMyTreeLeaves (IterInputPorts (
    deOptionList TT.Port (
        TruthTable_getPorts (
            deOptionTruthTable (
                GetTruthTable (
                    allModelElements (InputModel)
                )
            )
        ) InputModel
    ))
    "")
    (deOptionList TT.Port (TruthTable_getPorts (deOptionTruthTable (GetTruthTable (allModelElements (InputModel)))) InputModel))
    ""
    (TruthTable_getRows (deOptionTruthTable (GetTruthTable (allModelElements (InputModel)))) InputModel)
    InputModel
.






