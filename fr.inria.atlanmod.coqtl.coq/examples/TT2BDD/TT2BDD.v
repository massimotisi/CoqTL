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

Definition TT2BDD (tt : Model TTMetamodel_EObject TTMetamodel_ELink)
    : Model bddMetamodel_EObject bddMetamodel_ELink :=
    (Build_Model
        (
            TransformAllEObjects (allModelElements tt)
        )
        (
			nil
        )
    ).

Eval compute in TT2BDD (InputModel).





