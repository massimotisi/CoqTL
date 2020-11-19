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

(*
Placeholder function
*)
Definition TransformEObject (o : TTMetamodel_EObject) : bddMetamodel_EObject :=
    (Build_bddMetamodel_EObject BDDEClass (BuildBDD "000_Placeholder" "Placeholder"))
    .
    
(*
Build_TTMetamodel_EObject 
    LocatedElementEClass 
    Build_Abstract_LocatedElement 
        TruthTableEClass 
        BuildTruthTable  "000_Placeholder"  "" "Placeholder" 
*)
(*
Definition obj: TTMetamodel_EObject := (Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable "1147258851_TruthTable" "" "Test"))).

Definition ExtractLocatedElementFromEObject (o : TTMetamodel_EObject) : LocatedElement :=
    match o with
    | Build_TTMetamodel_EObject 
        _
        b => match b with
             | Build_Abstract_LocatedElement _ _
             |  Builld_Concrete_LocatedElement "" "" ""
             end.
    end.

Eval compute in ExtractLocatedElementFromEObject obj.
*)

Fixpoint TransformAllEObjects (l : list TTMetamodel_EObject) : list bddMetamodel_EObject :=
    match l with
        | nil => nil
        | h :: t => (TransformEObject h) :: (TransformAllEObjects t)
    end.


Definition TT2BDD (tt : Model TTMetamodel_EObject TTMetamodel_ELink)
    : Model bddMetamodel_EObject bddMetamodel_ELink :=
    (Build_Model
        (
            TransformAllEObjects (allModelElements tt)
        )
        (
            (Build_bddMetamodel_ELink BDDTreesEReference (BuildBDDTrees  (BuildBDD "626742236_BDD" "Test") ( nil ))) ::
			nil
        )
    ).

Eval compute in TT2BDD (InputModel).





