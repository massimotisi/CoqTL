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
    
Definition TransformEObject (o : TTMetamodel_EObject) : option bddMetamodel_EObject :=
    match (TTMetamodel_toEClass LocatedElementEClass o) with
    | Some locatedElement => 
        match locatedElement with
        | Build_Abstract_LocatedElement TruthTableEClass _ => TransformTruthTable locatedElement
        | Build_Abstract_LocatedElement TT.PortEClass _ => TransformPort locatedElement
        | Build_Abstract_LocatedElement RowEClass _ => TransformRow locatedElement
        | Build_Abstract_LocatedElement CellEClass _ => None
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



Inductive MyTree : Set :=
  | MySubtree : (*portId*) string -> (*name*) string -> (*forZero*) MyTree -> (*forOne*) MyTree -> MyTree
  | MyLeaf : (*rowId*) string -> (*name*) string -> (*assignments*) list Assignment -> MyTree
  .

Fixpoint IterInputPorts (ports : list TT.Port) (subTreeName : string) : MyTree :=
    match ports with 
    | nil => MyLeaf "" "" nil
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

Fixpoint AssignmentListFromRowOutputPorts (ports : list TT.Port) (row : Row) (tt : TTModel) (subTreeName : string) : list Assignment :=
    match ports with 
    | nil => nil
    | abstractPort :: tail => 
        match abstractPort with
        | TT.Build_Abstract_Port TT.OutputPortEClass (TT.BuildOutputPort outputPortId _ outputPortName) => 
            match RowGetCellForPortId row tt outputPortId with 
            | None => AssignmentListFromRowOutputPorts tail row tt subTreeName
            | Some cell => (BuildAssignment (subTreeName++outputPortName) (Cell_getValue cell)) :: AssignmentListFromRowOutputPorts tail row tt subTreeName
            end
        | _ => AssignmentListFromRowOutputPorts tail row tt subTreeName
        end
    end
.


Fixpoint FillMyTreeLeaves (myTree : MyTree) (ports : list TT.Port) (subTreeName : string) (matchingRows : option (list Row)) (tt : TTModel) : MyTree :=
    match myTree with 
    | MySubtree portId name forZero forOne => 
        MySubtree portId name (FillMyTreeLeaves forZero ports (name++"0") (ReduceMatchingRows matchingRows portId false tt) tt) (FillMyTreeLeaves forOne ports (name++"1") (ReduceMatchingRows matchingRows portId true tt) tt)
    | MyLeaf rowId name _ => 
        match matchingRows with
        | None => MyLeaf rowId subTreeName nil
        | Some nil => MyLeaf rowId subTreeName nil
        | Some (row::_) => MyLeaf (Row_getId row) subTreeName (AssignmentListFromRowOutputPorts ports row tt subTreeName)
        end 
    end
.


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





Fixpoint bddEOjectListFromMyTree (myTree : MyTree) : list bddMetamodel_EObject := 
    match myTree with
    | MySubtree portId name forZero forOne => app (bddEOjectListFromMyTree forZero) ((Build_bddMetamodel_EObject TreeEClass (Build_Abstract_Tree SubtreeEClass (BuildSubtree ("Subtree_"++name)))) :: (bddEOjectListFromMyTree forOne))
    | MyLeaf rowId name assignments => map (fun assignment : Assignment => Build_bddMetamodel_EObject AssignmentEClass assignment) assignments
    end
.

Definition TT2BDD_baseobjects (tt : TTModel) : bddModel :=
    (Build_Model
        (
            app (TransformAllEObjects (allModelElements tt))    (bddEOjectListFromMyTree (FillMyTreeLeaves (IterInputPorts (
                                                                    deOptionList TT.Port (
                                                                        TruthTable_getPorts (
                                                                            deOptionTruthTable (
                                                                                GetTruthTable (
                                                                                    allModelElements (tt)
                                                                                )
                                                                            )
                                                                        ) tt
                                                                    ))
                                                                    "")
                                                                    (deOptionList TT.Port (TruthTable_getPorts (deOptionTruthTable (GetTruthTable (allModelElements (tt)))) tt))
                                                                    ""
                                                                    (TruthTable_getRows (deOptionTruthTable (GetTruthTable (allModelElements (tt)))) tt)
                                                                    tt)
                                                                )
        )
        nil
    )
.



Fixpoint bddEOjectList_getOutputPortFromName (bddEObjects : list bddMetamodel_EObject) (portName : string) : option OutputPort :=
    match bddEObjects with 
    | nil => None
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject PortEClass obj =>
            match obj with 
            | Build_Abstract_Port OutputPortEClass outputPort => 
                match outputPort with 
                | BuildOutputPort _ portName => Some outputPort
                end
            | Build_Abstract_Port InputPortEClass (BuildInputPort _ portName) => bddEOjectList_getOutputPortFromName tail portName
            end
        | _ => bddEOjectList_getOutputPortFromName tail portName
        end
    end
.

Fixpoint bddEOjectList_getInputPortFromId (bddEObjects : list bddMetamodel_EObject) (portId : string) : option InputPort :=
    match bddEObjects with 
    | nil => None
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject PortEClass obj =>
            match obj with 
            | Build_Abstract_Port InputPortEClass inputPort => 
                match inputPort with 
                | BuildInputPort portId _ => Some inputPort
                end
            | Build_Abstract_Port OutputPortEClass (BuildOutputPort portId _) => bddEOjectList_getInputPortFromId tail portId
            end
        | _ => bddEOjectList_getInputPortFromId tail portId
        end
    end
.

Definition lastChar (str : string) := substring ((String.length str) - 1) 1 str .

Definition myTreeToTree (myTree : MyTree) : Tree := 
    match myTree with
    | MySubtree portId name forZero forOne => Build_Abstract_Tree SubtreeEClass (BuildSubtree ("Subtree_"++name))
    | MyLeaf rowId name assignments => Build_Abstract_Tree LeafEClass (BuildLeaf rowId)
    end
.


Fixpoint bddELinkListFromMyTree (myTree : MyTree) (bddEObjects : list bddMetamodel_EObject) : list bddMetamodel_ELink := 
    match myTree with
    | MySubtree portId name forZero forOne => 
        match bddEOjectList_getInputPortFromId bddEObjects portId with 
            | Some inputPort =>
            (Build_bddMetamodel_ELink SubtreePortEReference 
                (BuildSubtreePort
                    (BuildSubtree ("Subtree_"++name))
                    inputPort
                )
            )
            ::
            (app 
                (
                    (Build_bddMetamodel_ELink SubtreeTreeForZeroEReference 
                            (BuildSubtreeTreeForZero 
                                (BuildSubtree ("Subtree_"++name)) 
                                (myTreeToTree forZero)
                            )
                    )
                    ::
                    (Build_bddMetamodel_ELink TreeOwnerSubtreeForZeroEReference 
                            (BuildTreeOwnerSubtreeForZero 
                                (myTreeToTree forZero)
                                ((BuildSubtree ("Subtree_"++name))::nil) 
                            )
                    )
                    ::
                    (bddELinkListFromMyTree forZero bddEObjects)
                )
                (
                    (Build_bddMetamodel_ELink SubtreeTreeForOneEReference 
                            (BuildSubtreeTreeForOne 
                                (BuildSubtree ("Subtree_"++name)) 
                                (myTreeToTree forOne)
                            )
                    )
                    ::
                    (Build_bddMetamodel_ELink TreeOwnerSubtreeForOneEReference 
                            (BuildTreeOwnerSubtreeForOne
                                (myTreeToTree forOne)
                                ((BuildSubtree ("Subtree_"++name))::nil) 
                            )
                    )
                    ::
                    (bddELinkListFromMyTree forOne bddEObjects)
                )
            )
        | None => nil
        end
    | MyLeaf rowId name assignments =>
        (Build_bddMetamodel_ELink LeafAssignmentsEReference (BuildLeafAssignments (BuildLeaf rowId) assignments))
        ::
        (match bddEOjectList_getOutputPortFromName (bddEObjects) (lastChar name) with 
        | None => nil
        | Some port => 
            app
            (map (fun assignment : Assignment => (Build_bddMetamodel_ELink AssignmentOwnerEReference (BuildAssignmentOwner assignment (BuildLeaf rowId)))) assignments)
            (map (fun assignment : Assignment => (Build_bddMetamodel_ELink AssignmentPortEReference (BuildAssignmentPort assignment port))) assignments)
        end)
    end
.

Fixpoint bddEOjectList_getBDD (bddEObjects : list bddMetamodel_EObject) : option BDD :=
    match bddEObjects with 
    | nil => None
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject BDDEClass obj => Some obj
        | _ => bddEOjectList_getBDD tail
        end
    end
.

Fixpoint bddEOjectList_getPorts (bddEObjects : list bddMetamodel_EObject) : list Port :=
    match bddEObjects with 
    | nil => nil
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject PortEClass obj => obj::(bddEOjectList_getPorts tail)
        | _ => bddEOjectList_getPorts tail
        end
    end
.

Fixpoint bddEOjectList_getSubtreesFromInputPortName (bddEObjects : list bddMetamodel_EObject) (inputPortName : string) : list Subtree :=
    match bddEObjects with 
    | nil => nil
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject TreeEClass (Build_Abstract_Tree SubtreeEClass obj) => 
            match obj with 
            | BuildSubtree subtreeName =>
                match eqb (lastChar subtreeName) inputPortName with 
                | true => obj::(bddEOjectList_getSubtreesFromInputPortName tail inputPortName)
                | false => bddEOjectList_getSubtreesFromInputPortName tail inputPortName
                end
            end
        | _ => bddEOjectList_getSubtreesFromInputPortName tail inputPortName
        end
    end
.

Fixpoint InputPortSubtreesELinks (bddEObjects : list bddMetamodel_EObject) : list bddMetamodel_ELink :=
    match bddEObjects with 
    | nil => nil
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject PortEClass (Build_Abstract_Port InputPortEClass inputPort) => 
            (Build_bddMetamodel_ELink InputPortSubtreesEReference 
                (BuildInputPortSubtrees
                    inputPort
                    (bddEOjectList_getSubtreesFromInputPortName bddEObjects (InputPort_getName inputPort))
                )
            )::(InputPortSubtreesELinks tail)
        | _ => InputPortSubtreesELinks tail
        end
    end
.

Fixpoint bddEOjectList_getAssignmentsFromInputPortName (bddEObjects : list bddMetamodel_EObject) (outputPortName : string) : list Assignment :=
    match bddEObjects with 
    | nil => nil
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject AssignmentEClass obj => 
            match obj with 
            | BuildAssignment assignmentName _ =>
                match eqb (lastChar assignmentName) outputPortName with 
                | true => obj::(bddEOjectList_getAssignmentsFromInputPortName tail outputPortName)
                | false => bddEOjectList_getAssignmentsFromInputPortName tail outputPortName
                end
            end
        | _ => bddEOjectList_getAssignmentsFromInputPortName tail outputPortName
        end
    end
.

Fixpoint OutputPortAssignmentsELinks (bddEObjects : list bddMetamodel_EObject) : list bddMetamodel_ELink :=
    match bddEObjects with 
    | nil => nil
    | head::tail => 
        match head with
        | Build_bddMetamodel_EObject PortEClass (Build_Abstract_Port OutputPortEClass outputPort) => 
            (Build_bddMetamodel_ELink OutputPortAssignmentsEReference 
                (BuildOutputPortAssignments
                    outputPort
                    (bddEOjectList_getAssignmentsFromInputPortName bddEObjects (OutputPort_getName outputPort))
                )
            )::(OutputPortAssignmentsELinks tail)
        | _ => OutputPortAssignmentsELinks tail
        end
    end
.

Definition bddELinkListFromMyTreeRoot (myTree : MyTree) (bddEObjects : list bddMetamodel_EObject) : list bddMetamodel_ELink := 
    match myTree with
    | MySubtree _ name _ _ =>     
        match bddEOjectList_getBDD bddEObjects with 
        | Some bdd =>
            app
            (
                app
                (
                    (Build_bddMetamodel_ELink BDDPortsEReference 
                        (BuildBDDPorts
                            bdd
                            (bddEOjectList_getPorts bddEObjects)
                        )
                    )
                    ::
                    (map (fun port : Port => (Build_bddMetamodel_ELink PortOwnerEReference (BuildPortOwner port bdd))) (bddEOjectList_getPorts bddEObjects))
                )
                (
                    app 
                    (InputPortSubtreesELinks bddEObjects)
                    (OutputPortAssignmentsELinks bddEObjects)
                )
            )
            (
                (Build_bddMetamodel_ELink BDDTreeEReference 
                    (BuildBDDTree
                        bdd
                        (Build_Abstract_Tree SubtreeEClass (BuildSubtree ("Subtree_"++name)))
                    )
                )
                ::
                (Build_bddMetamodel_ELink TreeOwnerBDDEReference 
                    (BuildTreeOwnerBDD
                        (Build_Abstract_Tree SubtreeEClass (BuildSubtree ("Subtree_"++name)))
                        bdd
                    )
                )
                ::
                (bddELinkListFromMyTree myTree bddEObjects)
            )
        | None => nil
        end
    | MyLeaf _ _ _ => nil
    end
.


Definition TT2BDD (bdd : bddModel) : bddModel :=
    match bdd with 
    | Build_Model bddEObjects bddELinks =>
        (Build_Model
            bddEObjects
            (bddELinkListFromMyTreeRoot (FillMyTreeLeaves (IterInputPorts (
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
                InputModel) bddEObjects)
        )
    end    
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

Eval compute in TT2BDD (TT2BDD_baseobjects InputModel).