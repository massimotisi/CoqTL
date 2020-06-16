Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.

Section Syntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink).

  (** * Abstract Syntax **)

  (** ** Expression Types **)

  Definition outputReferenceTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
    denoteFunction smm (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).

  Definition outputPatternElementTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    denoteFunction smm (sclasses) (denoteModelClass tclass).

  Definition iteratedListTypes
             (sclasses : list SourceModelClass) (itype: Type) :=
    denoteFunction smm (sclasses) (list itype).

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFunction smm (sclasses) bool.

  (** ** Syntax Types **)

  Inductive MatchedOutputPatternElement: Type :=
    BuildMatchedOutputPatternElement :
      string ->
      forall (InElTypes: list SourceModelClass) (IterType: Type)  (OutType:TargetModelClass),
        (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
        MatchedOutputPatternElement.

  Inductive MatchedRule : Type :=
    BuildMatchedRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
          (SourceModel -> (iteratedListTypes InElTypes IterType))
          -> list (MatchedOutputPatternElement)
          -> MatchedRule.

  Inductive MatchedTransformation : Type :=
    BuildMatchedTransformation :
      list MatchedRule ->
      MatchedTransformation.

  Inductive OutputPatternElementReference: Type :=
    BuildOutputPatternElementReference :
      forall (InElTypes: list SourceModelClass) (IterType: Type) (OutType:TargetModelClass) (OutRef: TargetModelReference),
        (MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType OutRef)) ->
        OutputPatternElementReference.

  Inductive OutputPatternElement : Type :=
    BuildOutputPatternElement :
      string ->
      forall (InElTypes: list SourceModelClass) (IterType: Type) (OutType:TargetModelClass),
        (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
        list (OutputPatternElementReference)-> OutputPatternElement.

  Inductive Rule : Type :=
    BuildRule :
      (* name *) string ->
      (* from *) forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        (* for *)  -> forall (IterType: Type),
          (SourceModel -> (iteratedListTypes InElTypes IterType))
          (* to *) -> list OutputPatternElement
          -> Rule.

  Inductive Transformation : Type :=
    BuildTransformation :
      list Rule ->
      Transformation.

  (** ** Accessors **)

  Definition OutputPatternElementReference_getInElTypes (o: OutputPatternElementReference) : list SourceModelClass :=
    match o with BuildOutputPatternElementReference y _ _ _ _ => y end.

  Definition OutputPatternElementReference_getIterType (o: OutputPatternElementReference) : Type :=
    match o with BuildOutputPatternElementReference _ y _ _ _ => y end.

  Definition OutputPatternElementReference_getOutType (o: OutputPatternElementReference) : TargetModelClass :=
    match o with BuildOutputPatternElementReference _ _ y _ _ => y end.

  Definition OutputPatternElementReference_getRefType (o: OutputPatternElementReference) : TargetModelReference :=
    match o with BuildOutputPatternElementReference _ _ _ y _ => y end.
 
  Definition OutputPatternElementReference_getOutputReference (o: OutputPatternElementReference) :
    MatchedTransformation -> (OutputPatternElementReference_getIterType o) -> SourceModel -> (outputReferenceTypes (OutputPatternElementReference_getInElTypes o) (OutputPatternElementReference_getOutType o) (OutputPatternElementReference_getRefType o)):=
    match o with BuildOutputPatternElementReference _ _ _ _ y => y end.

  Definition OutputPatternElement_getName (o: OutputPatternElement) : string :=
    match o with BuildOutputPatternElement y _ _ _ _ _ => y end.

  Definition OutputPatternElement_getInElTypes (o: OutputPatternElement) : list SourceModelClass :=
    match o with BuildOutputPatternElement _ y _ _ _ _ => y end.

  Definition OutputPatternElement_getIterType (o: OutputPatternElement) : Type :=
    match o with BuildOutputPatternElement _ _ y _ _ _ => y end.

  Definition OutputPatternElement_getOutType (o: OutputPatternElement) : TargetModelClass :=
    match o with BuildOutputPatternElement _ _ _ y _ _ => y end.

  Definition OutputPatternElement_getOutputElementReferences (o: OutputPatternElement) :
    list OutputPatternElementReference :=
    match o with BuildOutputPatternElement _ _ _ _ _ y => y end.

  Definition OutputPatternElement_getOutPatternElement (o: OutputPatternElement) :
    (OutputPatternElement_getIterType o) -> SourceModel -> (outputPatternElementTypes (OutputPatternElement_getInElTypes o) (OutputPatternElement_getOutType o)) :=
    match o with BuildOutputPatternElement _ _ _ _ y _ => y end.

  Definition Rule_getName (x : Rule) : string :=
    match x with BuildRule y _ _ _ _ _ => y end.

  Definition Rule_getInTypes (x : Rule) : list SourceModelClass :=
    match x with BuildRule _ y _ _ _ _ => y end.

  Definition Rule_getGuard (x : Rule) :
    SourceModel -> (guardTypes (Rule_getInTypes x)):=
    match x with BuildRule _ _ y _ _ _ => y end.

  Definition Rule_getIteratorType (x : Rule) : Type :=
    match x with BuildRule _ _ _ y _ _ => y end.

  Definition Rule_getIteratedList (x: Rule) :
    SourceModel -> (iteratedListTypes (Rule_getInTypes x) (Rule_getIteratorType x)) :=
    match x with BuildRule _ _ _ _ y _ => y end.

  Definition Rule_getOutputPattern (x : Rule) :
    list OutputPatternElement :=
    match x with BuildRule _ _ _ _ _ y => y end.

  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.

  Definition MatchedOutputPatternElement_getName (o: MatchedOutputPatternElement) : string :=
    match o with BuildMatchedOutputPatternElement y _ _ _ _ => y end.

  Definition MatchedOutputPatternElement_getInElTypes (o: MatchedOutputPatternElement) : list SourceModelClass :=
    match o with BuildMatchedOutputPatternElement _ y _ _ _ => y end.

  Definition MatchedOutputPatternElement_getIterType (o: MatchedOutputPatternElement) : Type :=
    match o with BuildMatchedOutputPatternElement _ _ y _ _ => y end.

  Definition MatchedOutputPatternElement_getOutType (o: MatchedOutputPatternElement) : TargetModelClass :=
    match o with BuildMatchedOutputPatternElement _ _ _ y _ => y end.

  Definition MatchedOutputPatternElement_getOutPatternElement (o: MatchedOutputPatternElement) :
    (MatchedOutputPatternElement_getIterType o) -> SourceModel -> (outputPatternElementTypes (MatchedOutputPatternElement_getInElTypes o) (MatchedOutputPatternElement_getOutType o)) :=
    match o with BuildMatchedOutputPatternElement _ _ _ _ y => y end.

  Definition MatchedRule_getName (x : MatchedRule) : string :=
    match x with BuildMatchedRule y _ _ _ _ _ => y end.

  Definition MatchedRule_getInTypes (x : MatchedRule) : list SourceModelClass :=
    match x with BuildMatchedRule _ y _ _ _ _ => y end.

  Definition MatchedRule_getGuard (x : MatchedRule) :
    SourceModel -> (guardTypes (MatchedRule_getInTypes x)):=
    match x with BuildMatchedRule _ _ y _ _ _ => y end.

  Definition MatchedRule_getIteratorType (x : MatchedRule) : Type :=
    match x with BuildMatchedRule _ _ _ y _ _ => y end.

  Definition MatchedRule_getIteratedList (x: MatchedRule) :
    SourceModel -> (iteratedListTypes (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)) :=
    match x with BuildMatchedRule _ _ _ _ y _ => y end.

  Definition MatchedRule_getOutputPattern (x : MatchedRule) :
    list MatchedOutputPatternElement :=
    match x with BuildMatchedRule _ _ _ _ _ y => y end.

  Definition MatchedTransformation_getRules (x : MatchedTransformation) : list MatchedRule :=
    match x with BuildMatchedTransformation y => y end.

  (** ** Copying Matched Transformation *)

  Definition matchOutputPatternElement (x: OutputPatternElement)
    : MatchedOutputPatternElement :=
    match x with
    | BuildOutputPatternElement a b c d e f => BuildMatchedOutputPatternElement a b c d e
    end.

  Definition matchRule (x: Rule) : MatchedRule :=
    match x with
    | BuildRule a b c d e f => BuildMatchedRule a b c d e (map matchOutputPatternElement f)
    end.

  Definition matchTransformation (x: Transformation) : MatchedTransformation :=
    match x with
    | BuildTransformation a => BuildMatchedTransformation (map matchRule a)
    end.

  Definition unmatchOutputPatternElement (x: MatchedOutputPatternElement)
    : OutputPatternElement :=
    match x with
    | BuildMatchedOutputPatternElement a b c d e => BuildOutputPatternElement a b c d e nil
    end.

  Definition unmatchRule (x: MatchedRule) : Rule :=
    match x with
    | BuildMatchedRule a b c d e f => BuildRule a b c d e (map unmatchOutputPatternElement f)
    end.

  Definition unmatchTransformation (x: MatchedTransformation) : Transformation :=
    match x with
    | BuildMatchedTransformation a => BuildTransformation (map unmatchRule a)
    end.

  (** ** Utilities *)

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
    find (fun(o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
         (Rule_getOutputPattern r).

End Syntax.

Arguments BuildTransformation {_ _ _ _} _ {_ _ _ _} _ _.
Arguments MatchedTransformation {_ _ _ _} _ {_ _ _ _} _.

Arguments BuildRule {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _.

Arguments BuildOutputPatternElement {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _.

Arguments BuildOutputPatternElementReference {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _.
