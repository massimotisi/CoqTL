Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import DecimalNat.
Require Import DecimalString.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.tTop.
Require Import core.utils.tArith.
Require Import core.utils.CpdtTactics.


Set Implicit Arguments.

Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.
  
  About SourceModel.

  (** * Concrete Syntax

  Example: 
        rule Attribute2Column
        from                    -- InputPatternElement
          a : Attribute         -- Element Definition
            a.name = "father"     -- Guard
        to [                    -- OutputPatternElement
          output "t":           -- elem_id
            c : Column          -- elem_name : elem_type
              t.name <- a.name
              t.id   <- a.id
          references:           -- ref_def
            Column * Table      -- ref_type   
            M                   -- trg_instance -> help resolving
            :=                  -- ref_ends -> specify how to construct ref_def
            y' <- a.class;
            y <- resolve(a.class);
            BuildRef c y
         ]
   **)

  (** ** OutputPatternElementReference **)

  (* Build OutputPatternElementReference with :
      an ref_type
      an trg_instance
      and a ref_ends         
   *)
  Inductive OutputPatternElementReference : Type :=
  | BuildOutputPatternElementReference : forall (OutRefs: TargetModelReference),
      (option (denoteModelReference OutRefs))
      -> OutputPatternElementReference.

  Definition OutputPatternElementReferenceType (o :  OutputPatternElementReference) : TargetModelReference :=
    match o with BuildOutputPatternElementReference type link => type end.
                                                                                       
  Definition OutputPatternElementReferenceLink (o :  OutputPatternElementReference) : option TargetModelLink :=
    match o with
      (BuildOutputPatternElementReference type link) =>
      ml <- link;
      return toModelLink type ml
    end.
  
  Fixpoint getOutputPatternElementReferenceTargetModelLinks (l : list OutputPatternElementReference) : list TargetModelLink :=
    match l with
    | nil => nil
    | ope :: opel => match ope with
                    | BuildOutputPatternElementReference OutRefs x =>
                      match x with
                      | Some x => BuildModelLink OutRefs x :: getOutputPatternElementReferenceTargetModelLinks opel
                      | None => getOutputPatternElementReferenceTargetModelLinks opel
                      end
                    end
    end.

  (** ** OutputPatternElement **)

  (* Build OutputPatternElement with :
      an elem_type
      an elem_id
      an elem_def
      and a (elem_name->ref_def)
   *)
  Inductive OutputPatternElement : Type :=
  | BuildOutputPatternElement : forall (OutElType: TargetModelClass),
      string
      -> (denoteModelClass OutElType)
      -> ((denoteModelClass OutElType) -> list OutputPatternElementReference)
      -> OutputPatternElement.
  
  Definition getOutputPatternElementName (o :  OutputPatternElement) : string :=
    match o with BuildOutputPatternElement type name el refs => name end.

  Definition getOutputPatternElementType (o :  OutputPatternElement) : TargetModelClass :=
    match o with BuildOutputPatternElement type name el refs => type end.

  Definition getOutputPatternElementBindings (o :  OutputPatternElement) : ((denoteModelClass (getOutputPatternElementType o)) -> list OutputPatternElementReference) :=
    match o with BuildOutputPatternElement type name el refs => refs end.

  Definition getOutputPatternElementElementType (o :  OutputPatternElement) : Set :=
    match o with BuildOutputPatternElement type name el refs => denoteModelClass type end.

  Definition getOutputPatternElementElement (o :  OutputPatternElement) : getOutputPatternElementElementType o :=
    match o with BuildOutputPatternElement type name el refs => el end.
  
  Definition getOutputPatternElementTargetModelElement (o :  OutputPatternElement) : TargetModelElement :=
    match o with BuildOutputPatternElement OutElType x x0 x1 => toModelElement OutElType x0 end.

  Definition getOutputPatternElementTargetModelLinks (o :  OutputPatternElement): list TargetModelLink :=
    match o with BuildOutputPatternElement type name el refs => getOutputPatternElementReferenceTargetModelLinks (refs el) end.

  Definition getOutputPatternElementElementByType (o :  OutputPatternElement) (type: TargetModelClass) : option (denoteModelClass type).
  Proof.
    remember o as ope.
    destruct o.
    remember (eqModelClass_dec type OutElType) as equal.
    destruct equal.
    - rewrite e.
      exact (Some d).
    - exact None.
  Defined.

  Inductive Rule: Type :=
  | BuildMultiElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> Rule)
        -> Rule
  | BuildSingleElementRule :
      forall (InElType: SourceModelClass) (A: Type),
        ((denoteModelClass InElType) -> (bool * list A))
        -> ((denoteModelClass InElType) -> option A -> list OutputPatternElement)
        -> Rule.
  
  Definition Phase : Type := SourceModel -> list (string * Rule).

  Definition Transformation : Type := Phase -> Phase.

  (** * Abstract Syntax **)

  Inductive OutputBindingExpressionA : Type :=
      BuildOutputBindingExpressionA :
        nat ->
        nat ->
        nat ->
        OutputBindingExpressionA.

  Definition OutputBindingExpressionA_getRule (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA y _ _ => y end.
  
  Definition OutputBindingExpressionA_getOutputPatternElement (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA _ y _ => y end.

  Definition OutputBindingExpressionA_getOutputBinding (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA _ _ y => y end.
  
  Inductive OutputPatternElementReferenceA : Type :=
      BuildOutputPatternElementReferenceA :
        TargetModelReference ->
        OutputBindingExpressionA -> 
        OutputPatternElementReferenceA.

  Definition OutputPatternElementReferenceA_getType (x : OutputPatternElementReferenceA) : TargetModelReference :=
    match x with BuildOutputPatternElementReferenceA y _ => y end. 
  
  Definition OutputPatternElementReferenceA_getOutputBindingExpression (x : OutputPatternElementReferenceA) : OutputBindingExpressionA :=
    match x with BuildOutputPatternElementReferenceA _ y => y end. 

  Inductive OutputPatternElementExpressionA : Type :=
    BuildOutputPatternElementExpressionA :
      nat ->
      nat ->
      OutputPatternElementExpressionA.

  Lemma OutputPatternElementExpressionA_dec : 
    forall (x1: OutputPatternElementExpressionA) (x2: OutputPatternElementExpressionA), { x1 = x2 } + { x1 <> x2 }.
  Proof. repeat decide equality. Defined.

  Definition OutputPatternElementExpressionA_equals (x1: OutputPatternElementExpressionA) (x2: OutputPatternElementExpressionA) : bool :=
    if OutputPatternElementExpressionA_dec x1 x2 then true else false.

  Definition OutputPatternElementExpressionA_getRule (x : OutputPatternElementExpressionA) : nat :=
    match x with BuildOutputPatternElementExpressionA y _ => y end.

  Definition OutputPatternElementExpressionA_getOutputPatternElement (x : OutputPatternElementExpressionA) : nat :=
    match x with BuildOutputPatternElementExpressionA _ y => y end.
  
  Inductive OutputPatternElementA : Type := 
    BuildOutputPatternElementA :
      string ->
      TargetModelClass ->
      OutputPatternElementExpressionA ->
      list OutputPatternElementReferenceA -> OutputPatternElementA.

  Definition OutputPatternElementA_getName (x : OutputPatternElementA) : string :=
    match x with BuildOutputPatternElementA y _ _ _  => y end.

  Definition OutputPatternElementA_getType (x : OutputPatternElementA) : TargetModelClass :=
    match x with BuildOutputPatternElementA _ y _ _  => y end.

  Definition OutputPatternElementA_getOutputPatternElementExpression (x : OutputPatternElementA) : OutputPatternElementExpressionA :=
    match x with BuildOutputPatternElementA _ _ y _  => y end.

  Definition OutputPatternElementA_getOutputPatternElementReferences (x : OutputPatternElementA) : list OutputPatternElementReferenceA :=
    match x with BuildOutputPatternElementA _ _ _ y  => y end.

  Inductive GuardExpressionA : Type :=
    BuildGuardExpressionA :
      nat ->
      GuardExpressionA.

  Definition GuardExpressionA_getRule (x : GuardExpressionA) : nat :=
    match x with BuildGuardExpressionA y => y end.

  (* TODO: evaluate if it's better to have derived accessors

    GuardExpressionA_getRuleA : option RuleA :=
    (nth_error (TransformationA_getRules tr) (GuardExpressionA_getRule o));
      
  GuardExpressionA_getRule : option Rule := *)

  Inductive ForExpressionA : Type :=
    BuildForExpressionA :
      nat ->
      ForExpressionA.

  Definition ForExpressionA_getRule (x : ForExpressionA) : nat :=
    match x with BuildForExpressionA y => y end.
  
  Inductive RuleA : Type := 
    BuildRuleA :
      string ->
      list SourceModelClass ->
      GuardExpressionA ->
      ForExpressionA ->
      list OutputPatternElementA -> RuleA.

  Definition RuleA_getName (x : RuleA) : string :=
    match x with BuildRuleA y _ _ _ _ => y end.

  Definition RuleA_getInTypes (x : RuleA) : list SourceModelClass :=
    match x with BuildRuleA _ y _ _ _ => y end.

  Definition RuleA_getGuard (x : RuleA) : GuardExpressionA :=
    match x with BuildRuleA _ _ y _ _ => y end.

  Definition RuleA_getOutputPattern (x : RuleA) : list OutputPatternElementA :=
    match x with BuildRuleA _ _ _ _ y => y end.

  Definition RuleA_getForExpression (x : RuleA) : ForExpressionA :=
    match x with BuildRuleA _ _ _ y _ => y end.
  
  Inductive TransformationA : Type := 
    BuildTransformationA :
      list RuleA ->
      Transformation ->
      TransformationA.

  Definition TransformationA_getTransformation (x : TransformationA) : Transformation :=
    match x with BuildTransformationA _ y => y end.

  Definition TransformationA_getRules (x : TransformationA) : list RuleA :=
    match x with BuildTransformationA y _ => y end.

  Definition OutputPatternElementExpressionA_getRuleA (x : OutputPatternElementExpressionA) (tr: TransformationA) : option RuleA :=
    find (fun r:RuleA =>
            match find (OutputPatternElementExpressionA_equals x) (map OutputPatternElementA_getOutputPatternElementExpression (RuleA_getOutputPattern r)) with
            | Some _ => true
            | None => false
            end)
         (TransformationA_getRules tr).

  (** * Parser **)
  
  Definition parseOutputPatternElementReference (tr: Transformation) (r ope oper: nat) (o: OutputPatternElementReference) : OutputPatternElementReferenceA :=   
    match o with
    | BuildOutputPatternElementReference t _ =>
      BuildOutputPatternElementReferenceA t (BuildOutputBindingExpressionA r ope oper)
    end.

  Definition parseOutputPatternElement (tr: Transformation) (r ope: nat) (o: OutputPatternElement) : OutputPatternElementA :=   
    match o with
    | BuildOutputPatternElement t n _ f =>
      BuildOutputPatternElementA n t (BuildOutputPatternElementExpressionA r ope) (mapWithIndex (parseOutputPatternElementReference tr r ope) 0 (f (bottomModelClass t)))
    end.

  Fixpoint parseRuleOutput (tr: Transformation) (n: nat) (r: Rule) : list OutputPatternElementA :=
    match r with
    | BuildMultiElementRule iet f => parseRuleOutput tr n (f (bottomModelClass iet)) 
    | BuildSingleElementRule iet f g => mapWithIndex (parseOutputPatternElement tr n) 0 (g (bottomModelClass iet) None) 
    end.    
  
  Fixpoint parseRuleTypes (r: Rule) : list SourceModelClass :=
    match r with
    | BuildMultiElementRule iet f => (cons iet (parseRuleTypes (f (bottomModelClass iet))))
    | BuildSingleElementRule iet f g => iet::nil
    end.

  Definition parseRuleDeclaration (tr: Transformation) (n: nat) (r: (string * Rule)) : RuleA :=
    (BuildRuleA (fst r) (parseRuleTypes (snd r)) (BuildGuardExpressionA n) (BuildForExpressionA n)) (parseRuleOutput tr n (snd r)).
  
  Definition parseTransformation (tr: Transformation) : TransformationA :=
    BuildTransformationA 
      (mapWithIndex (parseRuleDeclaration tr) 0 (tr (fun c:SourceModel => nil) (Build_Model nil nil) )) tr.

  Definition parsePhase (tr: Phase) : TransformationA :=
    parseTransformation (fun t: Phase => tr).

  (** * Expression Evaluation **)
  (* API for the expression language evaluator (Gallina) *)

  Fixpoint Rule_getSingleElementRule (r: Rule) (sp: list SourceModelElement) : option (Rule * SourceModelElement) :=
    match r, sp with
    | BuildMultiElementRule s f, e::els => 
      match toModelClass s e with
      | Some e' => Rule_getSingleElementRule (f e') els
      | None => None
      end
    | BuildSingleElementRule s f g as bser, e::nil =>
      match toModelClass s e with
      | Some e' => Some (bser, e)
      | None => None
      end
    | _, _ => None
    end.
  
  (* TODO: move to the engine part *)
  (* Before evaluate guard, pre-check the intypes of rule and source elems length are equal. immediate stop eval if not. *)
  Definition evalGuardExpressionPre (r: RuleA) (sp: list SourceModelElement) : option bool :=
    let lenInTypes := (length (RuleA_getInTypes r)) in
      let lenSp := (length sp) in
        match beq_nat lenInTypes lenSp with
         | true => Some true 
         | false => None
        end.

  (* TODO: use Rule_getSingleElementRule *)
  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalGuardExpressionFix (r : Rule) (intypes: list SourceModelClass) (el: list SourceModelElement) : option bool :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalGuardExpressionFix (f e') ts els
    | BuildSingleElementRule s f g, t::nil, e::nil =>
      e' <- toModelClass s e;
      return (fst (f e'))
    | _, _, _ => None
    end.

  Definition evalGuardExpression (o : GuardExpressionA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (GuardExpressionA_getRule o));
      ra <- (nth_error (TransformationA_getRules tr) (GuardExpressionA_getRule o));
      evalGuardExpressionFix (snd r) (RuleA_getInTypes ra) sp.
  
  Definition Rule_getForSectionType (r: Rule) (sp: list SourceModelElement) : Type :=
    match Rule_getSingleElementRule r sp with
    | Some (@BuildSingleElementRule iet ft f g, e) => ft
    | _ => Error
    end.
  
  Definition ForExpressionA_getForSectionType (o : ForExpressionA) (tr: TransformationA) (sm: SourceModel)  (sp: list SourceModelElement)  : Type :=
    match (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (ForExpressionA_getRule o)) with
    | None => Error
    | Some r => Rule_getForSectionType (snd r) sp
    end.


  Definition evalForExpression' (r : Rule) (sp: list SourceModelElement) :
    option (list (Rule_getForSectionType r sp)).
  Proof.
    destruct (Rule_getSingleElementRule r sp) eqn:rc.
    2: { exact None. }
    1: { destruct (fst p) eqn:m.
         2: { destruct (toModelClass InElType (snd p)) eqn: ser.
              2: { exact None. }
              1: { unfold Rule_getForSectionType.
                   rewrite rc.
                   rewrite surjective_pairing_transparent with (p:=p).
                   rewrite m.
                   exact (return (snd (p0 d))). }}
         1: { exact None. }}
  Defined.
  
  Definition evalForExpression (fe : ForExpressionA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option (list (ForExpressionA_getForSectionType fe tr sm sp)).
  Proof.
    destruct (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (ForExpressionA_getRule fe)) eqn:nth_r.
    - destruct (nth_error (TransformationA_getRules tr) (ForExpressionA_getRule fe)) eqn:nth_ra.
      + remember (evalForExpression' (snd p) sp) as ret.
        unfold ForExpressionA_getForSectionType.
        rewrite nth_r.
        exact (ret). 
      + exact None.
    - exact None.
  Defined.

  Definition evalOutputPatternElementExpression' (o : OutputPatternElementExpressionA) (tr: TransformationA) (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option TargetModelElement :=
    match Rule_getSingleElementRule r sp with
    | Some (@BuildSingleElementRule s ft f g, e) =>
      e' <- toModelClass s e;
        ope <- (nth_error (g e' None) (OutputPatternElementExpressionA_getOutputPatternElement o));
        return (getOutputPatternElementTargetModelElement ope)
    | _ => None
    end.

  (* TODO checking the order of arguments *)
  Definition evalOutputPatternElementExpression (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (o : OutputPatternElementExpressionA): option TargetModelElement :=
    r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o));
      evalOutputPatternElementExpression' o tr (snd r) sm sp.

  Definition OutputPatternElementExpressionA_getForSectionType (o : OutputPatternElementExpressionA) (tr: TransformationA) (sm: SourceModel)  (sp: list SourceModelElement)  : Type :=
    match (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o)) with
    | None => Error
    | Some r => Rule_getForSectionType (snd r) sp
    end.
  
  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Definition evalOutputPatternElementExpressionWithIter' (o : OutputPatternElementExpressionA) (tr: TransformationA) (r : Rule)
           (sm: SourceModel) (sp: list SourceModelElement) (fet: OutputPatternElementExpressionA_getForSectionType o tr sm sp) : option TargetModelElement.
  Proof.
  destruct (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o)) eqn: find_r_ca.
  2 : { exact None. }
  1 : { unfold OutputPatternElementExpressionA_getForSectionType in fet. 
        rewrite  find_r_ca in fet.
        unfold Rule_getForSectionType in fet.
        destruct (Rule_getSingleElementRule (snd p) sp) eqn: rc_ca.
        2 : { exact None. }
        1 : { destruct (fst p0) eqn:r_ca.
              2: { rewrite surjective_pairing_transparent with (p:=p0) in fet. 
                   rewrite r_ca in fet.
                   destruct (toModelClass InElType (snd p0)) eqn: m_ca.
                   2 : { exact None. } 
                   1 : { pose (l d (Some fet)) as outputPatternElements. 
                         destruct (nth_error outputPatternElements (OutputPatternElementExpressionA_getOutputPatternElement o)) eqn: f_ca.
                          2 : { exact None. } 
                          1 : { exact (Some (getOutputPatternElementTargetModelElement o0)). }
                   }
                 }
              1: { exact None. }
            }
  }
  Defined.

  Definition evalOutputPatternElementExpressionWithIter (o : OutputPatternElementExpressionA)  (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) 
         (fet: OutputPatternElementExpressionA_getForSectionType o tr sm sp) : option TargetModelElement :=
      r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o));
        evalOutputPatternElementExpressionWithIter' o tr (snd r) sm sp fet.

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Definition evalOutputBindingExpression' (o : OutputBindingExpressionA) (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) 
   (te: TargetModelElement) : option TargetModelLink :=
    match Rule_getSingleElementRule r sp with
    | Some (@BuildSingleElementRule s ft f g, e) =>
        e' <- toModelClass s e;
        ope <- (nth_error (g e' None) (OutputBindingExpressionA_getOutputPatternElement o));
        te' <- toModelClass (getOutputPatternElementType ope) te;
        oper <- (nth_error ((getOutputPatternElementBindings ope) te') (OutputBindingExpressionA_getOutputBinding o));
        (OutputPatternElementReferenceLink oper)
    | _ => None
    end.

  Definition evalOutputBindingExpression (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) (o : OutputBindingExpressionA) : option TargetModelLink :=
    r <- (nth_error ((TransformationA_getTransformation tr) ((TransformationA_getTransformation tr) (fun c:SourceModel => nil)) sm) (OutputBindingExpressionA_getRule o));
      evalOutputBindingExpression' o (snd r) sm sp te. 

  Definition OutputBindingExpressionA_getForSectionType (o : OutputBindingExpressionA) (tr: TransformationA) (sm: SourceModel)  (sp: list SourceModelElement)  : Type :=
    match (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputBindingExpressionA_getRule o)) with
    | None => Error
    | Some r => Rule_getForSectionType (snd r) sp
    end.

  Definition evalOutputBindingExpressionWithIter' (o : OutputBindingExpressionA) (tr: TransformationA) (r : Rule) (sm: SourceModel) 
    (sp: list SourceModelElement) (te: TargetModelElement) (fet: OutputBindingExpressionA_getForSectionType o tr sm sp) 
      : option TargetModelLink.
  Proof.
    destruct (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputBindingExpressionA_getRule o)) eqn: find_r_ca.
    2 : { exact None. }
    1 : { unfold OutputBindingExpressionA_getForSectionType in fet. 
          rewrite  find_r_ca in fet.
          unfold Rule_getForSectionType in fet.
          destruct (Rule_getSingleElementRule (snd p) sp) eqn: rc_ca.
          2 : { exact None. }
          1 : { destruct (fst p0) eqn:r_ca.
                2: { rewrite surjective_pairing_transparent with (p:=p0) in fet. 
                     rewrite r_ca in fet.
                     destruct (toModelClass InElType (snd p0)) eqn: m_ca.
                     2 : { exact None. } 
                     1 : { pose (l d (Some fet)) as outputPatternElements. 
                           destruct (nth_error outputPatternElements (OutputBindingExpressionA_getOutputPatternElement o)) eqn: f_ca.
                           2 : { exact None. } 
                           1 : { destruct (toModelClass (getOutputPatternElementType o0) te) eqn: te_ca.
                                 2 : { exact None. } 
                                 1 : { destruct (nth_error ((getOutputPatternElementBindings o0) d0) (OutputBindingExpressionA_getOutputBinding o)) eqn: refs_ca.
                                       2 : { exact None. } 
                                       1 : { exact (OutputPatternElementReferenceLink o1). } 
                                 }
                           }
                     }
                }
                1: { exact None. }
          }
    }
  Defined.

  Definition evalOutputBindingExpressionWithIter (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) (o : OutputBindingExpressionA) 
    (fet: OutputBindingExpressionA_getForSectionType o tr sm sp) : option TargetModelLink :=
    r <- (nth_error ((TransformationA_getTransformation tr) ((TransformationA_getTransformation tr) (fun c:SourceModel => nil)) sm) (OutputBindingExpressionA_getRule o));
      ra <- (nth_error (TransformationA_getRules tr) (OutputBindingExpressionA_getRule o));
      evalOutputBindingExpressionWithIter' o tr (snd r) sm sp te fet. 

  (** * Engine **)

  (** ** Rule application **)

  Inductive ModelFragment (ModelElement: Type) (ModelLink: Type): Type :=
    BuildModelFragment: list ModelElement -> list ModelLink -> ModelFragment ModelElement ModelLink.

  Fixpoint getSourcePatternId (sp: list SourceModelElement) : string :=
    match sp with
    | se :: ses => (getId se) ++ "_" ++ (getSourcePatternId ses)
    | _ => "_"
    end.

  Definition newId := ""%string.

  (*TODO*)
  Definition setTargetElementId (te: TargetModelElement) (ope: OutputPatternElementA) (sp: list SourceModelElement) : TargetModelElement :=
    if (beq_string (getId te) newId) then
      match (OutputPatternElementA_getOutputPatternElementExpression ope) with
        BuildOutputPatternElementExpressionA a b => 
      setId te  ((getSourcePatternId sp) ++
                      NilZero.string_of_uint (Unsigned.to_lu a) ++ "_" ++
                      NilZero.string_of_uint (Unsigned.to_lu b))%string
            end
    else te.

  Definition ForExpressionA_getForSectionType2OutputPatternElementExpressionA 
    (f : ForExpressionA) (o : OutputPatternElementExpressionA) (tr: TransformationA) (sp: list SourceModelElement) 
    (sm: SourceModel)  (fe: ForExpressionA_getForSectionType f tr sm sp) 
      : option (OutputPatternElementExpressionA_getForSectionType o tr sm sp).
  Proof.
    destruct (beq_nat (OutputPatternElementExpressionA_getRule o)
                      (ForExpressionA_getRule f)) eqn: ca.
    - unfold ForExpressionA_getForSectionType in fe.
      symmetry in ca.
      apply beq_nat_eq in ca.
      rewrite <- ca in fe.
      exact (Some fe).
    - exact None.
  Defined.

  Definition instantiateRuleOnPattern' (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (ope: OutputPatternElementA) 
    (fe: ForExpressionA_getForSectionType (RuleA_getForExpression r) tr sm sp) : option (TargetModelElement) :=
   let  opee := (OutputPatternElementA_getOutputPatternElementExpression ope) in 
   tfe <- ForExpressionA_getForSectionType2OutputPatternElementExpressionA (RuleA_getForExpression r) opee tr sp sm fe;
   tme <- (evalOutputPatternElementExpressionWithIter opee tr sm sp tfe);
   return (setTargetElementId tme ope sp).


  Definition instantiateRuleOnPattern (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    pre <- evalGuardExpressionPre r sp;
      m <- evalGuardExpression (RuleA_getGuard r) tr sm sp;
      if m then 
        match (optionListToList (evalForExpression (RuleA_getForExpression r) tr sm sp)) with
         | nil => Some nil
         | lst => return (optionList2List (flat_map (fun ope => map (instantiateRuleOnPattern' r tr sm sp ope) lst)
                                                    (RuleA_getOutputPattern r)))
        end
      else
        None.

  Definition applyOutputPatternReferencesOnPattern (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (l: list OutputPatternElementReferenceA) (te: TargetModelElement) : list TargetModelLink :=
  optionList2List (map (evalOutputBindingExpression tr sm sp te) (map OutputPatternElementReferenceA_getOutputBindingExpression l)).


  Definition ForExpressionA_getForSectionType2OutputBindingExpressionA_getForSectionType 
    (f : ForExpressionA) (o : OutputBindingExpressionA) (tr: TransformationA) (sp: list SourceModelElement) 
    (sm: SourceModel)  (fe: ForExpressionA_getForSectionType f tr sm sp) 
      : option (OutputBindingExpressionA_getForSectionType o tr sm sp).
  Proof.
    destruct (beq_nat (OutputBindingExpressionA_getRule o)
                         (ForExpressionA_getRule f)) eqn: ca.
    - unfold ForExpressionA_getForSectionType in fe.
      symmetry in ca. 
      apply beq_nat_eq in ca.
      rewrite <- ca in fe.
      exact (Some fe).
    - exact None.
  Defined.

  Definition applyOutputPatternReferencesOnPatternIter (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) 
   (fe: ForExpressionA_getForSectionType (RuleA_getForExpression r) tr sm sp) (orefs: list OutputPatternElementReferenceA) (te: TargetModelElement) 
     : list (option TargetModelLink) :=
    let binds := (map OutputPatternElementReferenceA_getOutputBindingExpression orefs) in
map (fun bind => match (ForExpressionA_getForSectionType2OutputBindingExpressionA_getForSectionType (RuleA_getForExpression r) bind tr sp sm fe) with
      | Some tfe => (evalOutputBindingExpressionWithIter tr sm sp te bind tfe)
      | None => None
     end) binds
     .




  Definition applyRuleOnPattern (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (tes: list TargetModelElement): (list TargetModelLink) :=
    match (optionListToList (evalForExpression (RuleA_getForExpression r) tr sm sp)) with
     | nil =>  nil
     | fets => let orefs :=  (flat_map OutputPatternElementA_getOutputPatternElementReferences (RuleA_getOutputPattern r)) in
              optionList2List (concat (flat_map (fun te => (map (fun fe => applyOutputPatternReferencesOnPatternIter r tr sm sp fe orefs te) fets)) tes))
    end.





  (** ** Rule matching **)
  Definition matchRuleOnPattern (r: RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuardExpression (RuleA_getGuard r) tr sm sp.

  Definition matchPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : list RuleA :=
    filter (fun (r:RuleA) =>
            match matchRuleOnPattern r tr sm sp with
            | (Some true) => true
            | _ => false end) (TransformationA_getRules tr).
  
  Definition instantiatePattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (concat (optionList2List (map (fun r => instantiateRuleOnPattern r tr sm sp) l)))
    end.

  Definition applyPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (concat (optionList2List (map (fun r => tes <- instantiateRuleOnPattern r tr sm sp;
                                                      return applyRuleOnPattern r tr sm sp tes
                                             ) l))) end.

  Definition transformPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (ModelFragment TargetModelElement TargetModelLink) :=
      tes <- instantiatePattern tr sm sp;
        tls <- applyPattern tr sm sp;
  return BuildModelFragment tes tls.

  (** ** Resolution **)

  Definition find_OutputPatternElementA (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (name: string): option OutputPatternElementA :=
    find (fun oel => beq_string (OutputPatternElementA_getName oel) name)
              (concat (map RuleA_getOutputPattern (matchPattern tr sm sp))).




  Definition resolveFix (tr: TransformationA) (sm : SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
      ope <- find (fun oel => beq_string (OutputPatternElementA_getName oel) name)
          (concat (map RuleA_getOutputPattern (matchPattern tr sm sp)));
      te <- evalOutputPatternElementExpression tr sm sp (OutputPatternElementA_getOutputPatternElementExpression ope);
      toModelClass type (setTargetElementId te ope sp).

  Definition resolve (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    resolveFix (parsePhase tr) sm name type sp.

  Definition resolveAll (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (sps: list (list SourceModelElement)) : option (list (denoteModelClass type)) :=
    Some (optionList2List (map (resolve tr sm name type) sps)).



  Definition resolveIter (tr: TransformationA) (sm:SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement) 
    (iter : nat) : option (denoteModelClass type) :=
  ope <- (find_OutputPatternElementA tr sm sp name);
  r <- Some (OutputPatternElementExpressionA_getRule (OutputPatternElementA_getOutputPatternElementExpression ope));
  ra <- (nth_error (TransformationA_getRules tr) r);
  fe <- Some (RuleA_getForExpression ra);
  fe_res <- (evalForExpression fe tr sm sp);
  fet <- nth_error fe_res iter;
  let  opee := (OutputPatternElementA_getOutputPatternElementExpression ope) in 
   tfe <- ForExpressionA_getForSectionType2OutputPatternElementExpressionA fe opee tr sp sm fet;
   te<- (evalOutputPatternElementExpressionWithIter (OutputPatternElementA_getOutputPatternElementExpression ope) tr sm sp tfe);
   (toModelClass type (setTargetElementId te ope sp)).



  (** ** Rule scheduling **)
    
  Definition maxArity (tr: TransformationA) : nat :=
    max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))).

  (* Fold-left alternative
     
     Definition maxArity (tr: TransformationA) : nat :=
     fold_left max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))) 0. *)
                                                     
  Definition allTuples (tr: TransformationA) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).
  
  Definition execute (tr: TransformationA) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List (map (instantiatePattern tr sm) (allTuples tr sm))))
      (concat (optionList2List (map (applyPattern tr sm) (allTuples tr sm)))).

  (* One-phase alternative

     Definition pairconcat 
  
     Definition execute (tr: TransformationA) (sm : SourceModel) : TargetModel :=
     let res := (pairconcat (map (transformPattern tr sm) (allTuples tr sm))) in
     Build_Model
      (fst res) (snd res).*)
  
  (** * Typeclass instantiation **)
  
(*  Theorem match_incl :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleA),
          matchPattern tr sm sp = Some r -> In r (TransformationA_getRules tr).
  Proof.
    unfold matchPattern.
    intro tr.
    induction (TransformationA_getRules tr).
    - intros. inversion H.
    - simpl.
      intros sm sp r.
      unfold matchRuleOnPattern.
      destruct (evalGuardExpression (RuleA_getGuard a) tr sm sp).
      * intros.
        destruct b.
        ** left.
           inversion H. 
           auto.
        ** right.
           apply IHl with sm sp.
           auto.
      * intros.
        apply IHl in H.
        right.
        assumption.
  Qed.

  Theorem tr_match_pattern_derivable : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (sp : list SourceModelElement)(r : RuleA),
        matchPattern tr sm sp = return r ->
        matchRuleOnPattern r tr sm sp = return true.
  Proof.
    intros.
    unfold matchPattern in H0.
    apply find_some in H0.
    destruct H0.
    destruct (matchRuleOnPattern r tr sm sp).
    + destruct b.
      * reflexivity.
      * inversion H1.
    + inversion H1.
  Qed.

  Theorem tr_instantiate_pattern_derivable : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (sp : list SourceModelElement) (tp : list TargetModelElement),
        ( exists (r : RuleA),
            instantiateRuleOnPattern r tr sm sp = Some tp /\
            matchPattern tr sm sp = Some r) <->
        instantiatePattern tr sm sp = Some tp.
  Proof.
    intros.
    split.
    - intros.
      unfold instantiatePattern.
      destruct H0.
      destruct H0.
      rewrite H1.
      assumption.
    - intros.
      unfold instantiatePattern in H0.
      destruct (matchPattern tr sm sp) eqn:t.
      + exists r.
        split.
        * assumption.
        * reflexivity.
      + inversion H0.  
  Qed.

  Theorem tr_apply_pattern_derivable : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (sp : list SourceModelElement) (tls : list TargetModelLink),
        (exists (r : RuleA) (tp : list TargetModelElement),
            matchPattern tr sm sp = Some r /\
            instantiateRuleOnPattern r tr sm sp = Some tp /\
            applyRuleOnPattern r tr sm sp tp = Some tls) <->
        applyPattern tr sm sp = Some tls.
  Proof.
    intros.
    split.
    - unfold applyPattern.
      intros.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      rewrite H0.
      rewrite H1.
      assumption.
    - intros.
      unfold applyPattern in H0.
      destruct  (matchPattern tr sm sp) eqn:md.
      + destruct (instantiateRuleOnPattern r tr sm sp) eqn:id.
        * exists r, l.
          split.
          -- reflexivity.
          -- split.
             ++ assumption.
             ++ assumption.
        * inversion H0.
      + inversion H0.
  Qed.

  Theorem tr_surj_elements : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (t1 : TargetModelElement),
        In t1 (allModelElements tm) ->
        (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
            incl sp (allModelElements sm) /\
            In t1 tp /\
            incl tp (allModelElements tm) /\
            instantiatePattern tr sm sp = Some tp).
  Proof.
    intros tr sm tm H0 t1.
    rewrite H0. simpl.
    intros.
    apply concat_map_option_exists in H.
    destruct H. destruct H.
    rename x into sp1.
    remember (matchPattern tr sm sp1) as r'.
    destruct r'.
    
    2: {
      unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction.
    }
    1: {
      remember (instantiatePattern tr sm sp1) as tp_temp.
      destruct tp_temp eqn:tp1_case.
      2: {
        contradiction.
      }
      1: {
        rename l into tp1.
        exists sp1, tp1.
        repeat split.
        - apply tuples_up_to_n_incl with (n:=(maxArity tr)).
          assumption.
        - assumption.
        - apply concat_map_option_incl with (a:=sp1). assumption. symmetry. assumption.
        - symmetry. assumption.
      }
    }
  Qed.
  
  Theorem tr_surj_links : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall  (t1 : TargetModelLink),
        In t1 (allModelLinks tm) ->
        (exists (sp : list SourceModelElement) (tpl : list TargetModelLink),
            incl sp (allModelElements sm) /\
            In t1 tpl /\
            incl tpl (allModelLinks tm) /\
            applyPattern tr sm sp = Some tpl).
  Proof.
    intros tr sm tm H0 t1.
    rewrite H0. simpl.
    intros.
    apply concat_map_option_exists in H.
    destruct H. destruct H.
    rename x into sp1.
    remember (applyPattern tr sm sp1) as r'.
    destruct r'.
      2: {
        contradiction.
      }
      1: {
        unfold applyPattern in Heqr'.
        destruct (matchPattern tr sm sp1) eqn:Hmatch. 
        2: {
          inversion Heqr'.
        }  
        1: {
          destruct (instantiateRuleOnPattern r tr sm sp1) eqn:Hinst.
          2: {
            inversion Heqr'.
          }
          1: {
            rename l0 into te1.
            rename l into tpl.
            exists sp1, tpl. 
            repeat split.
            --- apply tuples_up_to_n_incl with (n:=(maxArity tr)).
                assumption.
            --- assumption.
            --- apply concat_map_option_incl with (a:=sp1). 
                ---- assumption. 
                ---- unfold applyPattern. rewrite Hmatch. rewrite Hinst. symmetry. assumption.
            --- rewrite <- tr_apply_pattern_derivable.
                exists r, te1.
                split.
                +++ assumption.
                +++ split.
                    *** assumption.
                    *** symmetry. assumption.
                +++ apply H0.
          }
        }
      }
  Qed.


  Lemma MaxArity_geq_lenOfrule :
        forall (tr: TransformationA) (r: RuleA),
          In r (TransformationA_getRules tr) -> 
          maxArity tr >= length (RuleA_getInTypes r).
  Proof.
    intros.
    destruct tr.
    simpl in H.
    rename l into rules.
    induction rules.
    - contradiction.
    - simpl in H.
      destruct H.
      + unfold maxArity.
        unfold TransformationA_getRules.
        rewrite H.
        simpl. 
        destruct ((map (Datatypes.length (A:=SourceModelClass)) (map RuleA_getInTypes rules))).
        ++ simpl. omega.
        ++ destruct (ble_nat (Datatypes.length (RuleA_getInTypes r)) (max (n :: l))) eqn:max.
           +++ apply ble_nat_true. assumption.
           +++ omega.
      + apply IHrules in H.
        assert (maxArity (BuildTransformationA (a :: rules) t) >= maxArity (BuildTransformationA rules t)).
        { 
          unfold maxArity.
          unfold TransformationA_getRules.
          simpl. 
          destruct (map (Datatypes.length (A:=SourceModelClass)) (map RuleA_getInTypes rules)) eqn: rules_ca.
          ++ simpl. omega.
          ++ destruct (ble_nat (Datatypes.length (RuleA_getInTypes a)) (max (n :: l))) eqn:max.
             +++ omega.
             +++ apply ble_nat_false in max.
                 omega.
        }
        remember (maxArity (BuildTransformationA (a :: rules) t)) as x.
        remember (maxArity (BuildTransformationA rules t)) as y.
        remember (Datatypes.length (RuleA_getInTypes r)) as z.
        apply (@ge_trans x y z); assumption.
  Qed.

  Lemma eq_ruletype_sp :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
          incl sp (allModelElements sm) ->
          instantiateRuleOnPattern r tr sm sp = Some tp -> length (RuleA_getInTypes r) = Datatypes.length sp.
  Proof.
    intros.
    unfold instantiateRuleOnPattern in H0.
    destruct (evalGuardExpressionPre r sp) eqn: guard; inversion H0.
    unfold evalGuardExpressionPre in guard.
    destruct (Datatypes.length (RuleA_getInTypes r) =? Datatypes.length sp) eqn: ca.
    - apply  beq_nat_true in ca. assumption.
    - inversion guard.
  Qed.

  Lemma InstantiatePattern_le_maxArity :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
      incl sp (allModelElements sm) ->
      In r (TransformationA_getRules tr) ->
      instantiateRuleOnPattern r tr sm sp= Some tp -> maxArity tr >= Datatypes.length sp.
  Proof.
    intros.
    assert (length (RuleA_getInTypes r) = Datatypes.length sp). 
    { apply (@eq_ruletype_sp tr sm sp tp r); assumption. }
    assert ( maxArity tr >= length (RuleA_getInTypes r)). 
    { apply (@MaxArity_geq_lenOfrule). assumption. }
    rewrite H2 in H3.
    assumption.
  Qed.


  Lemma In_allTuples :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
      incl sp (allModelElements sm) ->
      In r (TransformationA_getRules tr) ->
      instantiateRuleOnPattern r tr sm sp = Some tp -> In sp (allTuples tr sm).
  Proof.
    intros.
    case (le_lt_dec (length sp) (maxArity tr)).
    - intros.
      unfold allTuples.
      apply tuples_up_to_n_incl_length.
      + assumption.
      + assumption.
    - intros.
      assert (maxArity tr >= Datatypes.length sp). { apply (@InstantiatePattern_le_maxArity tr sm sp tp r); assumption. }
        omega.
  Qed.

  Theorem outp_incl_elements2 :
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
      (sp : list SourceModelElement) (r: RuleA) (tes: list TargetModelElement),
      tm = execute tr sm -> In r (TransformationA_getRules tr) -> incl sp (allModelElements sm) ->
      matchPattern tr sm sp = Some r ->
      instantiateRuleOnPattern r tr sm sp = Some tes ->
      incl tes (allModelElements tm).
  Proof.
    intros.
    rewrite H.
    simpl.
    apply concat_map_option_incl with (a:=sp).
    - apply In_allTuples with (tp:=tes) (r:=r); assumption.
    - unfold instantiatePattern.
      rewrite H2.
      assumption.
  Qed.

  Theorem outp_incl_elements :
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (sp : list SourceModelElement) (tes: list TargetModelElement),
        incl sp (allModelElements sm) ->
        instantiatePattern tr sm sp = Some tes ->
        incl tes (allModelElements tm).
  Proof.
    intros.
    unfold instantiatePattern in H1.
    destruct (matchPattern tr sm sp) eqn:match_dest.
    * apply outp_incl_elements2 with (tr:=tr) (sm:=sm) (sp:=sp) (r:=r).
      ** crush.
      ** apply match_incl with (sm:=sm) (sp:=sp). crush.
      ** crush.
      ** crush.
      ** crush.
    * crush.
  Qed.

  Theorem outp_incl_links2 :
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
      (sp : list SourceModelElement) (r: RuleA) (tes: list TargetModelElement) (tls: list TargetModelLink),
      tm = execute tr sm -> In r (TransformationA_getRules tr) -> incl sp (allModelElements sm) ->
      matchPattern tr sm sp = Some r ->
      instantiateRuleOnPattern r tr sm sp = Some tes ->
      applyRuleOnPattern r tr sm sp tes = Some tls ->
      incl tls (allModelLinks tm).
  Proof.
    intros.
    rewrite H.
    simpl.
    apply concat_map_option_incl with (a:=sp).
    - apply In_allTuples with (tp:=tes) (r:=r); assumption.
    - unfold applyPattern.
      rewrite H2.
      rewrite H3.
      assumption.
  Qed.

  Theorem outp_incl_links :
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall  (sp : list SourceModelElement) (tls: list TargetModelLink),
        incl sp (allModelElements sm) ->
        applyPattern tr sm sp = Some tls ->
        incl tls (allModelLinks tm).
  Proof.
    intros.
    unfold applyPattern in H1.
    destruct (matchPattern tr sm sp) eqn:match_dest.
    - destruct (instantiateRuleOnPattern r tr sm sp) eqn:inst_dest.
      apply outp_incl_links2 with (tr:=tr) (sm:=sm) (sp:=sp) (r:=r) (tes:=l).
      + crush.
      + apply match_incl with (sm:=sm) (sp:=sp). crush.
      + crush.
      + crush.
      + crush.
      + crush.
      + crush.
    - crush.
  Qed.

  Theorem match_functional :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleA) (r2: RuleA),
      matchPattern tr sm sp = Some r1 -> 
      matchPattern tr sm sp = Some r2 -> 
      r1 = r2.
  Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
  Qed.

  Instance CoqTLEngine : 
    TransformationEngine TransformationA RuleA OutputPatternElementA OutputPatternElementReferenceA SourceModelElement SourceModelLink TargetModelElement TargetModelLink := 
    {
      getRules := TransformationA_getRules;
      getOutputPatternElements := RuleA_getOutputPattern;
      getOutputPatternElementReferences := OutputPatternElementA_getOutputPatternElementReferences;

      execute := execute;
      
      matchPattern := matchPattern;
      instantiatePattern := instantiatePattern;
      applyPattern := applyPattern;

      matchRuleOnPattern := matchRuleOnPattern;
      instantiateRuleOnPattern := instantiateRuleOnPattern;
      applyRuleOnPattern := applyRuleOnPattern;

      match_pattern_derivable :=  tr_match_pattern_derivable; 
      instantiate_pattern_derivable :=  tr_instantiate_pattern_derivable;
      apply_pattern_derivable :=  tr_apply_pattern_derivable; 
      tr_surj_elements := tr_surj_elements;
      tr_surj_links := tr_surj_links;

      outp_incl_elements := outp_incl_elements;
      outp_incl_links := outp_incl_links;
      match_in := match_incl;
      match_functional := match_functional;
    }.
*)  
End CoqTL.



(* Set Implicit Arguments Inference *)

Arguments Phase : default implicits.
Arguments BuildSingleElementRule : default implicits.
Arguments BuildMultiElementRule : default implicits.
Arguments BuildOutputPatternElement : default implicits.
Arguments BuildOutputPatternElementReference : default implicits.
Arguments resolve : default implicits.
Arguments execute : default implicits.
Arguments getOutputPatternElementTargetModelElement : default implicits.