Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.



Theorem Table_name_uniqueness :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (@allModelElements _ _ cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (@allModelElements _ _ rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  apply tr_execute_surj_elements with (te:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [inst].
  destruct H as [Hinsm]. destruct H as [Hintp]. rename H into Hincltp.
  apply tr_instantiatePattern_surj_elements with (te:=t1) (tm:=rm) in inst.
  - { 
      destruct inst as [r]. destruct H as [Hrintr]. destruct H as [Hmatch]. rename H into Hinst.
      destruct sp eqn:sp_ca.
      -- inversion Hmatch.  (* TODO theorem at this point *)
      -- destruct l eqn:l_ca.
         --- apply tr_instantiateRuleOnPattern_surj_elements with (te:=t1) (tm:=rm) in Hinst.  
              ----  destruct Hinst as [Hgpre].
                    destruct H as [Hguard].
                    destruct H as [outexpr].
                    destruct H as [HoutinOuts].
                    destruct H as [Ha].
                    rename H into Heval.
                    unfold evalOutputPatternElement in Heval.
                    crush.  (* TODO check whats going on here *)
                    ----- destruct c eqn: c_ca.
                          destruct c0 eqn: c0_ca.
                          ------- simpl in Heval.
                                  admit.
                          ------- simpl in Heval.
                                  contradiction.
                    ----- destruct c eqn: c_ca.
                          destruct c0 eqn: c0_ca.
                          ------- simpl in Heval.
                                  contradiction.
                          ------- simpl in Heval.
                                  admit.
              ---- admit.
              ---- assumption.
              ---- assumption.
              ---- assumption.
         --- inversion Hmatch.
    }
  - assumption.
  - assumption.
  - assumption.
Admitted.