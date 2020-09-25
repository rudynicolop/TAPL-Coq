Require Import String.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Coq.MSets.MSetDecide.
Module MSD := Coq.MSets.MSetDecide.

(* 
    A Coq formalization of:
    System F/
    The Polymorphic Lambda-Calculus/
    The Second Order Lambda Calculus.
*)

Ltac inv H := inversion H; subst.

Ltac injintrosubst H :=
    injection H; intros; subst.

Definition id := string.

Module IdDec <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Definition t := id.
    Definition eq (x1 x2 : t) := x1 = x2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (x1 x2 : t),
        {x1 = x2} + {x1 <> x2}.
    Proof. intros. apply string_dec. Qed.
    Theorem eq_refl : forall (x : t), x = x.
    Proof. intros. reflexivity. Qed.
    Theorem eq_sym : forall (x y : t), x = y -> y = x.
    Proof. unfold eq. intros; subst; reflexivity. Qed.
    Theorem eq_trans : forall (x y z : t), x = y -> y = z -> x = z.
    Proof. intros; subst. reflexivity. Qed.
End IdDec.

(* variable sets *)
Module IS := WS.Make IdDec.
Module ISF := MSF.WFactsOn IdDec IS.
Module ISD := MSD.WDecideOn IdDec IS.
Module ISDA := ISD.MSetDecideAuxiliary.

Section Syntax.
    Inductive type : Type :=
        | TVar (A : id)
        | TFun (a b : type)
        | TForall (A : id) (t : type).

    (* Free type-variables in a type. *)
    Fixpoint fvt (t : type) : IS.t :=
        match t with
        | TVar A => IS.singleton A
        | TFun a b => IS.union (fvt a) (fvt b)
        | TForall A t => IS.remove A (fvt t)
        end.

    Inductive expr : Type :=
        | EVar (x : id)
        | EFun (x : id) (t : type) (e : expr)
        | EApp (e1 e2 : expr)
        | EForall (A : id) (e : expr)
        | EInst (e : expr) (t : type).

    (* Free type-variables in an expression. *)
    Fixpoint fvte (e : expr) : IS.t :=
        match e with
        | EVar _ => IS.empty
        | EFun _ t e 
        | EInst e t => IS.union (fvt t) (fvte e)
        | EApp e1 e2 => IS.union (fvte e1) (fvte e2)
        | EForall A e => IS.remove A (fvte e)
        end.

    (* Free expression-variables in an expression. *)
    Fixpoint fve (e : expr) : IS.t :=
        match e with
        | EVar x => IS.singleton x
        | EFun x t e => IS.remove x (fve e)
        | EApp e1 e2 => IS.union (fve e1) (fve e2)
        | EForall _ e
        | EInst e _ => fve e
        end.

    Inductive value : expr -> Prop :=
        | value_fun :
            forall (x : id) (t : type) (e : expr),
            value (EFun x t e)
        | value_forall :
            forall (A : id) (e : expr),
            value (EForall A e).
End Syntax.

Module StaticSemantics.
    Section WellFormedness.
        (*
            Pierce omits any discussion of well-formed types.
            I first learned System F from Adrian Sampson,
            who did indeed emphasize well-formedness of types.
            CS 4110 System F Lecture Notes:
                https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture22.pdf
        *)
        Definition delta := list id.

        Inductive WF (d : delta) : type -> Prop := 
            | wf_var : 
                forall (A : id),
                In A d ->
                WF d (TVar A)
            | wf_fun :
                forall (a b : type),
                WF d a -> WF d b ->
                WF d (TFun a b)
            | wf_forall :
                forall (A : id) (t : type),
                WF (A :: d) t ->
                WF d (TForall A t).

        (* Exchange. *)
        Lemma delta_perm :
            forall (d : delta) (t : type),
            WF d t ->
            forall (d' : delta),
            Permutation d d' ->
            WF d' t.
        Proof.
            intros d t HW.
            induction HW; intros d' HP;
            constructor; auto.
            apply Permutation_in with (l := d); auto.
        Qed.

        (* Weakening. *)
        Lemma weaken_delta :
            forall (d : delta) (t : type),
            WF d t ->
            forall (A : id),
            WF (A :: d) t.
        Proof.
            intros d t HW.
            induction HW; intros U;
            constructor; auto.
            - apply in_cons. assumption.
            - pose proof IHHW U as IH.
                apply delta_perm with
                    (d := U :: A :: d); auto.
                constructor.
        Qed.

        (* Contraction. *)
        Lemma contract_delta :
            forall (A : id) (d : delta) (t : type),
            WF (A :: A :: d) t ->
            WF (A :: d) t.
        Proof.
            intros A d t H.
            dependent induction H;
            constructor; subst; auto.
            - inv H; auto. constructor; auto.
            - apply IHWF. admit.
            (* Coq generates a jenk
                induction hypothesis. *)
        Admitted.
    End WellFormedness.

    Section Gamma.
        Definition gamma := id -> option type.

        Definition empty : gamma := fun x => None.

        Definition bind (x : id) (t : type) (g : gamma) : gamma :=
            fun y => if (x =? y)%string then Some t else g y.

        Lemma bind_correct : 
            forall (x : id) (t : type) (g : gamma),
            bind x t g x = Some t.
        Proof.
            intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
            - reflexivity.
            - apply eqb_neq in eq. contradiction.
        Qed.

        Lemma bind_complete :
            forall (x x' : id) (t t' : type),
            x' <> x -> 
            forall (g : gamma),
            (g x = Some t <-> bind x' t' g x = Some t). 
        Proof.
            intros. unfold bind. apply eqb_neq in H. 
            rewrite H. split; intros; apply H0.
        Qed.

        Lemma rebind_correct : 
            forall (x : id) (t t' : type) (g : gamma),
            bind x t (bind x t' g) = bind x t g.
        Proof.
            intros. apply functional_extensionality. intros y.
            unfold bind. destruct ((x =? y)%string); reflexivity.
        Qed.

        Lemma bind_diff_comm : 
            forall (x y : id) (u v : type) (g : gamma),
            x <> y ->
            bind x u (bind y v g) = bind y v (bind x u g).
        Proof.
            intros. apply functional_extensionality. intros z.
            unfold bind. destruct ((x =? z)%string) eqn:eq.
                - apply eqb_eq in eq; subst.
                    destruct ((y =? z)%string) eqn:eeq.
                    + apply eqb_eq in eeq; subst. contradiction.
                    + reflexivity.
                - apply eqb_neq in eq. destruct ((y =? z)%string) eqn:eeq; reflexivity.
        Qed.
    End Gamma.

    (* 
        Capture-avoiding type variable substitution:
            sub A u t t': t{u/A} = t'
    *)
    Inductive sub (A : id) (u : type) : type -> type -> Prop :=
        | sub_var_hit :
            sub A u (TVar A) u
        | sub_var_miss :
            forall (B : id),
            A <> B ->
            sub A u (TVar B) (TVar B)
        | sub_fun :
            forall (a b a' b' : type),
            sub A u a a' ->
            sub A u b b' ->
            sub A u (TFun a b) (TFun a' b')
        | sub_forall_bound :
            forall (t : type),
            sub A u (TForall A t) (TForall A t)
        | sub_forall_notfree :
            forall (B : id) (t t' : type),
            A <> B ->
            ~ IS.In B (fvt u) ->
            sub A u t t' ->
            sub A u (TForall B t) (TForall B t')
        | sub_forall_free :
            forall (B C : id) (t t' t'' : type),
            A <> B ->
            A <> C ->
            B <> C ->
            IS.In B (fvt u) ->
            ~ IS.In C (fvt u) ->
            ~ IS.In C (fvt t) ->
            sub B (TVar C) t t' ->
            sub A u t' t'' ->
            sub A u (TForall B t) (TForall C t'').



    Lemma sub_eq :
        forall (U : id) (t : type),
        sub U (TVar U) t t.
    Proof.
        intros U t. induction t.
        - destruct (IdDec.eq_dec U A) as [H | H]; subst.
            + apply sub_var_hit.
            + apply sub_var_miss; auto.
        - constructor; auto.
        - destruct (IdDec.eq_dec U A) as [H | H]; subst.
            + apply sub_forall_bound.
            + constructor; auto. simpl.
                intros HI. apply H.
                apply ISF.singleton_1 in HI.
                assumption.
    Qed.

    (* Type equivalence. *)
    Inductive teq : type -> type -> Prop :=
        | teq_eq :
            forall (t : type),
            teq t t
        | teq_fun :
            forall (a1 b1 a2 b2 : type),
            teq a1 a2 ->
            teq b1 b2 ->
            teq (TFun a1 b1) (TFun a2 b2)
        | teq_forall :
            forall (A B : id) (a a' b b' : type),
            sub B (TVar A) b b' ->
            teq a b' ->
            sub A (TVar B) a a' ->
            teq a' b ->
            teq (TForall A a) (TForall B b).

    (* Treating substitution like a procedure. *)
    (* Axiom sub_deterministic :
        forall (A : id) (a t t'1 t'2 : type),
        sub A a t t'1 ->
        sub A a t t'2 ->
        teq t'1 t'2. *)

    Lemma teq_sym :
        forall (t1 t2 : type),
        teq t1 t2 -> teq t2 t1.
    Proof.
        intros t1 t2 H. induction H;
        try constructor; auto.
        apply teq_forall with (a' := b') (b' := a'); auto.
    Qed.

    (* Type-checking with well-formedness checking. *)
    Inductive check (d : delta) (g : gamma) : expr -> type -> Prop :=
        | check_var :
            forall (x : id) (t : type),
            g x = Some t ->
            check d g (EVar x) t
        | check_fun :
            forall (x : id) (t t' : type) (e : expr),
            WF d t ->
            check d (bind x t g) e t' ->
            check d g (EFun x t e) (TFun t t')
        | check_app :
            forall (e1 e2 : expr) (a b c : type),
            teq a c ->
            check d g e1 (TFun a b) ->
            check d g e2 c ->
            check d g (EApp e1 e2) b
        | check_forall :
            forall (A : id) (e : expr) (t : type),
            check (A :: d) g e t ->
            check d g (EForall A e) (TForall A t)
        | check_inst :
            forall (e : expr) (u t t' : type) (A : id),
            WF d u ->
            sub A u t t' ->
            check d g e (TForall A t) ->
            check d g (EInst e u) t'.
End StaticSemantics.
Module SS := StaticSemantics.

Module DynamicSemantics.
    (* 
        Capture-avoiding substitution:
            sub x es e e': e{es/x} = e'
    *)
    Inductive sub (x : id) (es : expr) : expr -> expr -> Prop :=
        | sub_var_hit :
            sub x es (EVar x) es
        | sub_var_miss :
            forall (y : id),
            x <> y ->
            sub x es (EVar y) (EVar y)
        | sub_app :
            forall (e1 e2 e1' e2' : expr),
            sub x es e1 e1' ->
            sub x es e2 e2' ->
            sub x es (EApp e1 e2) (EApp e1' e2')
        | sub_fun_bound :
            forall (t : type) (e : expr),
            sub x es (EFun x t e) (EFun x t e)
        | sub_fun_notfree :
            forall (y : id) (t : type) (e e' : expr),
            x <> y ->
            ~ IS.In y (fve es) ->
            sub x es e e' ->
            sub x es (EFun y t e) (EFun y t e')
        | sub_fun_free :
            forall (y z : id) (t : type) (e e' e'' : expr),
            x <> y ->
            x <> z ->
            y <> z ->
            IS.In y (fve es) ->
            ~ IS.In z (fve es) ->
            ~ IS.In z (fve e) ->
            sub y (EVar z) e e' ->
            sub x es e' e'' ->
            sub x es (EFun y t e) (EFun z t e'')
        | sub_forall :
            forall (A : id) (e e' : expr),
            sub x es e e' ->
            sub x es (EForall A e) (EForall A e')
        | sub_inst :
            forall (e e' : expr) (t : type),
            sub x es e e' ->
            sub x es (EInst e t) (EInst e' t).

    Axiom sub_total :
        forall (x : id) (es e : expr),
        exists (e' : expr), sub x es e e'.

    (* 
        Capture-avoiding type-substitution in an expression:
            tsub A u e e': e{u/A} = e'.
    *)
    Inductive tsub (A : id) (u : type) : expr -> expr -> Prop :=
        | tsub_var :
            forall (x : id),
            tsub A u (EVar x) (EVar x)
        | tsub_fun :
            forall (x : id) (t t' : type) (e e' : expr),
            SS.sub A u t t' ->
            tsub A u e e' ->
            tsub A u (EFun x t e) (EFun x t' e')
        | tsub_app :
            forall (e1 e2 e1' e2' : expr),
            tsub A u e1 e1' ->
            tsub A u e2 e2' ->
            tsub A u (EApp e1 e2) (EApp e1' e2')
        | tsub_inst :
            forall (e e' : expr) (t t' : type),
            SS.sub A u t t' ->
            tsub A u e e' ->
            tsub A u (EInst e t) (EInst e' t')
        | tsub_forall_bound :
            forall (e : expr),
            tsub A u (EForall A e) (EForall A e)
        | tsub_forall_notfree :
            forall (B : id) (e e' : expr),
            A <> B ->
            ~ IS.In B (fvt u) ->
            tsub A u e e' ->
            tsub A u (EForall B e) (EForall B e')
        | tsub_forall_free :
            forall (B C : id) (e e' e'' : expr),
            A <> B ->
            A <> C ->
            B <> C ->
            IS.In B (fvt u) ->
            ~ IS.In C (fvt u) ->
            ~ IS.In C (fvte e) ->
            tsub B (TVar C) e e' ->
            tsub A u e' e'' ->
            tsub A u (EForall B e) (EForall C e'').

    Axiom tsub_total :
        forall (A : id) (u : type) (e : expr),
        exists (e' : expr), tsub A u e e'.

    (* Expression equivalence. *)
    Inductive eeq : expr -> expr -> Prop :=
        | eeq_eq :
            forall (e : expr),
            eeq e e
        | eeq_fun :
            forall (x : id) (t1 t2 : type) (e1 e2 : expr),
            SS.teq t1 t2 ->
            eeq e1 e2 ->
            eeq (EFun x t1 e1) (EFun x t2 e2)
        | eeq_app :
            forall (ea1 eb1 ea2 eb2 : expr),
            eeq ea1 ea2 ->
            eeq eb1 eb2 ->
            eeq (EApp ea1 eb1) (EApp ea2 eb2)
        | eeq_inst :
            forall (e1 e2 : expr) (t1 t2 : type),
            SS.teq t1 t2 ->
            eeq e1 e2 ->
            eeq (EInst e1 t1) (EInst e2 t2)
        | eeq_forall :
            forall (A1 A2 : id) (e1 e2 e2' : expr),
            tsub A2 (TVar A2) e2 e2' ->
            eeq e1 e2' ->
            eeq (EForall A1 e1) (EForall A2 e2).

    (* Lazy-evaluation. *)
    Inductive step : expr -> expr -> Prop :=
        | step_redux :
            forall (x : id) (t : type) (e e' es : expr),
            sub x es e e' ->
            step (EApp (EFun x t e) es) e'
        | step_app :
            forall (e1 e2 e1' : expr),
            step e1 e1' ->
            step (EApp e1 e2) (EApp e1' e2)
        | step_inst_forall :
            forall (A : id) (e e' : expr) (t : type),
            tsub A t e e' ->
            step (EInst (EForall A e) t) e'
        | step_inst :
            forall (e e' : expr) (t : type),
            step e e' ->
            step (EInst e t) (EInst e' t).

    (* Multi-step: *)
    Inductive mstep : expr -> expr -> Prop :=
        | mstep_refl :
            forall (e : expr),
            mstep e e
        | mstep_trans :
            forall (e e' e'' : expr),
            step e e' ->
            mstep e' e'' ->
            mstep e e''.
End DynamicSemantics.
Module DS := DynamicSemantics.

Module Progress.
    Module CanonicalForms.
        Definition canon_fun (v : expr) : Prop := 
            value v -> 
            forall (a b : type),
            SS.check [] SS.empty v (TFun a b) -> 
            exists (x : id) (t : type) (e : expr), 
            SS.teq a t /\ v = EFun x t e.
        
        Definition canon_forall (v : expr) : Prop :=
            value v ->
            forall (A : id) (t : type),
            SS.check [] SS.empty v (TForall A t) ->
            exists (B : id) (e : expr),
            SS.teq (TForall A t) (TForall B t) /\ v = EForall B e.

        Lemma canonical_forms_fun :
            forall (v : expr), canon_fun v.
        Proof.
            intros v HV a b HT.
            dependent induction HT; inv HV.
            exists x. exists a. exists e.
            repeat constructor.
        Qed.

        Lemma canonical_forms_forall :
            forall (v : expr), canon_forall v.
        Proof.
            intros v HV A t HT.
            dependent induction HT; inv HV.
            exists A. exists e.
            repeat constructor.
        Qed.   
    End CanonicalForms.
    Module CF := CanonicalForms.

    Theorem progress_thm : 
        forall (e : expr) (t : type),
        SS.check [] SS.empty e t ->
        value e \/ exists (e' : expr), DS.step e e'.
    Proof.
        intros e t HT.
        remember [] as d in HT.
        remember SS.empty as g in HT.
        assert (duh1 : @nil id = @nil id);
        assert (duh2 : SS.empty = SS.empty);
        try reflexivity.
        dependent induction HT; subst;
        try (pose proof IHHT  duh1 duh2 duh1 duh2 as IH;  clear IHHT);
        try (pose proof IHHT1 duh1 duh2 duh1 duh2 as IH1; clear IHHT1);
        try (pose proof IHHT2 duh1 duh2 duh1 duh2 as IH2; clear IHHT2);
        try discriminate; clear duh1 duh2; try clear IHHT.
        - left. constructor.
        - right. destruct IH1 as [H1 | H1].
            + pose proof 
                CF.canonical_forms_fun
                    e1 H1 a b HT1
                as [x [t [e [Hteq Hfun]]]]; subst.
                pose proof DS.sub_total x e2 e
                    as [e' HSub].
                exists e'. constructor; auto.
            + destruct H1 as [e1' Hstep].
                exists (EApp e1' e2).
                constructor; auto.
        - left. constructor.
        - right. destruct IH as [IHe | IHe].
            + pose proof 
                CF.canonical_forms_forall
                    e IHe A t HT
                as [B [ef [Hteq Hforall]]]; subst.
                pose proof DS.tsub_total B u ef
                    as [ef' HSub].
                exists ef'. constructor; auto.
            + destruct IHe as [e' Hstep].
                exists (EInst e' u).
                constructor; auto.
    Qed.
End Progress.

Module Preservation.
    Section SubstitutionLemmas.
        Lemma bind_unfree_var :
            forall (e : expr) (x : id) (a b : type) 
                (d : SS.delta) (g : SS.gamma),
            ~ IS.In x (fve e) ->
            SS.check d g e a <-> SS.check d (SS.bind x b g) e a.
        Proof.
            intros e z a b d g HIn.
            split; intros HT;
            dependent induction HT; simpl in *.
            - constructor. assert (Hxz : x <> z).
                + intros Hxz. apply HIn.
                    subst. constructor; auto.
                + apply SS.bind_complete; auto.
            - constructor; auto.
                destruct (IdDec.eq_dec x z)
                    as [Hxz | Hxz]; subst.
                    + rewrite SS.rebind_correct; auto.
                    + rewrite SS.bind_diff_comm;
                        auto. apply IHHT.
                        intros Hzf. apply HIn.
                        apply ISF.remove_2; auto.
            - apply SS.check_app with (a := a) (c := c); auto.
                + apply IHHT1. intros HI.
                    apply HIn. apply ISF.union_2; auto.
                + apply IHHT2. intros HI.
                    apply HIn. apply ISF.union_3; auto.
            - constructor; auto.
            - apply SS.check_inst with (A := A) (t := t); auto.
            - assert (Hxz : x <> z).
                + intros Hxz. apply HIn; subst.
                    constructor; auto.
                + constructor.
                    apply SS.bind_complete in H; auto.
            - constructor; auto.
                destruct (IdDec.eq_dec x z)
                    as [Hxz | Hxz]; subst.
                    + rewrite SS.rebind_correct
                        in HT. auto.
                    + apply IHHT with (z0 := z) (b0 := b).
                        * intros HI. apply HIn.
                            apply ISF.remove_2; auto.
                        * rewrite SS.bind_diff_comm; auto.
            - apply SS.check_app with (a := a) (c := c); auto.
                + apply IHHT1 with (z0 := z) (b1 := b); auto.
                    intros HI. apply HIn.
                    apply ISF.union_2; auto.
                + apply IHHT2 with (z0 := z) (b0 := b); auto.
                    intros HI. apply HIn.
                    apply ISF.union_3; auto.
            - constructor. apply IHHT with
                (z0 := z) (b0 := b); auto.
            - apply SS.check_inst with (A := A) (t := t); auto.
                apply IHHT with (z0 := z) (b0 := b); auto.
        Qed.

        Lemma delta_perm :
            forall (d : SS.delta) (g : SS.gamma)
                (e : expr) (t : type),
            SS.check d g e t ->
            forall (d' : SS.delta),
            Permutation d d' ->
            SS.check d' g e t.
        Proof.
            intros d g e t HT.
            induction HT; intros d' HP;
            try constructor; auto.
            - apply SS.delta_perm with (d := d); auto.
            - apply SS.check_app with (a := a) (c := c); auto.
            - apply SS.check_inst with (A := A) (t := t); auto.
                apply SS.delta_perm with (d := d); auto.
        Qed.

        Lemma bind_delta :
            forall (d : SS.delta) (g : SS.gamma)
                (e : expr) (t : type),
            SS.check d g e t ->
            forall (A : id),
            SS.check (A :: d) g e t.
        Proof.
            intros d g e t H.
            induction H; intros U;
            try constructor; auto.
            - apply SS.weaken_delta; auto.
            - apply SS.check_app with
                (a := a) (c := c); auto.
            - pose proof IHcheck U as IH.
                apply delta_perm with 
                    (d := U :: A :: d); auto.
                constructor.
            - pose proof IHcheck U as IH.
                apply SS.check_inst with (A := A) (t := t); auto.
                apply SS.weaken_delta; auto.
        Qed.

        Lemma substitution_lemma :
            forall (x : id) (es e e' : expr),
            DS.sub x es e e' ->
            forall (a b : type) (d : SS.delta) (g : SS.gamma),
            SS.check d (SS.bind x a g) e b -> 
            SS.check d g es a -> 
            SS.check d g e' b.
        Proof.
            intros x es e e' HS.
            induction HS;
            intros a b d g HTB HTS; inv HTB.
            - rewrite SS.bind_correct in H0.
                injintrosubst H0; auto.
            - constructor. rewrite 
                <- SS.bind_complete in H1; auto.
            - apply SS.check_app with (a := a0) (c := c); auto.
                + apply IHHS1 with (a := a); auto.
                + apply IHHS2 with (a := a); auto.
            - constructor; auto.
                rewrite SS.rebind_correct in H4; auto.
            - constructor; auto. rewrite <-
                SS.bind_diff_comm in H6; auto.
                apply IHHS in H6; auto.
                apply bind_unfree_var; auto.
            - constructor; auto.
                apply IHHS2 with (a := a).
                + rewrite SS.bind_diff_comm; auto.
                    apply IHHS1 with (a := t).
                    * rewrite SS.bind_diff_comm; auto.
                        apply bind_unfree_var; auto.
                    * constructor. apply SS.bind_correct.
                + apply bind_unfree_var; auto.
            - constructor.
                apply IHHS with (a := a); auto.
                apply bind_delta; auto.
            - apply SS.check_inst with
                (A := A) (t := t0); auto.
                apply IHHS with (a := a); auto.
        Qed.

        (*
            Substitution Lemmas from these notes:
                http://www.cs.cmu.edu/~crary/814/hw4/hw4-handout.pdf
        *)
        Lemma type_sub_type :
            forall (U : id) (u t t' : type),
            SS.sub U u t t' ->
            forall (d : SS.delta),
            SS.WF (U :: d) t ->
            SS.WF d u ->
            SS.WF d t'.
        Proof.
            intros U u t t' HSS.
            induction HSS;
            intros d HWFt HWFu; inv HWFt; auto;
            constructor; auto.
            - assert (duh : A :: d = [A] ++ d);
                try reflexivity.
                rewrite duh in H1.
                apply in_app_iff in H1 as [H1' | H1']; auto.
                inv H1'; try contradiction.
            - apply SS.contract_delta; auto.
            - apply IHHSS.
                + apply SS.delta_perm with
                    (d := B :: A :: d); auto.
                    constructor.
                + apply SS.weaken_delta; auto.
            - apply IHHSS2;
                try apply IHHSS1.
                    + apply SS.delta_perm with
                        (d := C :: B :: A :: d);
                        try apply SS.weaken_delta; auto.
                        apply Permutation_trans
                            with (l' := B :: C :: A :: d);
                        repeat constructor.
                    + apply SS.weaken_delta.
                        repeat constructor.
                    + apply SS.weaken_delta.
                        assumption.
        Qed.

        Definition sub_gamma (U : id) (u : type) (g g' : SS.gamma) : Prop := 
            forall (t t' : type),
            SS.sub U u t t' ->
            forall (x : id),
            g x = Some t -> g' x = Some t'.

        Remark sub_gamma_empty :
            forall (U : id) (u : type),
            sub_gamma U u SS.empty SS.empty.
        Proof. intros U u T T' _ x HES. inv HES. Qed.

        Lemma tsub_gamma_lemma :
            forall (U : id) (u : type) (e e' : expr),
            DS.tsub U u e e' ->
            forall (g g' : SS.gamma),
            sub_gamma U u g g' ->
            forall (t t' : type),
            SS.sub U u t t' ->
            forall (d : SS.delta),
            SS.WF d u ->
            SS.check (U :: d) g e t ->
            SS.check d g' e' t'.
        Proof.
            intros U u e e' HDS.
            induction HDS; 
            intros g g' HSG;
            unfold sub_gamma in HSG;
            intros w w' HSS d HWF HT; inv HT.
            - constructor. apply HSG with (t := w); auto.
            - inv HSS. admit.
            - apply SS.check_app with (a := a) (c := c); auto.
                + apply IHHDS1 with (g := g) (t := TFun a w); auto.
                    constructor; auto.
                    admit.
                + apply IHHDS2 with (g := g) (t := c); auto.
                    admit.
            - apply SS.check_inst with
                (A := A0) (t := t').
                + apply type_sub_type with
                    (U := A) (u := u) (t := t); auto.
                + admit.
                + apply IHHDS with
                    (g := g) (t := TForall A0 t0); auto.
                    admit.
            - inv HSS; try contradiction.
                constructor. admit.
            - inv HSS; try contradiction.
                constructor. apply IHHDS with
                    (g := g) (t := t); auto.
                    + apply SS.weaken_delta; auto.
                    + admit.
            - inv HSS; try contradiction.
                admit.
        Admitted.
    End SubstitutionLemmas.

    (* 
        This could've been part of the
            definition of check. 
    *)
    Axiom check_teq :
        forall (U V : type),
        SS.teq U V ->
        forall (e : expr),
        SS.check [] SS.empty e U ->
        SS.check [] SS.empty e V.

    Theorem preservation :
        forall (e e' : expr),
        DS.step e e' -> forall (t : type),
        SS.check [] SS.empty e t -> 
        SS.check [] SS.empty e' t.
    Proof.
        intros e e' HS.
        induction HS; intros u HT; inv HT.
        - inv H3. apply substitution_lemma with
            (a := a) (b := u) (d := []) (g := SS.empty) in H; auto.
            apply check_teq with (U := c); auto.
            apply SS.teq_sym. assumption.
        - apply SS.check_app with (a := a) (c := c); auto.
        - inv H5. apply tsub_gamma_lemma with
            (g := SS.empty) (U := A0)
                (u := t) (e := e) (t := t0); auto.
            apply sub_gamma_empty.
        - apply SS.check_inst with (A := A) (t := t0); auto.
    Qed.
End Preservation.

Module ChurchEncodings.
    Module Booleans.
        Definition X : type := TVar "X".
        
        Definition BOOL : type := TForall "X" (TFun X (TFun X X)). 
        
        Definition TRUE : expr := 
            EForall "X" (EFun "a" X (EFun "b" X (EVar "a"))).

        Definition FALSE : expr := 
            EForall "X" (EFun "a" X (EFun "b" X (EVar "b"))).

        Example true_bool :
            forall (d : SS.delta) (g : SS.gamma),
            SS.check d g TRUE BOOL.
        Proof. repeat constructor. Qed.

        Example false_bool :
            forall (d : SS.delta) (g : SS.gamma),
            SS.check d g FALSE BOOL.
        Proof. repeat constructor. Qed.

        Definition COND : expr :=
            EForall "X"
                (EFun "b" BOOL
                    (EFun "then" X
                        (EFun "else" X
                            (EApp
                                (EApp
                                    (EInst (EVar "b") X)
                                    (EVar "then"))
                                (EVar "else"))))).

        Example COND_check :
            forall (d : SS.delta) (g : SS.gamma),
            SS.check d g COND
                (TForall "X" (TFun BOOL (TFun X (TFun X X)))).
        Proof.
            repeat constructor.
            apply SS.check_app with
                (a := X) (c := X);
            repeat constructor.
            apply SS.check_app with
                (a := X) (c := X);
            repeat constructor.
            apply SS.check_inst with
                (A := "X") (t := TFun X (TFun X X));
            repeat constructor.
        Qed.

        Definition NOT : expr :=
            EFun "bool" BOOL
                (EForall "X"
                    (EFun "a" X
                        (EFun "b" X
                            (EApp 
                                (EApp 
                                    (EInst (EVar "bool") X)
                                    (EVar "b"))
                                (EVar "a"))))).

        Example NOT_check :
            forall (d : SS.delta) (g : SS.gamma),
            SS.check d g NOT (TFun BOOL BOOL).
        Proof.
            repeat constructor.
            apply SS.check_app with
                (a := X) (c := X);
            repeat constructor.
            apply SS.check_app with
                (a := X) (c := X);
            repeat constructor.
            apply SS.check_inst with
                (A := "X") (t := TFun X (TFun X X));
            repeat constructor.
        Qed.
    End Booleans.

    Module NaturalNumbers.
        Definition X : type := TVar "X".
        Definition R : type := TVar "R".

        Definition NAT : type := TForall "X" (TFun (TFun X X) (TFun X X)).
        
        Definition ZERO : expr := 
            EForall "X"
                (EFun "f" (TFun X X)
                    (EFun "z" X
                        (EVar "z"))).

        Example zero_nat :
            forall (d : SS.delta) (g : SS.gamma),
            SS.check d g ZERO NAT.
        Proof. repeat constructor. Qed.

        Definition SUCC : expr := 
            EFun "n" NAT
                (EForall "X"
                    (EFun "f" (TFun X X)
                        (EFun "z" X
                            (EApp 
                                (EVar "f")
                                (EApp
                                    (EApp
                                        (EInst (EVar "n") X)
                                        (EVar "f"))
                                    (EVar "z")))))).

        Example SUCC_check :
            forall (d : SS.delta) (g : SS.gamma),
            SS.check d g SUCC (TFun NAT NAT).
        Proof.
            repeat constructor.
            apply SS.check_app with
                (a := X) (c := X);
            repeat constructor.
            apply SS.check_app with
                (a := X) (c := X);
            repeat constructor.
            apply SS.check_app with
                (a := TFun X X) (c := TFun X X);
            repeat constructor.
            apply SS.check_inst with
                 (A := "X") (t := TFun (TFun X X) (TFun X X));
            repeat constructor.
        Qed.
        
        Definition ADD : expr := 
            EFun "n" NAT
                (EFun "m" NAT
                    (EApp 
                        (EApp 
                            (EInst (EVar "n") NAT)
                            SUCC)
                        (EVar "m"))).

        Example ADD_check :
            SS.check [] SS.empty ADD (TFun NAT (TFun NAT NAT)).
        Proof.
            repeat constructor.
            apply SS.check_app with
                (a := NAT) (c := NAT);
            repeat constructor.
            apply SS.check_app with
                (a := TFun NAT NAT) (c := TFun NAT NAT);
            try apply SUCC_check;
            repeat constructor.
            apply SS.check_inst with (A := "X")
            (t := TFun (TFun X X) (TFun X X));
            repeat constructor.
        Qed.
    End NaturalNumbers.
End ChurchEncodings.
