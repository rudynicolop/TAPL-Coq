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

Axiom exists_not_in :
    forall (S : IS.t),
    exists (X : id), ~ IS.In X S.

Section Gamma.
    Context {T : Type}.

    Definition gamma := id -> option T.

    Definition empty : gamma := fun x => None.

    Definition bind (x : id) (t : T) (g : gamma) : gamma :=
        fun y => if (x =? y)%string then Some t else g y.

    Lemma bind_correct : 
        forall (x : id) (t : T) (g : gamma),
        bind x t g x = Some t.
    Proof.
        intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
        - reflexivity.
        - apply eqb_neq in eq. contradiction.
    Qed.

    Lemma bind_complete :
        forall (x x' : id) (t t' : T),
        x' <> x -> 
        forall (g : gamma),
        (g x = Some t <-> bind x' t' g x = Some t). 
    Proof.
        intros. unfold bind. apply eqb_neq in H. 
        rewrite H. split; intros; apply H0.
    Qed.

    Lemma rebind_correct : 
        forall (x : id) (t t' : T) (g : gamma),
        bind x t (bind x t' g) = bind x t g.
    Proof.
        intros. apply functional_extensionality. intros y.
        unfold bind. destruct ((x =? y)%string); reflexivity.
    Qed.

    Lemma bind_diff_comm : 
        forall (x y : id) (u v : T) (g : gamma),
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

Module Univerals.
    Module Syntax.
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
        Export Syntax.

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

        Section TypeSubstitution.
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

            (* 
                Type substitution in types is a total function.
                TODO: maybe provable with axiom.
            *)
            Axiom sub_total :
                forall (U : id) (u t : type),
                exists (t' : type), sub U u t t'.

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

        End TypeSubstitution.

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
        Export Syntax.

        Section Substitution.
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

            (* 
                Expression Substitution is a total function.
                TODO: maybe provable with axiom.
            *)
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

            (* 
                Type substitution in expressions is a total function.
                TODO: maybe provable with axiom.
             *)
            Axiom tsub_total :
                forall (A : id) (u : type) (e : expr),
                exists (e' : expr), tsub A u e e'.
        End Substitution.

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
        Export Syntax.

        Module CanonicalForms.
            Definition canon_fun (v : expr) : Prop := 
                value v -> 
                forall (a b : type),
                SS.check [] empty v (TFun a b) -> 
                exists (x : id) (t : type) (e : expr), 
                SS.teq a t /\ v = EFun x t e.
            
            Definition canon_forall (v : expr) : Prop :=
                value v ->
                forall (A : id) (t : type),
                SS.check [] empty v (TForall A t) ->
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
            SS.check [] empty e t ->
            value e \/ exists (e' : expr), DS.step e e'.
        Proof.
            intros e t HT.
            remember [] as d in HT.
            remember empty as g in HT.
            assert (duh1 : @nil id = @nil id);
            assert (duh2 : @empty type = @empty type);
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
        Export Syntax.

        Section SubstitutionLemmas.
            Lemma bind_unfree_var :
                forall (e : expr) (x : id) (a b : type) 
                    (d : SS.delta) (g : gamma),
                ~ IS.In x (fve e) ->
                SS.check d g e a <-> SS.check d (bind x b g) e a.
            Proof.
                intros e z a b d g HIn.
                split; intros HT;
                dependent induction HT; simpl in *.
                - constructor. assert (Hxz : x <> z).
                    + intros Hxz. apply HIn.
                        subst. constructor; auto.
                    + apply bind_complete; auto.
                - constructor; auto.
                    destruct (IdDec.eq_dec x z)
                        as [Hxz | Hxz]; subst.
                        + rewrite rebind_correct; auto.
                        + rewrite bind_diff_comm;
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
                        apply bind_complete in H; auto.
                - constructor; auto.
                    destruct (IdDec.eq_dec x z)
                        as [Hxz | Hxz]; subst.
                        + rewrite rebind_correct
                            in HT. auto.
                        + apply IHHT with (z0 := z) (b0 := b).
                            * intros HI. apply HIn.
                                apply ISF.remove_2; auto.
                            * rewrite bind_diff_comm; auto.
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
                forall (d : SS.delta) (g : gamma)
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
                forall (d : SS.delta) (g : gamma)
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
                forall (a b : type) (d : SS.delta) (g : gamma),
                SS.check d (bind x a g) e b -> 
                SS.check d g es a -> 
                SS.check d g e' b.
            Proof.
                intros x es e e' HS.
                induction HS;
                intros a b d g HTB HTS; inv HTB.
                - rewrite bind_correct in H0.
                    injintrosubst H0; auto.
                - constructor. rewrite 
                    <- bind_complete in H1; auto.
                - apply SS.check_app with (a := a0) (c := c); auto.
                    + apply IHHS1 with (a := a); auto.
                    + apply IHHS2 with (a := a); auto.
                - constructor; auto.
                    rewrite rebind_correct in H4; auto.
                - constructor; auto. rewrite <-
                    bind_diff_comm in H6; auto.
                    apply IHHS in H6; auto.
                    apply bind_unfree_var; auto.
                - constructor; auto.
                    apply IHHS2 with (a := a).
                    + rewrite bind_diff_comm; auto.
                        apply IHHS1 with (a := t).
                        * rewrite bind_diff_comm; auto.
                            apply bind_unfree_var; auto.
                        * constructor. apply bind_correct.
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

            Definition sub_gamma (U : id) (u : type) (g g' : gamma) : Prop := 
                forall (t t' : type),
                SS.sub U u t t' ->
                forall (x : id),
                g x = Some t -> g' x = Some t'.

            Remark sub_gamma_empty :
                forall (U : id) (u : type),
                sub_gamma U u empty empty.
            Proof. intros U u T T' _ x HES. inv HES. Qed.

            Lemma tsub_gamma_lemma :
                forall (U : id) (u : type) (e e' : expr),
                DS.tsub U u e e' ->
                forall (g g' : gamma),
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
            SS.check [] empty e U ->
            SS.check [] empty e V.

        Theorem preservation :
            forall (e e' : expr),
            DS.step e e' -> forall (t : type),
            SS.check [] empty e t -> 
            SS.check [] empty e' t.
        Proof.
            intros e e' HS.
            induction HS; intros u HT; inv HT.
            - inv H3. apply substitution_lemma with
                (a := a) (b := u) (d := []) (g := empty) in H; auto.
                apply check_teq with (U := c); auto.
                apply SS.teq_sym. assumption.
            - apply SS.check_app with (a := a) (c := c); auto.
            - inv H5. apply tsub_gamma_lemma with
                (g := empty) (U := A0)
                    (u := t) (e := e) (t := t0); auto.
                apply sub_gamma_empty.
            - apply SS.check_inst with (A := A) (t := t0); auto.
        Qed.
    End Preservation.

    Module ChurchEncodings.
        Export Syntax.

        Module Booleans.
            Definition X : type := TVar "X".
            
            Definition BOOL : type := TForall "X" (TFun X (TFun X X)). 
            
            Definition TRUE : expr := 
                EForall "X" (EFun "a" X (EFun "b" X (EVar "a"))).

            Definition FALSE : expr := 
                EForall "X" (EFun "a" X (EFun "b" X (EVar "b"))).

            Example true_bool :
                forall (d : SS.delta) (g : gamma),
                SS.check d g TRUE BOOL.
            Proof. repeat constructor. Qed.

            Example false_bool :
                forall (d : SS.delta) (g : gamma),
                SS.check d g FALSE BOOL.
            Proof. repeat constructor. Qed.

            (* COND b t f = if b then t else f *)
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
                forall (d : SS.delta) (g : gamma),
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

            (* NOT b = !b *)
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
                forall (d : SS.delta) (g : gamma),
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

            Definition NAT : type := TForall "X" (TFun (TFun X X) (TFun X X)).
            
            Definition ZERO : expr := 
                EForall "X"
                    (EFun "f" (TFun X X)
                        (EFun "z" X
                            (EVar "z"))).

            Example zero_nat :
                forall (d : SS.delta) (g : gamma),
                SS.check d g ZERO NAT.
            Proof. repeat constructor. Qed.

            (* SUCC n = n + 1 *)
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
                forall (d : SS.delta) (g : gamma),
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
            
            (* ADD n m = n + m *)
            Definition ADD : expr := 
                EFun "n" NAT
                    (EFun "m" NAT
                        (EApp 
                            (EApp 
                                (EInst (EVar "n") NAT)
                                SUCC)
                            (EVar "m"))).

            Example ADD_check :
                forall (d : SS.delta) (g : gamma),
                SS.check d g ADD (TFun NAT (TFun NAT NAT)).
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

            (* MUL n m = n * m *)
            Definition MUL : expr :=
                EFun "n" NAT
                    (EFun "m" NAT
                        (EApp 
                            (EApp 
                                (EInst (EVar "n") NAT)
                                (EApp ADD (EVar "m")))
                        ZERO)).

            Example MUL_check :
                forall (d : SS.delta) (g : gamma),
                SS.check d g MUL (TFun NAT (TFun NAT NAT)).
            Proof.
                repeat constructor.
                apply SS.check_app with
                    (a := NAT) (c := NAT);
                repeat constructor.
                apply SS.check_app with
                    (a := TFun NAT NAT) (c := TFun NAT NAT);
                repeat constructor.
                - apply SS.check_inst with
                    (A := "X") (t := TFun (TFun X X) (TFun X X));
                    repeat constructor.
                - apply SS.check_app with
                    (a := NAT) (c := NAT);
                    try apply ADD_check;
                    try apply zero_nat;
                    repeat constructor.
            Qed.

            (* EXP m n = m^n *)
            Definition EXP : expr :=
                EFun "m" NAT
                    (EFun "n" NAT
                        (EApp 
                            (EApp 
                                (EInst (EVar "n") NAT)
                                (EApp MUL (EVar "m")))
                        (EApp SUCC ZERO))).

            Example EXP_check :
                forall (d : SS.delta) (g : gamma),
                SS.check d g EXP (TFun NAT (TFun NAT NAT)).
            Proof.
                repeat constructor.
                apply SS.check_app with
                    (a := NAT) (c := NAT);
                repeat constructor.
                - apply SS.check_app with
                    (a := TFun NAT NAT) (c := TFun NAT NAT);
                    try constructor.
                    + apply SS.check_inst with
                        (A := "X") (t := TFun (TFun X X) (TFun X X));
                        repeat constructor.
                    + apply SS.check_app with 
                        (a := NAT) (c := NAT);
                        try apply MUL_check;
                        repeat constructor.
                - apply SS.check_app with 
                    (a := NAT) (c := NAT);
                    try apply SUCC_check;
                    try apply zero_nat;
                    constructor.
            Qed.
        End NaturalNumbers.

        Module Pairs.
            Definition X : type := TVar "X".
            Definition Y : type := TVar "Y".
            Definition R : type := TVar "R".

            (*
                PROD A B = A * B.
                System F has no type constructors,
                i.e. no type-level functions, so
                I need Coq's type-constructors.
            *)
            Definition PROD (A B : type) : type := 
                TForall "R"
                    (TFun
                        (TFun A (TFun B R))
                    R).
                                
            Definition PAIR : expr := 
                EForall "X"
                    (EForall "Y"
                        (EFun "x" X
                            (EFun "y" Y
                                (EForall "R"
                                    (EFun "continuation"
                                        (TFun X (TFun Y R))
                                    (EApp 
                                        (EApp
                                            (EVar "continuation")
                                            (EVar "x"))
                                        (EVar "y"))))))).

            Example pair_check :
                forall (d : SS.delta) (g : gamma),
                SS.check d g PAIR
                    (TForall "X"
                        (TForall "Y" 
                            (TFun X (TFun Y (PROD X Y))))).
            Proof.
                intros d g.
                constructor. constructor.
                constructor.
                - constructor. apply in_cons.
                    repeat constructor. 
                - constructor.
                    + repeat constructor.
                    + constructor. constructor.
                        { constructor. constructor.
                            - apply in_cons. apply in_cons.
                                repeat constructor.
                            - constructor; constructor.
                                + apply in_cons.
                                    repeat constructor.
                                + repeat constructor. }
                        { apply SS.check_app with
                            (a := Y) (c := Y);
                            repeat constructor.
                            apply SS.check_app with
                                (a := X) (c := X);
                            repeat constructor. }
            Qed.

            Ltac dispatch_union HUNION :=
                repeat split; intros HFALSE; apply HUNION; subst;
                    try (apply ISF.union_2;
                        apply ISF.union_2;
                        apply ISF.singleton_2;
                        reflexivity);
                    try (apply ISF.union_2;
                        apply ISF.union_3;
                        apply ISF.singleton_2;
                        reflexivity);
                    try (apply ISF.union_3;
                        apply ISF.union_2;
                        assumption);
                    try (apply ISF.union_3;
                        apply ISF.union_3;
                        assumption).

            Example pair_prod :
                forall (d : SS.delta) (g : gamma)
                (e1 e2 : expr) (A B : type),
                SS.WF d A ->
                SS.WF d B ->
                SS.check d g e1 A ->
                SS.check d g e2 B ->
                SS.check d g
                    (EApp
                        (EApp
                            (EInst (EInst PAIR A) B)
                            e1) 
                    e2)  
                    (PROD A B).
                Proof.
                    intros d g e1 e2 A B WA WB HA HB.
                    apply SS.check_app with
                        (a := B) (c := B);
                    repeat constructor; auto.
                    apply SS.check_app with
                        (a := A) (c := A);
                    repeat constructor; auto.
                    apply SS.check_inst with 
                        (A := "Y") (t := TFun A
                            (TFun Y (PROD A Y))); auto.
                    - admit. 
                        (* next case has a similarly (obnoxious)
                            sub-case as this...not worth it. *)
                    - apply SS.check_inst with
                        (A := "X") (t := TForall "Y"
                            (TFun X (TFun Y (PROD X Y)))); auto;
                        try apply pair_check.
                        destruct (ISDA.dec_In "Y" (fvt A)) as [HY | HY].
                        { pose proof exists_not_in
                            (IS.union 
                                (IS.union
                                    (IS.singleton "X")
                                    (IS.singleton "Y")) 
                                (IS.union (fvt A) 
                                    (fvt (TFun X (TFun Y (PROD X Y))))))
                            as [Z HIn].
                            assert (HBIG : "X" <> Z /\
                                "Y" <> Z /\
                                ~ IS.In Z (fvt A) /\
                                ~ IS.In Z (fvt (TFun X (TFun Y (PROD X Y)))));
                            try dispatch_union HIn.
                            destruct HBIG as [Hxz [Hyz [HFA HFT]]].
                            pose proof SS.sub_total "Y" (TVar Z)
                                (TFun X (TFun Y (PROD X Y)))
                                as [t' Ht']. 
                            (* too many sub-cases...not worth it... *)
                            admit. }
                        { apply SS.sub_forall_notfree; auto;
                            try (intros Hxy; discriminate).
                            constructor; constructor;
                            try (apply SS.sub_var_miss;
                                intros Hxy; discriminate).
                            unfold PROD.
                            destruct (ISDA.dec_In "R" (fvt A)) as [HR | HR].
                            + pose proof exists_not_in
                                (IS.union 
                                    (IS.union
                                        (IS.singleton "X")
                                        (IS.singleton "R")) 
                                    (IS.union (fvt A) 
                                        (fvt (TFun (TFun X (TFun Y R)) R))))
                                as [Z HIn].
                                assert (HBIG : "X" <> Z /\
                                    "R" <> Z /\
                                    ~ IS.In Z (fvt A) /\
                                    ~ IS.In Z (fvt (TFun (TFun X (TFun Y R)) R)));
                                try dispatch_union HIn.
                                destruct HBIG as
                                    [Hxz [Hrz [HFA HFT]]].
                                pose proof SS.sub_total "R" (TVar Z)
                                    (TFun (TFun X (TFun Y R)) R) as [t' Ht'].
                                inv Ht'. inv H1. inv H5.
                                inv H3; try contradiction.
                                inv H2. inv H4. inv H7;
                                try contradiction.
                                apply SS.sub_forall_free with
                                    (t' := TFun (TFun (TVar "X")
                                        (TFun (TVar "Y") (TVar Z))) (TVar Z));
                                repeat constructor; auto. 
                                (* 
                                    this is futile...would need another
                                    axiom for substitution and type equality.
                                *) }       
                Admitted.
        End Pairs.
    End ChurchEncodings.
End Univerals.

Module Existentials.
    Module Syntax.
        Inductive type : Type :=
            | TVar (X : id)
            | TFun (t t' : type)
            | TForall (X : id) (t : type)
            | TExists (R : id) (t : type). (* exists representation type R. *)

        (* Free type-variables in a type. *)
        Fixpoint fvt (t : type) : IS.t :=
            match t with
            | TVar A => IS.singleton A
            | TFun a b => IS.union (fvt a) (fvt b)
            | TForall A t 
            | TExists A t => IS.remove A (fvt t)
            end.

        Inductive expr : Type :=
            | EVar (x : id)
            | EFun (x : id) (t : type) (e : expr)
            | EApp (e1 e2 : expr)
            | EForall (A : id) (e : expr)
            | EInst (e : expr) (t : type)
            | EPack (t r : type) (e : expr)
                (* pack representation type r
                    with implementation e as existential type t *)
            | EUnpack (A a : id) (e1 e2 : expr).
                (* unpack (open/import) existential (module) e1
                    with abstract data type A and name a in e2 *)

        (* Free type-variables in an expression. *)
        Fixpoint fvte (e : expr) : IS.t :=
            match e with
            | EVar _ => IS.empty
            | EFun _ t e 
            | EInst e t => IS.union (fvt t) (fvte e)
            | EApp e1 e2 => IS.union (fvte e1) (fvte e2)
            | EForall A e => IS.remove A (fvte e)
            | EPack t r e => IS.union (IS.union (fvt r) (fvt t)) (fvte e)
            | EUnpack A _ e1 e2 => IS.union (fvte e1) (IS.remove A (fvte e2))
            end.

        (* Free expression-variables in an expression. *)
        Fixpoint fve (e : expr) : IS.t :=
            match e with
            | EVar x => IS.singleton x
            | EFun x t e => IS.remove x (fve e)
            | EApp e1 e2 => IS.union (fve e1) (fve e2)
            | EForall _ e
            | EInst e _ 
            | EPack _ _ e => fve e
            | EUnpack _ a e1 e2 => IS.union (fve e1) (IS.remove a (fve e2))
            end.

        Inductive value : expr -> Prop :=
            | value_fun :
                forall (x : id) (t : type) (e : expr),
                value (EFun x t e)
            | value_forall :
                forall (A : id) (e : expr),
                value (EForall A e)
            | value_pack :
                forall (t r : type) (e : expr),
                value e ->
                value (EPack t r e).
    End Syntax.
    Export Syntax.

    Module StaticSemantics.
        Section WellFoundedness.
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
                    WF d (TForall A t)
                | wf_exists :
                    forall (R : id) (t : type),
                    WF (R :: d) t ->
                    WF d (TExists R t).

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
                        (d := U :: A :: d); 
                    auto. constructor.
                - pose proof IHHW U as IH.
                    apply delta_perm with
                        (d := U :: R :: d); 
                    auto. constructor.
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
                - apply IHWF. admit.
                (* Coq generates a jenk
                    induction hypothesis. *)
            Admitted.
        End WellFoundedness.

        Section TypeSubstitution.
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
                    sub A u (TForall B t) (TForall C t'')
                | sub_exists_bound :
                    forall (t : type),
                    sub A u (TExists A t) (TExists A t)
                | sub_exists_notfree :
                    forall (R : id) (t t' : type),
                    A <> R ->
                    ~ IS.In R (fvt u) ->
                    sub A u t t' ->
                    sub A u (TExists R t) (TExists R t')
                | sub_exists_free :
                    forall (R R' : id) (t t' t'' : type),
                    A <> R ->
                    A <> R' ->
                    R <> R' ->
                    IS.In R (fvt u) ->
                    ~ IS.In R' (fvt u) ->
                    ~ IS.In R' (fvt t) ->
                    sub R (TVar R') t t' ->
                    sub A u t' t'' ->
                    sub A u (TExists R t) (TExists R' t'').

            (* 
                Type substitution is a total function.
                TODO: maybe provable with axiom.
             *)
            Axiom sub_total :
                forall (U : id) (u t : type),
                exists (t' : type), sub U u t t'.

            Lemma sub_eq :
                forall (U : id) (t : type),
                sub U (TVar U) t t.
            Proof.
                intros U t. induction t.
                - destruct (IdDec.eq_dec U X) as [H | H]; subst.
                    + apply sub_var_hit.
                    + apply sub_var_miss; auto.
                - constructor; auto.
                - destruct (IdDec.eq_dec U X) as [H | H]; subst.
                    + apply sub_forall_bound.
                    + constructor; auto. simpl.
                        intros HI. apply H.
                        apply ISF.singleton_1 in HI.
                        assumption.
                - destruct (IdDec.eq_dec U R) as [H | H]; subst.
                    + apply sub_exists_bound.
                    + constructor; auto. simpl.
                        intros HI. apply H.
                        apply ISF.singleton_1 in HI.
                        assumption.
            Qed.

        End TypeSubstitution.

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
                teq (TForall A a) (TForall B b)
            | teq_exists :
                forall (R1 R2 : id) (t1 t1' t2 t2' : type),
                sub R2 (TVar R1) t2 t2' ->
                teq t1 t2' ->
                sub R1 (TVar R2) t1 t1' ->
                teq t1' t2 ->
                teq (TExists R1 t1) (TExists R2 t2).

        Lemma teq_sym :
            forall (t1 t2 : type),
            teq t1 t2 -> teq t2 t1.
        Proof.
            intros t1 t2 H. induction H;
            try constructor; auto.
            - apply teq_forall with (a' := b') (b' := a'); auto.
            - apply teq_exists with (t1' := t2') (t2' := t1'); auto.
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
                check d g (EInst e u) t'
            | check_pack :
                forall (R : id) (t r t' : type) (e : expr),
                sub R r t t' ->
                check d g e t' ->
                check d g (EPack (TExists R t) r e) (TExists R t)
            | check_unpack :
                forall (A a R : id) (e1 e2 : expr) (t1 t2 : type),
                WF d t2 ->
                check d g e1 (TExists R t1) ->
                check (A :: d) (bind a t1 g) e2 t2 ->
                check d g (EUnpack A a e1 e2) t2.
    End StaticSemantics.
    Module SS := StaticSemantics.

    Module DynamicSemantics.
        Section Substitution.
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
                    sub x es (EInst e t) (EInst e' t)
                | sub_pack :
                    forall (t r : type) (e e' : expr),
                    sub x es e e' ->
                    sub x es (EPack t r e) (EPack t r e')
                | sub_unpack_bound :
                    forall (A : id) (e1 e2 e1' : expr),
                    sub x es e1 e1' ->
                    sub x es (EUnpack A x e1 e2) (EUnpack A x e1' e2)
                | sub_unpack_notfree :
                    forall (A y : id) (e1 e2 e1' e2' : expr),
                    x <> y ->
                    ~ IS.In y (fve es) ->
                    sub x es e1 e1' ->
                    sub x es e2 e2' ->
                    sub x es (EUnpack A y e1 e2) (EUnpack A y e1' e2')
                | sub_unpack_free :
                    forall (A y z: id) (e1 e2 e1' e2' e2'' : expr),
                    x <> y ->
                    x <> z ->
                    y <> z ->
                    IS.In y (fve es) ->
                    ~ IS.In z (fve es) ->
                    ~ IS.In z (fve e2) ->
                    sub x es e1 e1' ->
                    sub y (EVar z) e2 e2' ->
                    sub x es e2' e2'' ->
                    sub x es (EUnpack A y e1 e2) (EUnpack A z e1' e2'').

            (*
                Expression substitution is a total function.
                TODO: maybe provable with axiom.
             *)
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
                    tsub A u (EForall B e) (EForall C e'')
                | tsub_pack :
                    forall (r t r' t' : type) (e e' : expr),
                    SS.sub A u r r' ->
                    SS.sub A u t t' ->
                    tsub A u e e' ->
                    tsub A u (EPack r t e) (EPack r' t' e')
                | tsub_unpack_bound :
                    forall (a : id) (e1 e2 e1' : expr),
                    tsub A u e1 e1' ->
                    tsub A u (EUnpack A a e1 e2) (EUnpack A a e1' e2)
                | tsub_unpack_notfree :
                    forall (B a : id) (e1 e2 e1' e2' : expr),
                    A <> B ->
                    ~ IS.In B (fvt u) ->
                    tsub A u e1 e1' ->
                    tsub A u e2 e2' ->
                    tsub A u (EUnpack B a e1 e2) (EUnpack B a e1' e2')
                | tsub_unpack_free :
                    forall (B C a : id) (e1 e2 e1' e2' e2'' : expr),
                    A <> B ->
                    A <> C ->
                    B <> C ->
                    IS.In B (fvt u) ->
                    ~ IS.In C (fvt u) ->
                    ~ IS.In C (fvte e2) ->
                    tsub A u e1 e1' ->
                    tsub B (TVar C) e2 e2' ->
                    tsub A u e2' e2'' ->
                    tsub A u (EUnpack B a e1 e2) (EUnpack C a e1' e2'').

            (* 
                Type substitution in expressions is a total function.
                TODO: maybe axiom makes this provable.
             *)
            Axiom tsub_total :
                forall (A : id) (u : type) (e : expr),
                exists (e' : expr), tsub A u e e'.
        End Substitution.

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
                step (EInst e t) (EInst e' t)
            | step_unpack_pack :
                forall (A a : id) (t r : type) (e1 e2 e2' e2'' : expr),
                sub a e1 e2 e2' ->
                tsub A r e2' e2'' ->
                step (EUnpack A a (EPack t r e1) e2) e2''
            | step_pack :
                forall (t r : type) (e e' : expr),
                step e e' ->
                step (EPack t r e) (EPack t r e')
            | step_unpack :
                forall (A a : id) (e1 e2 e1' : expr),
                step e1 e1' ->
                step (EUnpack A a e1 e2) (EUnpack A a e1' e2).
    End DynamicSemantics.

    Module Encoding.
        Module SF := Univerals.Syntax.

        (* 
            Type encodings.
            TODO: maybe provable with other axiom.
        *)
        Inductive tencode : type -> SF.type -> Prop :=
            | tencode_var : 
                forall (A : id),
                tencode (TVar A) (SF.TVar A)
            | tencode_fun :
                forall (t1 t2 : type) (t1' t2' : SF.type),
                tencode t1 t1' ->
                tencode t2 t2' ->
                tencode (TFun t1 t2) (SF.TFun t1' t2')
            | tencode_forall :
                forall (A : id) (t : type) (t' : SF.type),
                tencode t t' ->
                tencode (TForall A t) (SF.TForall A t')
            | tencode_exists :
                forall (X R : id) (t : type) (t' : SF.type),
                ~ IS.In R (SF.fvt t') ->
                tencode t t' ->
                tencode (TExists X t)
                    (SF.TForall R
                        (SF.TFun
                            (SF.TForall X (SF.TFun t' (SF.TVar R)))
                            (SF.TVar R))).

        (* Type-encoding is a total function. *)
        Axiom tencode_total :
            forall (t : type), exists (t' : SF.type),
            tencode t t'.
        
        (* Expression encodings, with type-checking embedded in premises. *)
        Inductive eencode (d : SS.delta) (g : gamma) : type -> expr -> SF.expr -> Prop :=
            | eencode_var :
                forall (x : id) (t : type),
                g x = Some t ->
                eencode d g t (EVar x) (SF.EVar x)
            | eencode_fun :
                forall (x : id) (t1 t2 : type) (e : expr)
                    (t1' : SF.type) (e' : SF.expr),
                SS.WF d t1 ->
                SS.check d (bind x t1 g) e t2 ->    
                tencode t1 t1' ->
                eencode d (bind x t1 g) t2 e e' ->
                eencode d g (TFun t1 t2) (EFun x t1 e) (SF.EFun x t1' e')
            | eencode_app :
                forall (t1 t2 : type) (e1 e2 : expr) (e1' e2' : SF.expr),
                SS.check d g e1 (TFun t1 t2) ->
                SS.check d g e2 t1 ->
                eencode d g (TFun t1 t2) e1 e1' ->
                eencode d g t1 e2 e2' ->
                eencode d g t2 (EApp e1 e2) (SF.EApp e1' e2')
            | eencode_forall :
                forall (X : id) (t : type) (e : expr) (e' : SF.expr),
                SS.check (X :: d) g e t ->
                eencode (X :: d) g t e e' ->
                eencode d g (TForall X t) (EForall X e) (SF.EForall X e')
            | eencode_inst :
                forall (e : expr) (u t ts : type) (A : id)
                    (e' : SF.expr) (u' : SF.type),
                SS.WF d u ->
                SS.sub A u t ts ->
                SS.check d g e (TForall A t) ->
                tencode u u' ->
                eencode d g (TForall A t) e e' ->
                eencode d g ts (EInst e u) (SF.EInst e' u')
            | eencode_pack :
                forall (X R k : id) (t r ts : type) (e : expr)
                    (t' r' : SF.type) (e' : SF.expr),
                ~ IS.In R (SF.fvt t') ->
                ~ IS.In R (SF.fvt r') ->
                ~ IS.In R (SF.fvte e') ->
                ~ IS.In k (SF.fve e') ->
                SS.sub X r t ts ->
                SS.check d g e ts ->
                tencode t t' ->
                tencode r r' ->
                eencode d g ts e e' ->
                eencode d g (TExists X t) (EPack (TExists X t) r e)
                    (SF.EForall R
                        (SF.EFun k (SF.TForall X (SF.TFun t' (SF.TVar R)))
                             (SF.EApp (SF.EInst (SF.EVar k) r') e')))
            | eencode_unpack :
                forall (A R x : id) (e1 e2 : expr) (e1' e2' : SF.expr)
                    (t1 t2 : type) (t2' : SF.type),
                SS.WF d t2 ->
                SS.check d g e1 (TExists R t1) ->
                SS.check (A :: d) (bind x t1 g) e2 t2 ->
                tencode t2 t2' ->
                eencode d g (TExists R t1) e1 e1' ->
                eencode (A :: d) (bind x t1 g) t2 e2 e2' ->
                eencode d g t2 (EUnpack A x e1 e2)
                    (SF.EApp (SF.EInst e1' t2')
                        (SF.EForall A (SF.EFun x (SF.TVar A) e2'))).

        (* 
            Expression-encoding is a total function. 
            TODO: maybe provable with other axiom.
        *)
        Axiom eencode_total :
            forall (d : SS.delta) (g : gamma) (t : type) (e : expr),
            SS.check d g e t ->
            exists (e' : SF.expr), eencode d g t e e'.

        (* Encoding type-checks. *)
        Lemma encode_check :
            forall (d : SS.delta) (g : gamma)
                (t : type) (e : expr),
            SS.check d g e t <-> 
            exists (e' : SF.expr),
            eencode d g t e e'.
        Proof.
            intros d g t e. split; intros H;
            try destruct H as [e' H];
            inv H; try apply eencode_total; auto;
            try constructor; auto.
            - apply SS.check_app with (a := t1) (c := t1);
                auto; constructor.
            - apply SS.check_inst with
                (A := A) (t := t0); auto.
            - apply SS.check_pack with (t' := ts); auto.
            - apply SS.check_unpack with (R := R) (t1 := t1); auto.
        Qed.
    End Encoding.
End Existentials.
