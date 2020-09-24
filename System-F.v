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
Module IS := WS.Make(IdDec).
Module ISF := MSF.WFactsOn(IdDec)(IS).

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
            bind x t g = bind x t (bind x t' g).
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

    Axiom sub_total :
        forall (A : id) (u t : type),
        exists (t' : type), sub A u t t'.

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
            forall (A B : id) (a b b' : type),
            sub B (TVar A) b b' ->
            teq a b' ->
            teq (TForall A a) (TForall B b).

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
            forall (x : id) (t : type) (e e' e'' : expr),
            sub x e e' e'' ->
            step (EApp (EFun x t e) e') e''
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
End DynamicSemantics.
Module DS := DynamicSemantics.

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

Module Progress.
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
                pose proof DS.sub_total x e e2
                    as [e2' HSub].
                exists e2'. constructor; auto.
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
