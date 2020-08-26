Set Warnings "-notation-overridden,-parsing".
Require Import String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

(* Require Import Coq.Sets.Ensembles. *)

(* The Simply-Typed Lambda Calculus *)

(* STLC types *)
Inductive ltype : Type :=
    | TNat : ltype
    | TBool : ltype
    | TArrow : ltype -> ltype -> ltype.

(* Binary operators *)
Inductive bop : Type :=
    | EAdd 
    | EMul
    | ESub
    | EEq
    | ELe
    | EAnd
    | EOr.

(* STLC expressions *)
Inductive expr : Type :=
    | ENat : nat -> expr
    | EBool : bool -> expr
    | EVar : string -> expr
    | ENot : expr -> expr
    | EBOp : bop -> expr -> expr -> expr
    | ECond : expr -> expr -> expr -> expr
    | ELam : string -> ltype -> expr -> expr
    | EApp : expr -> expr -> expr.

(* Gamma *)
Definition gamma := string -> option ltype.

Definition empty : gamma := fun x => None.

Definition bind (x : string) (t : ltype) (g : gamma) : gamma :=
    fun y => if String.eqb x y then Some t else g y.

Lemma bind_correct : 
    forall (x : string) (t : ltype) (g : gamma),
    bind x t g x = Some t.
Proof.
    intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
    - reflexivity.
    - apply eqb_neq in eq. contradiction.
Qed.

Lemma bind_complete :
    forall (x x' : string) (t t' : ltype) (g : gamma),
    x' <> x -> (g x = Some t <-> bind x' t' g x = Some t). 
Proof.
    intros. unfold bind. apply eqb_neq in H. 
    rewrite H. split; intros; apply H0.
Qed.

Lemma rebind_correct : 
    forall (x : string) (t t' : ltype) (g : gamma),
    bind x t g = bind x t (bind x t' g).
Proof.
    intros. apply functional_extensionality. intros y.
    unfold bind. destruct ((x =? y)%string); reflexivity.
Qed.

Lemma bind_diff_comm : 
    forall (x y : string) (u v : ltype) (g : gamma),
    x <> y ->
    bind x u (bind y v g) = bind y v (bind x u g).
Proof.
    - intros. apply functional_extensionality. intros z.
        unfold bind. destruct ((x =? z)%string) eqn:eq.
        + apply eqb_eq in eq; subst.
            destruct ((y =? z)%string) eqn:eeq.
            * apply eqb_eq in eeq; subst. contradiction.
            * reflexivity.
        + apply eqb_neq in eq. destruct ((y =? z)%string) eqn:eeq; reflexivity.
Qed.

(* Static Semantics *)
Inductive checks (g : gamma) : expr -> ltype -> Prop :=
    | natchecks : forall (n : nat), checks g (ENat n) TNat
    | boolchecks : forall (b : bool), checks g (EBool b) TBool
    | varchecks : forall (x : string) (t : ltype), 
        g x = Some t -> checks g (EVar x) t
    | notchecks : forall (e : expr), 
        checks g e TBool -> checks g (ENot e) TBool
    | addchecks : forall (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp EAdd e1 e2) TNat
    | mulchecks : forall (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp EMul e1 e2) TNat
    | subchecks : forall (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp ESub e1 e2) TNat
    | eqchecks : forall (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp EEq e1 e2) TBool
    | lechecks : forall (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp ELe e1 e2) TBool
    | andchecks : forall (e1 e2 : expr),
        checks g e1 TBool -> checks g e2 TBool -> checks g (EBOp EAnd e1 e2) TBool
    | orchecks : forall (e1 e2 : expr),
        checks g e1 TBool -> checks g e2 TBool -> checks g (EBOp EOr e1 e2) TBool
    | condchecks : forall (e1 e2 e3 : expr) (t : ltype),
        checks g e1 TBool -> checks g e2 t -> checks g e3 t ->
        checks g (ECond e1 e2 e3) t
    | lamchecks : forall (x : string) (t t' : ltype) (e : expr),
        checks (bind x t g) e t' -> checks g (ELam x t e) (TArrow t t')
    | appchecks : forall (e1 e2 : expr) (t t' : ltype),
        checks g e1 (TArrow t t') -> checks g e2 t -> checks g (EApp e1 e2) t'.

(* Free Variables *)
Fixpoint fv (e : expr) : set string := 
    match e with
    | ENat _  => empty_set string
    | EBool _ => empty_set string
    | EVar x  => set_add string_dec x (empty_set string)
    | ENot e  => fv e
    | EBOp _ e1 e2 => set_union string_dec (fv e1) (fv e2)
    | ECond e1 e2 e3 => set_union string_dec (set_union string_dec (fv e1) (fv e2)) (fv e3)
    | ELam x _ e => set_diff string_dec (fv e) (set_add string_dec x (empty_set string))
    | EApp e1 e2 => set_union string_dec (fv e1) (fv e2)
    end.
        

Lemma bind_unfree_var :
    forall (e : expr) (x : string) (t' t : ltype) (g : gamma),
    ~ set_In x (fv e) ->
    checks g e t <-> checks (bind x t' g) e t.
Proof.
    induction e; split; intros; simpl in H; inversion H0; subst.
    - apply natchecks.
    - apply natchecks. 
    - apply boolchecks.
    - apply boolchecks.
    - apply varchecks.
        apply bind_complete.
        + unfold not in *; intros; subst.
            apply H. left. reflexivity.
        + apply H2.
    - apply varchecks. destruct ((x =? s)%string) eqn:eq.
        + apply eqb_eq in eq; subst.
            simpl in H. exfalso. apply H. left. reflexivity.
        + apply eqb_neq in eq. eapply bind_complete.
            * apply eq.
            * apply H2.
    - apply notchecks. apply (IHe x t' TBool g).
        + unfold not in *; intros.
            apply H. apply set_mem_correct1 with string_dec.
            simpl. apply set_mem_correct2. apply H1.
        + apply H2.
    - apply notchecks. eapply IHe.
        + apply H.
        + apply H2.
    - apply addchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
    - apply mulchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
    - apply subchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
    - apply eqchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
    - apply lechecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
        - unfold fv in H. fold fv in H.
        apply andchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
    - apply orchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H5.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H6.
    - apply addchecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply mulchecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply subchecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply eqchecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply lechecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply andchecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply orchecks.
        + eapply IHe1.
            * unfold not in *. intros. apply H.
                apply set_union_intro1. apply H1.
            * apply H5.
        + eapply IHe2.
            * unfold not in *. intros. apply H.
                apply set_union_intro2. apply H1.
            * apply H6.
    - apply condchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply set_union_intro.
                left. apply H1.
            * apply H4.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply set_union_intro.
                right. apply H1.
            * apply H6.
        + apply IHe3.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H7.
    - apply condchecks.
    + eapply IHe1.
        * unfold not in *. intros. apply H.
            apply set_union_intro1. 
            apply set_union_intro1.
            apply H1.
        * apply H4.
    + eapply IHe2.
        * unfold not in *. intros. apply H.
            apply set_union_intro1.
            apply set_union_intro2.
            apply H1.
        * apply H6.
    + eapply IHe3.
        * unfold not in *; intros. apply H.
            apply set_union_intro2.
            apply H1.
        * apply H7.
    - apply lamchecks.
        destruct ((x =? s)%string) eqn:eq.
        + apply eqb_eq in eq as xs; subst.
            rewrite <- rebind_correct.
            apply H5.
        + apply eqb_neq in eq as xs.
            pose proof bind_diff_comm.
            apply not_eq_sym in xs.
            eapply H1 in xs as nxs.
            rewrite nxs. apply IHe.
            * unfold not in *. intros.
                apply H. apply set_diff_intro.
                apply H2.
                unfold set_In.
                unfold not. intros.
                apply xs.
                inversion H3. apply H4.
                inversion H4. 
            * apply H5.
    - apply lamchecks.
        destruct ((x =? s)%string) eqn:eq.
        + apply eqb_eq in eq; subst.
            erewrite rebind_correct.
            apply H5.
        + apply eqb_neq in eq.
            eapply IHe.
            * unfold not in *. intros.
                apply H.
                apply set_diff_intro.
                apply H1.
                unfold set_In.
                unfold not. intros.
                apply eq. inversion H2; subst.
                reflexivity.
                inversion H3.
            * eapply bind_diff_comm in eq.
                rewrite eq. apply H5.
    - eapply appchecks.
        + apply IHe1.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                left. apply H1.
            * apply H3.
        + apply IHe2.
            * unfold not in *; intros.
                apply H.
                apply set_union_intro.
                right. apply H1.
            * apply H5.
    - eapply appchecks.
        + eapply IHe1.
            * unfold not in *. intros.
                apply H. apply set_union_intro1.
                apply H1.
            * apply H3.
        + eapply IHe2.
            * unfold not in *. intros.
                apply H. apply set_union_intro2.
                apply H1.
            * apply H5.
Qed.

(* Capture-avoiding Substitution *)
Inductive sub (x : string) (s : expr) : expr -> expr -> Prop :=
    | natsub : forall (n : nat), sub x s (ENat n) (ENat n)
    | boolsub : forall (b : bool), sub x s (EBool b) (EBool b)
    | hitsub : sub x s (EVar x) s
    | misssub : forall (y : string), y <> x -> sub x s (EVar y) (EVar y)
    | notsub : forall (e e' : expr), sub x s e e' -> sub x s (ENot e) (ENot e')
    | bopsub : forall (op : bop) (e1 e1' e2 e2' : expr),
        sub x s e1 e1' -> sub x s e2 e2' -> sub x s (EBOp op e1 e2) (EBOp op e1' e2')
    | condsub : forall (e1 e1' e2 e2' e3 e3' : expr),
        sub x s e1 e1' -> sub x s e2 e2' -> sub x s e3 e3' ->
        sub x s (ECond e1 e2 e3) (ECond e1' e2' e3')
    | appsub : forall (e1 e1' e2 e2' : expr),
        sub x s e1 e1' -> sub x s e2 e2' -> sub x s (EApp e1 e2) (EApp e1' e2')
    | lam_bound_sub : forall (t : ltype) (e : expr),
        sub x s (ELam x t e) (ELam x t e)
    | lam_notfree_sub : forall (y : string) (t : ltype) (e e' : expr),
        x <> y -> set_mem string_dec y (fv s) = false -> 
        sub x s e e' -> sub x s (ELam y t e) (ELam y t e')
    | lam_free_sub : forall (y z : string) (t : ltype) (e e' e'' : expr),
        x <> y -> x <> z -> y <> z ->
        set_mem string_dec y (fv s) = true -> 
        set_mem string_dec z (fv s) = false ->
        set_mem string_dec z (fv e) = false ->
        sub y (EVar z) e e' -> 
        sub x s e' e'' -> 
        sub x s (ELam y t e) (ELam z t e'').

Axiom sub_exists : forall (x : string) (s e : expr),
    exists e', sub x s e e'.

Lemma sub_free : forall (x : string) (s e e' : expr),
    ~ set_In x (fv s) -> sub x s e e' ->
    ~ set_In x (fv e').
Proof.
    intros. induction H0; unfold not; 
    intros; simpl in *; try assumption.
    - contradiction.
    - destruct H1; contradiction.
    - apply IHsub; assumption.
    - apply set_union_elim in H0 as [h1 | h2].
        + apply IHsub1; assumption.
        + apply IHsub2; assumption.
    - apply set_union_elim in H0 as [H0 | h3].
        + apply set_union_elim in H0 as [h1 | h2].
            * apply IHsub1; assumption.
            * apply IHsub2; assumption.
        + apply IHsub3; assumption.
    - apply set_union_elim in H0 as [h1 | h2].
        + apply IHsub1; assumption.
        + apply IHsub2; assumption.
    - apply set_diff_iff in H0 as [_ h].
        apply h. constructor. reflexivity.
    - apply set_mem_complete1 in H1.
        eapply set_diff_iff in H3 as [h1 h2].
        apply IHsub; assumption.
    - apply set_mem_correct1 in H3.
        apply set_mem_complete1 in H4.
        apply set_mem_complete1 in H5.
        apply set_diff_iff in H6 as [h1 h2].
        apply IHsub2; assumption.
Qed.

Lemma sub_preserves_free : forall (x z : string) (s e e' : expr),
    x <> z -> sub x s e e' -> set_In z (fv e) -> set_In z (fv e').
Proof.
    intros. induction H0; simpl in *; try assumption.
    - destruct H1; contradiction.
    - apply IHsub; assumption.
    - apply set_union_intro.
        apply set_union_elim in H1. 
        destruct H1.
        + left. apply IHsub1; assumption.
        + right. apply IHsub2; assumption.
    - apply set_union_intro.
        apply set_union_elim in H1 as [H1 | H1].
        + left. apply set_union_intro.
            apply set_union_elim in H1 as [H1 | H1].
            * left. apply IHsub1; assumption.
            * right. apply IHsub2; assumption.
        + right. apply IHsub3; assumption.
    - apply set_union_intro. 
        apply set_union_elim in H1 as [H1 | H1].
        + left. apply IHsub1; assumption.
        + right. apply IHsub2; assumption.
    - apply set_diff_iff in H1 as [h1 h2].
        apply set_diff_intro.
        + apply IHsub; assumption.
        + assumption.
    - apply set_diff_iff in H1 as [h1 h2].
        apply set_diff_iff. split.
        + apply IHsub2.
            * apply H.
            * apply IHsub1.
                unfold not. intros.
                apply h2. constructor.
                assumption. assumption.
        + unfold not. intros.
            apply set_mem_complete1 in H6.
            apply H6. inversion H1; subst.
            * assumption.
            * inversion H7. 
Qed.

Lemma sub_entails_free : forall (x z : string) (s e e' : expr),
    x <> z -> ~ set_In z (fv s) -> sub x s e e' ->
    set_In z (fv e') -> set_In z (fv e).
Proof.
    intros. induction H1; simpl in *; 
    try contradiction; try assumption.
    - apply IHsub; assumption.
    - apply set_union_intro.
        apply set_union_elim in H2 as [H2 | H2].
        + left. apply IHsub1; assumption.
        + right. apply IHsub2; assumption.
    - apply set_union_intro. apply set_union_elim in H2 as [H2 | H2].
        + left. apply set_union_intro.
            apply set_union_elim in H2 as [H2 | H2].
            * left. apply IHsub1; assumption.
            * right. apply IHsub2; assumption.
        + right. apply IHsub3; assumption.
    - apply set_union_intro. apply set_union_elim in H2 as [H2 | H2].
        + left. apply IHsub1; assumption.
        + right. apply IHsub2; assumption.
    - apply set_diff_iff in H2 as [h1 h2].
        apply set_diff_intro.
        + apply IHsub; assumption.
        + assumption.
    - apply set_diff_iff in H2 as [h1 h2].
        assert (y <> z).
        unfold not. intros; subst.
        apply set_mem_correct1 in H5.
        contradiction.
        apply set_diff_intro.
        + apply IHsub1; try assumption.
            apply IHsub2; assumption.
        + unfold not. intros.
            apply H2. inversion H8.
            * assumption.
            * inversion H9.
Qed.

(* Dynamic Semantics *)
Inductive step : expr -> expr -> Prop :=
    | notstep : forall (b : bool),
        step (ENot (EBool b)) (EBool (negb b))
    | innerstep : forall (e e' : expr),
        step e e' -> step (ENot e) (ENot e')
    | addstep : forall (n1 n2 : nat),
        step (EBOp EAdd (ENat n1) (ENat n2)) (ENat (n1 + n2))
    | mulstep : forall (n1 n2 : nat),
        step (EBOp EMul (ENat n1) (ENat n2)) (ENat (n1 * n2))
    | substep : forall (n1 n2 : nat),
        step (EBOp ESub (ENat n1) (ENat n2)) (ENat (n1 - n2))
    | eqstep : forall (n1 n2 : nat),
        step (EBOp EEq (ENat n1) (ENat n2)) (EBool (n1 =? n2))
    | lestep : forall (n1 n2 : nat),
        step (EBOp ELe (ENat n1) (ENat n2)) (EBool (n1 <? n2))
    | andstep : forall (b1 b2 : bool),
        step (EBOp EAnd (EBool b1) (EBool b2)) (EBool (andb b1  b2))
    | orstep : forall (b1 b2 : bool),
        step (EBOp EOr (EBool b1) (EBool b2)) (EBool (orb b1  b2))
    | right_nat_step : forall (op : bop) (n : nat) (e e' : expr),
        step e e' -> step (EBOp op (ENat n) e) (EBOp op (ENat n) e')
    | right_bool_step : forall (op : bop) (b : bool) (e e' : expr),
        step e e' -> step (EBOp op (EBool b) e) (EBOp op (EBool b) e')
    | left_bop_step : forall (op : bop) (e1 e1' e2 : expr),
        step e1 e1' -> step (EBOp op e1 e2) (EBOp op e1' e2)
    | truestep : forall (e2 e3 : expr),
        step (ECond (EBool true) e2 e3) e2
    | falsestep : forall (e2 e3 : expr),
        step (ECond (EBool false) e2 e3) e3
    | condstep : forall (e1 e1' e2 e3 : expr),
        step e1 e1' -> step (ECond e1 e2 e3) (ECond e1' e2 e3)
    | appstep : forall (e1 e1' e2 : expr),
        step e1 e1' -> step (EApp e1 e2) (EApp e1' e2)
    | lamstep : forall (x : string) (t : ltype) (e1 e2 e3 : expr),
        sub x e2 e1 e3 -> step (EApp (ELam x t e1) e2) e3.
    
(* Values *)
Inductive value : expr -> Prop :=
    | natvalue : forall (n : nat), value (ENat n)
    | boolvalue : forall (b : bool), value (EBool b)
    | lamvalue : forall (x : string) (t : ltype) (e : expr),
        value (ELam x t e).

Definition bool_canonical_forms (v : expr) : Prop :=
    value v -> checks empty v TBool -> exists (b : bool), v = EBool b.

Lemma bool_canonical_forms_holds : forall v,
    bool_canonical_forms v.
Proof.
    unfold bool_canonical_forms. intros.
    inversion H; inversion H0; subst;
    try discriminate H2;
    try discriminate H3;
    try discriminate H4;
    try discriminate H5.
    exists b0. symmetry. apply H2.
Qed.

Definition nat_canonical_forms (v : expr) : Prop := 
    value v -> checks empty v TNat -> exists (n : nat), v = ENat n.

Lemma nat_canonical_forms_holds : forall v,
    nat_canonical_forms v.
Proof.
    unfold nat_canonical_forms. intros.
    inversion H; inversion H0; subst;
    try discriminate H2;
    try discriminate H3;
    try discriminate H4;
    try discriminate H5.
    exists n0. symmetry. apply H2.
Qed.

Definition lam_canonical_forms (v : expr) : Prop :=
    forall (t t' : ltype),
    value v -> checks empty v (TArrow t t') -> 
    exists (x : string) (e : expr), v = ELam x t e.

Lemma lam_canonical_forms_holds : forall v,
    lam_canonical_forms v.
Proof.
    unfold lam_canonical_forms. intros.
    inversion H; inversion H0; subst;
    try discriminate H2;
    try discriminate H3;
    try discriminate H4;
    try discriminate H5.
    exists x0. exists e0. symmetry.
    apply H3.
Qed.

Lemma canonical_forms : forall v,
    bool_canonical_forms v /\
    nat_canonical_forms v /\
    lam_canonical_forms v.
Proof.
    intros. split.
    - apply bool_canonical_forms_holds.
    - split.
        + apply nat_canonical_forms_holds.
        + apply lam_canonical_forms_holds.
Qed.
    
Definition progress (e : expr) (t : ltype) : Prop := 
    checks empty e t -> value e \/ exists (e' : expr), step e e'.

Theorem progress_holds : forall (e : expr) (t : ltype), progress e t.
Proof.
    unfold progress. 
    induction e; intros.
    - left. apply natvalue.
    - left. apply boolvalue.
    - inversion H. inversion H1.
    - right. inversion H; subst.
        apply IHe in H1 as h1. destruct h1 as [h | [e' h]].
        + apply (bool_canonical_forms_holds e h) in H1 as [b cfh]; subst.
        exists (EBool (negb b)). apply notstep.
        + exists (ENot e'). apply innerstep. apply h.
    - right. inversion H; subst; apply IHe1 in H4 as h1; apply IHe2 in H5 as h2; 
        destruct h1; destruct h2; 
        try (apply (nat_canonical_forms_holds e1 H0) in H4 as [n1 v1]; subst;
        apply (nat_canonical_forms_holds e2 H1) in H5 as [n2 v2]; subst);
        try (apply (nat_canonical_forms_holds e1 H0) in H4 as [n1 v1]; subst;
            destruct H1 as [e2' h]);
        try (apply (bool_canonical_forms_holds e1 H0) in H4 as [b1 v1]; subst;
        apply (bool_canonical_forms_holds e2 H1) in H5 as [b2 v2]; subst);
        try (apply (bool_canonical_forms_holds e1 H0) in H4 as [b1 v1]; subst;
            destruct H1 as [e2' h]);
        try (destruct H0 as [e1' h]).
            + exists (ENat (n1 + n2)). apply addstep.
            + exists (EBOp EAdd (ENat n1) e2'). apply right_nat_step. apply h.
            + exists (EBOp EAdd e1' e2). apply left_bop_step. apply h.
            + exists (EBOp EAdd e1' e2). apply left_bop_step. apply h.
            + exists (ENat (n1 * n2)). apply mulstep.
            + exists (EBOp EMul (ENat n1) e2'). apply right_nat_step. apply h.
            + exists (EBOp EMul e1' e2). apply left_bop_step. apply h.
            + exists (EBOp EMul e1' e2). apply left_bop_step. apply h.
            + exists (ENat (n1 - n2)). apply substep.
            + exists (EBOp ESub (ENat n1) e2'). apply right_nat_step. apply h.
            + exists (EBOp ESub e1' e2). apply left_bop_step. apply h.
            + exists (EBOp ESub e1' e2). apply left_bop_step. apply h.
            + exists (EBool (n1 =? n2)). apply eqstep.
            + exists (EBOp EEq (ENat n1) e2'). apply right_nat_step. apply h.
            + exists (EBOp EEq e1' e2). apply left_bop_step. apply h.
            + exists (EBOp EEq e1' e2). apply left_bop_step. apply h.
            + exists (EBool (n1 <? n2)). apply lestep.
            + exists (EBOp ELe (ENat n1) e2'). apply right_nat_step. apply h.
            + exists (EBOp ELe e1' e2). apply left_bop_step. apply h.
            + exists (EBOp ELe e1' e2). apply left_bop_step. apply h.
            + exists (EBool (andb b1 b2)). apply andstep.
            + exists (EBOp EAnd (EBool b1) e2'). apply right_bool_step. apply h.
            + exists (EBOp EAnd e1' e2). apply left_bop_step. apply h.
            + exists (EBOp EAnd e1' e2). apply left_bop_step. apply h.
            + exists (EBool (orb b1 b2)). apply orstep.
            + exists (EBOp EOr (EBool b1) e2'). apply right_bool_step. apply h.
            + exists (EBOp EOr e1' e2). apply left_bop_step. apply h.
            + exists (EBOp EOr e1' e2). apply left_bop_step. apply h.
    - right. inversion H; subst; 
        apply IHe1 in H3 as h1; apply IHe2 in H5 as h2; apply IHe3 in H6 as h3; subst.
        destruct h1 as [h1 | [e1' h1]].
        + apply (bool_canonical_forms_holds e1 h1) in H3 as [b v1].
            destruct b; subst.
            * exists e2. apply truestep.
            * exists e3. apply falsestep.
        + exists (ECond e1' e2 e3). apply condstep. apply h1.
    - left. apply lamvalue.
    - right. inversion H; subst;
        apply IHe1 in H2 as h1; apply IHe2 in H4 as h2; subst.
        destruct h1 as [h1 | [e1' h1]].
        + apply (lam_canonical_forms_holds e1 t0 t h1) in H2 as [x [e v1]]; subst.
            pose proof (sub_exists x e2 e) as [e'' hsub].
            exists e''. apply lamstep. apply hsub.
        + exists (EApp e1' e2). apply appstep. apply h1.
Qed.
    
Definition substitution_lemma 
    (x : string) (s e e' : expr) :=
    sub x s e e' ->
    forall (t t' : ltype) (g : gamma),
    checks (bind x t' g) e t -> 
    checks g s t' -> 
    checks g e' t.

Lemma substitution_lemma_holds : 
    forall (x : string) (s e e' : expr),
    substitution_lemma x s e e'.
Proof.
    unfold substitution_lemma.
    intros x s e e' HS.
    dependent induction HS; intros.
    - inversion H; subst. apply natchecks.
    - inversion H; subst. apply boolchecks.
    - inversion H; subst. rewrite bind_correct in H2.
        injection H2 as h2; subst. assumption.
    - inversion H0; subst. apply bind_complete in H3.
        + apply varchecks; assumption.
        + auto.
    - inversion H; subst. apply notchecks. eapply IHHS.
        + apply H2.
        + assumption.
    - inversion H; subst.
        + apply addchecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
        + apply mulchecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
        + apply subchecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
        + apply eqchecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
        + apply lechecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
        + apply andchecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
        + apply orchecks.
            * eapply IHHS1. apply H5. assumption.
            * eapply IHHS2. apply H6. assumption.
    - inversion H; subst. apply condchecks.
        + eapply IHHS1.
            * apply H4.
            * assumption.
        + eapply IHHS2.
            * apply H6.
            * assumption.
        + eapply IHHS3.
            * apply H7.
            * assumption.
    - inversion H; subst. eapply appchecks.
        + eapply IHHS1.
            * apply H3.
            * assumption.
        + eapply IHHS2.
            * apply H5.
            * assumption.
    - inversion H; subst. apply lamchecks.
        erewrite rebind_correct. apply H5.
    - inversion H1; subst. apply lamchecks.
        eapply IHHS.
        + pose proof bind_diff_comm.
            eapply H3 in H as h.
            rewrite h. apply H7.
        + apply set_mem_complete1 in H0.
            pose proof bind_unfree_var.
            eapply (H3 s y t t' g); assumption.
    - inversion H5; subst. apply lamchecks.
        eapply IHHS2.
        + pose proof bind_diff_comm.
            eapply H7 in H0 as h0.
            rewrite h0.
            eapply (IHHS1 t'0 t).
            * pose proof rebind_correct.
                eapply H7 in H1 as h1.
                rewrite h1.
                pose proof bind_unfree_var.
                eapply (H9 e z t t'0 (bind y t (bind x t' g))).
                apply set_mem_complete1 in H4.
                assumption. assumption.
            * apply varchecks. unfold bind.
                destruct ((z =? z)%string) eqn:eq.
                reflexivity.
                simpl in eq.
                apply eqb_neq in eq. contradiction.
        + apply set_mem_complete1 in H3.
            pose proof bind_unfree_var.
            eapply (H7 s z t t' g) in H3.
            apply H3. assumption.
Qed.    

Definition preservation (e e' : expr) : Prop :=
    step e e' -> forall (t : ltype),
    checks empty e t -> checks empty e' t.

Theorem preservation_holds : forall (e e' : expr),
    preservation e e'.
Proof.
    unfold preservation. intros e e' H.
    induction H; intros.
    - inversion H; subst. apply boolchecks.
    - inversion H0; subst. apply notchecks.
        apply IHstep. assumption.
    - inversion H; subst. apply natchecks.
    - inversion H; subst. apply natchecks.
    - inversion H; subst. apply natchecks.
    - inversion H; subst. apply boolchecks.
    - inversion H; subst. apply boolchecks.
    - inversion H; subst. apply boolchecks.
    - inversion H; subst. apply boolchecks.
    - inversion H0; inversion H5; 
        subst; constructor; auto.
    - inversion H0; inversion H5; 
        subst; constructor; auto.
    - inversion H0; subst; constructor; auto.
    - inversion H; subst. assumption.
    - inversion H; subst. assumption.
    - inversion H0; subst. apply condchecks; auto.
    - inversion H0; subst. eapply appchecks.
        + apply IHstep. apply H3.
        + assumption.
    - inversion H0; subst. inversion H3; subst.
        eapply substitution_lemma_holds.
        + apply H.
        + apply H2.
        + assumption.
Qed.

(* Normalization *)

Require Import Coq.Logic.Classical_Pred_Type.

Inductive halts (e : expr) : Prop :=
    | halts_value : value e -> halts e
    | halts_step : forall (e' : expr),
        step e e' -> halts e' -> halts e.

Lemma value_halts : forall (v : expr),
    value v <-> ~ exists (e : expr), step v e.
Proof.
    intros v; split.
    - intros Hv; inversion Hv; subst;
        intros [e' He]; inversion He.
    - intros NHe. eapply not_ex_all_not in NHe. admit.
Admitted.

Lemma step_unique : forall (e e' e'' : expr),
    step e e' -> step e e'' -> e' = e''.
Proof.
    induction e; intros e' e'' H' H''.
    - inversion H'; inversion H''; subst.
    - inversion H'; inversion H''; subst.
    - inversion H'; inversion H''; subst.
    - inversion H'; inversion H''; subst.
        + injection H2; intros; subst. reflexivity.
        + admit.
Admitted.

Lemma halts_red : forall (e e' : expr),
    step e e' -> halts e -> halts e'.
Proof.
    intros. inversion H0; subst.
    - apply value_halts in H1 as H'.
        exfalso. apply H'. exists e'. assumption.
    - pose proof (step_unique e e' e'0 H H1) as eq; 
        subst. assumption.
Qed.

Fail Inductive R : ltype -> expr -> Prop :=
| Rnat : forall (e : expr),
    checks empty e TNat ->
    halts e -> 
    R TNat e
| Rbool : forall (e : expr),
    checks empty e TBool -> 
    halts e -> 
    R TBool e
| Rarrow : forall (e : expr) (t1 t2 : ltype),
    checks empty e (TArrow t1 t2) -> 
    halts e ->
    (forall (e' : expr), R t1 e' -> R t2 (EApp e e')) ->
    R (TArrow t1 t2) e.

(* This definition was borrowed from Software Foundations,
    after I found that Coq rejected the above. *)
Fixpoint R (t : ltype) (e : expr) {struct t} : Prop :=
    checks empty e t /\ halts e /\
    match t with
    | TNat => True 
    | TBool => True
    | TArrow t1 t2 => 
        forall (e' : expr), R t1 e' -> R t2 (EApp e e')
    end.

Lemma R_halts : forall (t : ltype) (e : expr), R t e -> halts e.
Proof.
    dependent induction t; intros e H; unfold R in H;
    destruct H as [chks [hlts ih]]; try assumption.
Qed.

Lemma R_checks : 
    forall (t : ltype) (e : expr), 
    R t e -> checks empty e t.
Proof.
    intros. destruct t; unfold R in *; fold R in *;
    destruct H as [chks [hlts ih]]; try assumption.
Qed.

(* Parsing Lemma in TAPL... *)
Lemma R_step' :
    forall (t : ltype) (e e' : expr),
    checks empty e t -> step e e' ->
    R t e <-> R t e'.
Proof.
    dependent induction t; unfold R; split; intros.
    - destruct H1 as [chks [hlts ih]]. split.
        + eapply preservation_holds.
            * apply H0.
            * assumption.
        + split; try trivial. eapply halts_red.
            * apply H0.
            * assumption.
    - destruct H1 as [chks [hlts ih]]. split.
        + assumption.
        + split; try trivial. eapply halts_step.
            * apply H0.
            * assumption.
    - destruct H1 as [chks [hlts ih]]. split.
        + eapply preservation_holds.
            * apply H0.
            * assumption.
        + split; try trivial. eapply halts_red.
            * apply H0.
            * assumption.
    - destruct H1 as [chks [hlts ih]]. split.
        + assumption.
        + split; try trivial. eapply halts_step.
            * apply H0.
            * assumption.
    - destruct H1 as [chks [hlts ih]]. split.
        { eapply preservation_holds.
            - apply H0.
            - assumption. }
        { split; try trivial. eapply halts_red.
            - apply H0.
            - assumption.
            - fold R in *. intros.
                specialize ih with (e' := e'0).
                apply ih in H1. eapply IHt2.
                + apply R_checks in H1.
                    eapply preservation_holds.
                    * eapply appstep. apply H0.
                    * assumption.
                + apply appstep. admit. }
    - destruct H1 as [chks [hlts ih]]. split.
        + assumption.
        + split; try trivial. eapply halts_step.
            * apply H0.
            * assumption.
            * fold R in *. admit.
Admitted.  