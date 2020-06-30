Set Warnings "-notation-overridden,-parsing".
Require Import String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListSet.
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
    | ELam x _ e => set_remove string_dec x (fv e)
    | EApp e1 e2 => set_union string_dec (fv e1) (fv e2)
    end.

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
        sub x s e e' -> sub x s (ELam y t e) (ELam y t e').

Lemma sub_exists : forall (x : string) (s e : expr),
    exists e', sub x s e e'.
Proof.
    intros. induction e.
    - exists (ENat n). apply natsub.
    - exists (EBool b). apply boolsub.
    - destruct (String.eqb x s0) eqn:h.
        + apply String.eqb_eq in h; subst. exists s.
            apply hitsub.
        + rewrite String.eqb_sym in h. 
            apply String.eqb_neq in h. exists (EVar s0).
            apply misssub. apply h.
    - destruct IHe as [e' h]. exists (ENot e').
        apply notsub. apply h.
    - destruct IHe1 as [e1' h1]. destruct IHe2 as [e2' h2].
        exists (EBOp b e1' e2'). apply bopsub.
        apply h1. apply h2.
    - destruct IHe1 as [e1' h1]. 
        destruct IHe2 as [e2' h2]. destruct IHe3 as [e3' h3].
        exists (ECond e1' e2' e3'). apply condsub.
        apply h1. apply h2. apply h3.
    - destruct IHe as [e' h']. destruct (String.eqb x s0) eqn:h.
        + apply String.eqb_eq in h. subst.
            exists (ELam s0 l e). apply lam_bound_sub.
        + rewrite String.eqb_sym in h. 
            apply String.eqb_neq in h.
Admitted.

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
              assert (hsub: exists e3, sub x e2 e e3).
 Admitted.
    

Definition preservation (e e' : expr) (t : ltype) : Prop :=
    step e e' -> checks empty e t -> checks empty e' t.

Theorem preservation_holds : forall (e e' : expr) (t : ltype),
    preservation e e' t.
Proof.
Admitted.
    