(* The Simply-Typed Lambda Calculus with minimal extensions,
    with unit, pairs, and either types. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Definition id := string.

Inductive type : Type := 
    | TUnit
    | TFun (t1 t2 : type)
    | TPair (t1 t2 : type)
    | TEither (t1 t2 : type).

Fixpoint type_eqb (a b : type) : bool :=
        match a, b with
        | TUnit, TUnit => true
        | TFun a1 a2, TFun b1 b2 
        | TPair a1 a2, TPair b1 b2
        | TEither a1 a2, TEither b1 b2 => type_eqb a1 b1 && type_eqb a2 b2
        | _, _ => false
        end.

Theorem type_eq_refl :
    forall (a b : type), a = b <-> type_eqb a b = true.
Proof.
    induction a; destruct b; split; intros;
    try reflexivity; try inversion H; subst;
    simpl in *;
    try (apply andb_true_iff; split;
        try (apply IHa1; reflexivity);
        try (apply IHa2; reflexivity));
    try (apply andb_true_iff in H as [H1' H2'];
        apply IHa1 in H1'; apply IHa2 in H2'; 
        subst; reflexivity).
Qed.

Inductive pattern : Type :=
    | PWild
    | PVar (x : id)
    | PUnit
    | PPair (p1 p2 : pattern)
    | PLeft (t1 t2 : type) (p : pattern)
    | PRight (t1 t2 : type) (p : pattern).

Inductive expr : Type :=
    | EUnit
    | EVar (x : id)
    | EFun (p : pattern) (t : type) (e : expr)
    | EApp (e1 e2 : expr)
    | EPair (e1 e2 : expr)
    | EProj (e : expr) (n : nat)
    | ELeft (t1 t2 : type) (e : expr)
    | ERight (t1 t2 : type) (e : expr)
    | EMatch (e : expr) (cases : list (pattern * expr)).

Inductive value : Type :=
    | VUnit
    | VFun (p : pattern) (t : type) (e : expr)
    | VPair (v1 v2 : value)
    | VLeft (t1 t2 : type) (v : value)
    | VRight (t1 t2 : type) (v : value).

Inductive instance : pattern -> value -> Prop :=
    | instance_wild : forall (v : value), instance PWild v
    | instance_var : forall (x : id) (v : value), instance (PVar x) v
    | instance_unit : instance PUnit VUnit
    | instance_pair : forall (p1 p2 : pattern) (v1 v2 : value),
        instance p1 v1 -> instance p2 v2 -> 
        instance (PPair p1 p2) (VPair v1 v2)
    | instance_left : forall (t1 t2 : type) (p : pattern) (v : value),
        instance p v -> instance (PLeft t1 t2 p) (VLeft t1 t2 v)
    | instance_right : forall (t1 t2 : type) (p : pattern) (v : value),
        instance p v -> instance (PRight t1 t2 p) (VRight t1 t2 v).

Fixpoint instanceb (p : pattern) (v : value) : bool :=
    match p, v with
    | PWild, _
    | PVar _, _
    | PUnit, VUnit => true
    | PPair p1 p2, VPair v1 v2 => instanceb p1 v1 && instanceb p2 v2
    | PLeft pt1 pt2 p, VLeft vt1 vt2 v
    | PRight pt1 pt2 p, VRight vt1 vt2 v => 
        type_eqb pt1 vt1 && type_eqb pt2 vt2 && instanceb p v
    | _, _ => false
    end.

Theorem instance_refl : forall (p : pattern) (v : value),
    instance p v <-> instanceb p v = true.
Proof.
    induction p; destruct v; split; intros; 
    try reflexivity; try constructor;
    try discriminate H; try inversion H; 
    subst; simpl in *.
    - apply IHp1 in H3. apply IHp2 in H5.
        rewrite H3. rewrite H5. reflexivity.
    - apply IHp1. apply andb_true_iff in H as [H2 _].
        assumption.
    - apply andb_true_iff in H as [_ H2].
        apply IHp2. assumption.
    - apply andb_true_iff. split.
        + apply andb_true_iff. split.
            * apply type_eq_refl. reflexivity.
            * apply type_eq_refl. reflexivity.
        + apply IHp. assumption.
    - apply andb_true_iff in H as [H1'' H3'].
        apply andb_true_iff in H1'' as [H1' H2'].
        apply type_eq_refl in H1'.
        apply type_eq_refl in H2'.
        subst. apply IHp in H3'.
        constructor. assumption.
    - apply andb_true_iff. split.
        + apply andb_true_iff. split.
            * apply type_eq_refl. reflexivity.
            * apply type_eq_refl. reflexivity.
        + apply IHp. assumption.
    - apply andb_true_iff in H as [H1'' H3'].
        apply andb_true_iff in H1'' as [H1' H2'].
        apply type_eq_refl in H1'.
        apply type_eq_refl in H2'.
        subst. apply IHp in H3'.
        constructor. assumption.
Qed.

