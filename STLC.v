Set Warnings "-notation-overridden,-parsing".
Require Import String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
(* Require Import Ascii. *)
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.
(* Require Import List Setoid Permutation Sorted Orders. *)
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalNat.
Require Import Coq.Numbers.DecimalString.
Require Import Recdef.
Require Import Omega.

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

Lemma fv_nodup : forall (e : expr), NoDup (fv e).
Proof. 
    induction e; simpl; try apply NoDup_nil.
    - apply NoDup_cons.
        + unfold not. intros. inversion H.
        + apply NoDup_nil.
    - apply IHe.
    - apply (set_union_nodup string_dec IHe1 IHe2).
    - apply set_union_nodup.
        + apply (set_union_nodup string_dec IHe1 IHe2).
        + apply IHe3.
    - apply (set_remove_nodup string_dec s IHe).
    - apply (set_union_nodup string_dec IHe1 IHe2).
Qed.

Lemma union_empty : forall (x y : set string),
    set_union string_dec x y = empty_set string -> x = empty_set string /\ y = empty_set string.
Proof.
    intros [] []; intros; split; try reflexivity.
    - simpl in H. exfalso. apply set_add_not_empty in H. apply H.
    - simpl in H. apply H.
    - simpl in H. exfalso. apply set_add_not_empty in H. apply H.
    - simpl in H. exfalso. apply set_add_not_empty in H. apply H.
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
        x <> y -> x <> z ->
        set_mem string_dec z (fv s) = false ->
        set_mem string_dec z (fv e) = false ->
        sub y (EVar z) e e' -> sub x s e' e'' -> 
        sub x s (ELam y t e) (ELam z t e'').


Definition var_low_bound := 97.  (* inclusive *)
Definition var_upp_bound := 123. (* exclusive *)
Definition alph_size := 26.

Definition nat_to_letter (n : nat) : string := 
    String.String (ascii_of_nat (n + var_low_bound)) EmptyString.

Fixpoint fancy_nat_to_string (n : nat) (m : nat) {struct m} : string :=
    match m with
    | 0 => nat_to_letter n
    | S m' =>
        let quot   := n / alph_size in
        let remain := n mod alph_size in
        let prefix := 
            if 0 <? quot
            then fancy_nat_to_string (quot-1) m'
            else EmptyString in
        prefix ++ (nat_to_letter remain)
    end.

Fixpoint fancy_string_to_nat (s : string) : nat :=
    match s with
    | EmptyString  => 0
    | String c EmptyString => (nat_of_ascii c) - var_low_bound
    | String c s'  =>
        let cn  := ((nat_of_ascii c) - var_low_bound) in
        let aug := (cn + 1) * alph_size ^ (String.length s') in
        aug + (fancy_string_to_nat s')
    end.

Fixpoint nat_to_string' (n : nat) : string :=
    match n with
    | 0 => EmptyString
    | S k => String (ascii_of_nat n) (nat_to_string' k)
    end.

Definition nat_to_string (n : nat) : string := 
    NilEmpty.string_of_uint (Nat.to_uint n).

(* No way, I am not gonna do 121 cases,
    to prove a library function correct.  *)
Axiom string_of_uint_inj : forall u1 u2,
    NilEmpty.string_of_uint u1 = NilEmpty.string_of_uint u2
    -> u1 = u2.

Lemma nat_to_string_inj : forall (n1 n2 : nat),
    nat_to_string n1 = nat_to_string n2 -> n1 = n2.
Proof.
    intros. unfold nat_to_string in H.
    apply Unsigned.to_uint_inj.
    apply string_of_uint_inj. apply H.
Qed.        

(* bag must be sorted and have no duplicates *)
Fixpoint first_new_string (n : nat) (bag : set string) : string :=
    match bag with
    | nil => nat_to_string n
    | w::tail =>
        let word := nat_to_string n in
        if String.eqb w word
        then first_new_string (S n) tail
        else if set_mem string_dec word tail
        then first_new_string (S n) tail
        else word
    end.

(* Lemma stupid_string : forall (c : ascii) (s : string), s <> String c s.
Proof.
    unfold not. intros. induction s.
    - discriminate H.
    - apply IHs. injection H as h; subst. apply H.
Qed.

Lemma first_new_string_mono : forall (bag : set string) (n : nat),
    nat_to_string n <> first_new_string (S n) bag.
Proof.
    induction bag; induction n; unfold not; intros.
    - inversion H.
    - apply IHn.
    unfold not. intros. induction H.
    induction bag; unfold not; intros.
    - simpl in H. apply stupid_string in H. apply H.
    - specialize IHbag with n.
        apply IHbag. unfold first_new_string in H.
        destruct ((a =? nat_to_string (S n))%string) eqn:eq; 
        fold first_new_string in *. *)

(* Example with nats *)
Module NatOrder <: TotalLeBool.
Definition t := nat.
Fixpoint leb x y :=
    match x, y with
    | 0, _ => true
    | _, 0 => false
    | S x', S y' => leb x' y'
    end.
Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
Proof. 
    induction a1; induction a2; try (constructor; reflexivity).
    - specialize IHa1 with a2.
        destruct IHa1 as [h1 | h1]; 
        destruct IHa2 as [h2 | h2]; simpl;
        constructor; apply h1.
Qed.

Inductive lebr : nat -> nat -> Prop :=
    | lebz : forall (n : nat),
        lebr 0 n
    | lebs : forall (n m : nat),
        lebr n m -> lebr (S n) (S m).
Theorem lebr_total : forall (n m : nat), lebr n m \/ lebr m n.
Proof.
    induction n; induction m; try (left; apply lebz).
    - right. apply lebz.
    - specialize IHn with m.
        destruct IHn as [h1 | h1]; destruct IHm as [h2 | h2]. 
        + left. apply lebs. apply h1.
        + left. apply lebs. apply h1.
        + right. apply lebs. apply h1.
        + right. apply lebs. apply h1.
Qed.

Theorem leb_refl : forall (n1 n2 : nat),
    leb n1 n2 = true <-> lebr n1 n2.
Proof.
    induction n1; induction n2; split; intros.
    - apply lebz.
    - reflexivity.
    - apply lebz.
    - reflexivity.
    - discriminate H.
    - inversion H.
    - apply lebs. apply IHn1.
        simpl in H. apply H.
    - simpl. apply IHn1. inversion H; subst. apply H2.
Qed.

End NatOrder.

Module NatSort := Sort NatOrder.

Example SimpleMergeExample := NatSort.sort [5;3;6;1;8;6;0].
  
Check (Sorted NatOrder.lebr nil).

Module AsciiOrder <: TotalLeBool.
Definition t := ascii.

Definition ascii_to_list (a b : ascii) : list (bool * bool) :=
    match a, b with
    | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
         Ascii b0 b1 b2 b3 b4 b5 b6 b7 => 
         [(a0,b0);(a1,b1);(a2,b2);(a3,b3);(a4,b4);(a5,b5);(a6,b6);(a7,b7)]
    end.

Fixpoint leb' (x : list (bool * bool)) := 
    match x with
    | [] => true
    | (false,true)::_ => true
    | (false,false)::y => leb' y
    | (true,true)::y => leb' y
    | (true,false)::_ => false
    end.

Definition leb x y := leb' (ascii_to_list x y).

Fixpoint flip (x : (list (bool * bool))) : list (bool * bool) :=
    match x with
    | [] => []
    | (a,b)::t => (b,a)::(flip t)
    end.

Lemma leb'_total : forall (x : list (bool * bool)),
    leb' x = true \/ leb' (flip x) = true.
Proof.
    induction x.
    - left. reflexivity.
    - destruct a. destruct b; destruct b0; simpl; try apply IHx.
        + right. reflexivity.
        + left. reflexivity.
Qed.

Lemma flip_ascii : forall (a1 a2 : ascii),
    ascii_to_list a1 a2 = flip (ascii_to_list a2 a1).
Proof.
    unfold ascii_to_list.
    destruct a1; destruct a2. reflexivity.
Qed.

Theorem leb_total : forall (a1 a2 : ascii), 
    leb a1 a2 = true \/ leb a2 a1 = true.
Proof.
    intros. unfold leb.
    rewrite flip_ascii.
    Search (_ \/ _ <-> _ \/ _).
    apply or_comm.
    apply leb'_total.
Qed.

Inductive lebr' : list (bool * bool) -> Prop :=
    | lebe' : lebr' []
    | lebft' : forall (t : list (bool * bool)),
        lebr' ((false,true)::t)
    | lebss' : forall (b : bool) (t : list (bool * bool)),
        lebr' t -> lebr' ((b,b)::t).

Inductive lebr (a1 a2 : ascii) : Prop :=
    leba : lebr' (ascii_to_list a1 a2) -> lebr a1 a2.

Lemma leb'_refl : forall (x : list (bool * bool)),
    leb' x = true <-> lebr' x.
Proof.
    induction x; split; intros; simpl in *.
    - apply lebe'.
    - reflexivity.
    - destruct a. destruct b; destruct b0.
        + apply lebss'. apply IHx.
            apply H.
        + discriminate H.
        + apply lebft'.
        + apply lebss'. apply IHx. apply H.
    - destruct a. destruct b; destruct b0.
        + apply IHx. inversion H; subst.
            apply H1.
        + inversion H; subst. discriminate H2.
        + reflexivity.
        + inversion H; subst. apply IHx. apply H1.
Qed.

Theorem leb_refl : forall (a1 a2 : ascii),
    leb a1 a2 = true <-> lebr a1 a2.
Proof.
    unfold leb; split; intros.
    - apply leba. apply leb'_refl. apply H.
    - apply leb'_refl. inversion H. apply H0.
Qed.

Lemma lebr'_total : forall (x : list (bool * bool)),
    lebr' x \/ lebr' (flip x).
Proof.
    induction x.
    - left. apply lebe'.
    - destruct a. destruct b; destruct b0; simpl; destruct IHx.
        + left. apply lebss'. apply H.
        + right. apply lebss'. apply H.
        + right. apply lebft'.
        + right. apply lebft'.
        + left. apply lebft'.
        + left. apply lebft'.
        + left. apply lebss'. apply H.
        + right. apply lebss'. apply H.
Qed.

Theorem lebr_total : forall (a1 a2 : ascii),
    lebr a1 a2 \/ lebr a2 a1.
Proof.
    intros. destruct (leb a1 a2) eqn:eq.
    - left. apply leb_refl. apply eq.
    - right. pose proof (leb_total a1 a2). destruct H.
        + rewrite eq in *. discriminate.
        + apply leb_refl. apply H.
Qed.
End AsciiOrder.

Module StringOrder <: TotalLeBool.
Definition t := string.
Fixpoint leb x y := 
    match x, y with
    | EmptyString, _ => true
    | _, EmptyString => false
    | String cx sx, String cy sy =>
        if Ascii.eqb cx cy then leb sx sy
        else AsciiOrder.leb cx cy
    end.
Theorem leb_total : forall s1 s2, leb s1 s2 = true \/ leb s2 s1 = true.
Proof.
    induction s1.
    - intros. left. reflexivity.
    - induction s2.
        + right. reflexivity.
        + simpl.
            specialize IHs1 with s2.
            assert (eq: (a =? a0)%char = (a0 =? a)%char).
            apply Ascii.eqb_sym.
            rewrite eq in *.
            destruct (a0 =? a)%char.
            * apply IHs1.
            * apply AsciiOrder.leb_total.
Qed.

Inductive lebr : string -> string -> Prop :=
    | lebe : forall (s : string),
        lebr EmptyString s
    | lebt : forall (a : ascii) (s1 s2 : string),
        lebr s1 s2 -> lebr (String a s1) (String a s2)
    | leba : forall (a1 a2 : ascii) (s1 s2 : string),
        a1 <> a2 ->
        AsciiOrder.lebr a1 a2 ->
        lebr (String a1 s1) (String a2 s2).

Theorem lebr_total : forall (s1 s2 : string),
    lebr s1 s2 \/ lebr s2 s1.
Proof.
    induction s1.
    - intros. left. apply lebe.
    - induction s2.
        + right. apply lebe.
        + specialize IHs1 with s2.
            destruct ((a0 =? a)%char) eqn:eq;
            destruct IHs1 as [h | h].
            * apply Ascii.eqb_eq in eq; subst.
                left. apply lebt. apply h.
            * apply Ascii.eqb_eq in eq; subst.
                right. apply lebt. apply h.
            * apply Ascii.eqb_neq in eq.
                destruct (AsciiOrder.leb a a0) eqn:lt.
                { left. apply leba.
                    - apply not_eq_sym. apply eq.
                    - apply AsciiOrder.leb_refl. apply lt.
                }
                { pose proof 
                    (AsciiOrder.leb_total a a0) as [LT | LT].
                    - rewrite lt in LT. discriminate LT.
                    - right. apply AsciiOrder.leb_refl in LT.
                        apply leba. apply eq. apply LT.
                }
            * apply Ascii.eqb_neq in eq.
                destruct (AsciiOrder.leb a0 a) eqn:lt.
                { right. apply leba.
                    - apply eq.
                    - apply AsciiOrder.leb_refl. apply lt.
                }
                { pose proof 
                    (AsciiOrder.leb_total a0 a) as [LT | LT].
                    - rewrite lt in LT. discriminate LT. 
                    - left. apply AsciiOrder.leb_refl in LT.
                        apply leba. apply not_eq_sym. apply eq.
                        apply LT.
                }
Qed.

Theorem leb_refl : forall (s1 s2 : string),
    leb s1 s2 = true <-> lebr s1 s2.
Proof.
    induction s1; induction s2; split; intros.
    - apply lebe.
    - reflexivity.
    - apply lebe.
    - reflexivity.
    - discriminate H.
    - inversion H.
    - simpl in H.
        destruct ((a =? a0)%char) eqn:eq.
        + apply Ascii.eqb_eq in eq; subst.
            apply lebt. apply IHs1. apply H.
        + apply Ascii.eqb_neq in eq.
            apply leba. 
            * apply eq.
            * apply AsciiOrder.leb_refl. apply H.
    - simpl. destruct ((a =? a0)%char) eqn:eq.
        + apply Ascii.eqb_eq in eq; subst.
            inversion H; subst; apply IHs1.
            * apply H1.
            * contradiction.
        + inversion H; subst.
            * apply Ascii.eqb_neq in eq.
                contradiction.
            * apply AsciiOrder.leb_refl.
                apply H5.
Qed.
End StringOrder.

Function asucc' (bs : list bool) {measure List.length bs} : list bool :=
    match bs with
    | nil => [false]
    | [false] => [true]
    | [true] => [false;true]
    | false::a => true::a
    | true::false::a => false::true::a
    | true::true::a => false::(asucc' (true::a))
    end.
Proof. 
    intros.
    simpl. omega.
Qed.

Definition ascii_to_list (a : ascii) := 
    match a with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
        [b0;b1;b2;b3;b4;b5;b6;b7]
    end.

Fixpoint take (X : Type) (n : nat) (l : list X) : list X :=
    match n with
    | 0 => nil
    | S k =>
        match l with
        | nil => nil
        | h::t => h::(take X k t)
        end
    end.

Theorem take_correct : forall (X : Type) (n : nat) (l : list X),
    List.length l >= n ->
    List.length (take X n l) = n.
Proof.
Admitted.


(* Definition list_to_ascii (bs : list bool) : ascii :=
    take bool 8 bs. *)

(* Definition asucc (a : ascii) : ascii :=  *)
  

(* Definition ssucc (s : string) : string := 
    match s with
    | EmptyString => String zero EmptyString
    | String
    end. *)


Axiom nat_to_string_mono : forall (n1 n2 : nat),
    NatOrder.lebr n1 n2 <-> StringOrder.lebr (nat_to_string n1) (nat_to_string n2).

Lemma stupid : forall (n : nat), n <> S n.
Proof.
    unfold not. intros. induction n.
    - discriminate H.
    - apply IHn. injection H as h. apply h.
Qed.

Lemma first_new_string_available : 
    forall (bag : set string) (n : nat),
    NoDup bag -> Sorted StringOrder.lebr bag ->
    set_mem string_dec (nat_to_string n) bag = false ->
    first_new_string n bag = nat_to_string n.
Proof.
    induction bag; intros.
    - reflexivity.
    - unfold first_new_string.
        destruct ((a =? nat_to_string n)%string) eqn:eq;
        fold first_new_string.
        + apply eqb_eq in eq; subst.
            simpl in H1.
            destruct (string_dec (nat_to_string n) (nat_to_string n)) eqn:eq.
            * discriminate H1.
            * contradiction.
        + destruct (set_mem string_dec (nat_to_string n) bag) eqn:eeq.
            * apply set_mem_complete1 in H1.
                apply eqb_neq in eq as neeq.
                apply set_mem_correct1 in eeq.
                exfalso.
                apply H1.
                unfold set_In in *.
                apply in_cons. apply eeq.
            * reflexivity.
Qed.

Lemma first_new_string_correct : forall (n : nat) (bag : set string),
    NoDup bag -> Sorted StringOrder.lebr bag ->
    set_mem string_dec (first_new_string n bag) bag = false.
Proof.
    intros n bag. generalize dependent n. 
    induction bag; intros.
    - reflexivity.
    - unfold first_new_string.
        destruct ((a =? nat_to_string n)%string) eqn:eq; fold first_new_string.
        + inversion H; subst. inversion H0; subst. 
            specialize IHbag with (S n).
            apply (IHbag H4) in H5 as h.
            apply eqb_eq in eq as eqq.
            assert (ha: a <> nat_to_string (S n)).
            * rewrite eqq.
                unfold not. intros.
                apply nat_to_string_inj in H1.
                apply (stupid n). apply H1.
            * admit.
Admitted.

Module Import StringSort := Sort StringOrder.

Definition fresh (e : expr) : string :=
    let bag := sort (fv e) in first_new_string 0 bag.

Lemma fresh_fresh : forall e, 
    set_mem string_dec (fresh e) (fv e) = false.
Proof.
Admitted.
    (* intros. apply set_mem_complete2. unfold not.
    induction e; intros. 
    - simpl in H. apply H.
    - simpl in H. apply H.
    - unfold fresh in H.
     unfold fv in H. unfold first_new_string in H.
     destruct (Datatypes.length (set_add string_dec s (empty_set string))) eqn:h.
     + discriminate h.
     + destruct (set_mem string_dec (nat_to_string 0 0)
        (set_add string_dec s (empty_set string))) eqn:h'.
        { apply set_mem_correct1 in h'. 
            fold first_new_string in *.
            simpl in h. injection h. intros; subst.
            apply set_add_elim in h' as [ho | ho]; subst.
            - apply set_add_elim in H as [H' | H']; subst.
                + simpl in H'. discriminate H'.
                + inversion H'.
            - inversion ho.
        }
        { simpl in h. injection h. intros; subst.
            apply set_mem_complete1 in h'.
            unfold not in h'. apply h'.
            apply H.
        }
    - apply IHe. unfold fresh in *. 
        simpl in H. apply H.
    - unfold fresh in *. simpl in H.
        apply set_union_elim in H as [h | h].
        + apply IHe1. unfold first_new_string in *.
            destruct (Datatypes.length (set_union string_dec (fv e1) (fv e2))).
            {
                destruct (Datatypes.length (fv e1)).
                - apply h.
                - fold first_new_string in *.
                    destruct (set_mem string_dec (nat_to_string 0 0) (fv e1)) eqn:h'.
                    + apply set_mem_correct1 in h'. 
                        unfold nat_to_string in *.
                        unfold first_new_string.
                    + unfold nat_to_string. apply h.
            }
          *)

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
        + apply String.eqb_neq in h.
            destruct (set_mem string_dec s0 (fv s)) eqn:mem.
            * admit.
            * exists (ELam s0 l e'). apply lam_notfree_sub.
                apply h. apply mem. apply h'.
    - destruct IHe1 as [e1' h1]. destruct IHe2 as [e2' h2].
        exists (EApp e1' e2'). apply appsub.
        apply h1. apply h2.
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
              pose proof (sub_exists x e2 e) as [e'' hsub].
              exists e''. apply lamstep. apply hsub.
            + exists (EApp e1' e2). apply appstep. apply h1.
 Qed.
    

Definition preservation (e e' : expr) (t : ltype) : Prop :=
    step e e' -> checks empty e t -> checks empty e' t.

Theorem preservation_holds : forall (e e' : expr) (t : ltype),
    preservation e e' t.
Proof.
Admitted.
    