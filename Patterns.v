(* Here are definitions and proofs of an algorithm to 
    verify a pattern matching is exhaustive.
    See the below for the algorithm specification.
    http://moscova.inria.fr/~maranget/papers/warn/index.html
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Vectors.VectorDef.
Require Coq.Vectors.Fin.
Module F := Coq.Vectors.Fin.
Require Coq.Vectors.Vector.
Module V := Coq.Vectors.Vector.
Require Import Omega.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.

Require Coq.Logic.ClassicalFacts.
Module CF := Coq.Logic.ClassicalFacts.
Axiom proof_irrelevance : CF.proof_irrelevance.

Module VectorLemmas.

Lemma nth_cons : 
    forall (A : Type) (m n : nat) (h : A)
    (v : V.t A n) (Hmn : m < n),
    V.nth v (F.of_nat_lt Hmn) =
    V.nth (V.cons A h n v) (F.of_nat_lt (lt_n_S m n Hmn)).
Proof.
    intros A; destruct n as [| n];
    destruct m as [| m]; intros;
    try omega; try reflexivity.
    simpl. pose proof_irrelevance as PI.
    unfold CF.proof_irrelevance in PI.
    pose proof (PI (m < n) (lt_S_n m n Hmn)) as H.
    specialize H with
        (lt_S_n m n (lt_S_n (S m) (S n) (lt_n_S (S m) (S n) Hmn))).
    rewrite <- H. reflexivity.
Qed.

Lemma nth_take :
    forall (A : Type) (n : nat) (v : V.t A n) (q w : nat)
    (Hqw : q < w) (Hwn : w < n),
    V.nth v (F.of_nat_lt (lt_trans q w n Hqw Hwn)) = 
    V.nth (V.take w (lt_le_weak w n Hwn) v) (F.of_nat_lt Hqw).
Proof.
    intros A n v. dependent induction v; 
    intros; try omega. 
    pose proof nth_cons as HC.
    destruct q as [| q].
    - simpl. destruct w as [| w]; 
        try omega. reflexivity.
    - assert (Hqn' : q < n); try omega.
        assert (Hqn : S q < S n); try omega.
        pose proof (HC A q n h v Hqn') as HR.
        pose proof proof_irrelevance as PI.
        unfold CF.proof_irrelevance in PI.
        pose proof (PI (S q < S n) Hqn (Nat.lt_trans (S q) w (S n) Hqw Hwn)) as H0.
        rewrite <- H0.
        pose proof (PI (S q < S n) Hqn (lt_n_S q n Hqn')) as H00.
        rewrite <- H00 in HR. rewrite <- HR. 
        destruct w as [| w]; try omega.
        assert (Hwn' : w < n); try omega.
        assert (Hqw' : q < w); try omega.
        assert (Hwneq' : w <= n); try omega.
        assert (Hwneq : S w <= S n); try omega.
        pose proof (IHv q w Hqw' Hwn') as ASS. simpl.
        pose proof (PI (S w <= S n) Hwneq (Nat.lt_le_incl (S w) (S n) Hwn)) as H1.
        pose proof (PI (w <= n) Hwneq' (le_S_n w n (Nat.lt_le_incl (S w) (S n) Hwn))) as H2.
        pose proof (PI (q < w) Hqw' (lt_S_n q w Hqw)) as H3.
        pose proof (PI (q < n) Hqn' (Nat.lt_trans q w n (lt_S_n q w Hqw) Hwn')) as H4.
        pose proof (PI (w <= n) (Nat.lt_le_incl w n Hwn') (le_S_n w n (Nat.lt_le_incl (S w) (S n) Hwn))) as H5.
        subst. rewrite H5 in ASS.
        assumption.
Qed.

Lemma vec_len :
    forall (A : Type) (n : nat) (v : V.t A n),
    length (V.to_list v) = n.
Proof.
    intros. induction v.
    - reflexivity.
    - unfold V.to_list in *. simpl. auto.
Qed.

End VectorLemmas.

(* General Signature a Language Must Satisfy *)
Module Type Language.
Parameter constructor : Type.
Parameter constructor_arity : constructor -> nat.
Parameter value: Type.
Parameter sub_values: value -> list value.
Parameter vconstruct : value -> constructor -> Prop.
Parameter value_to_constructor : value -> constructor.
Axiom construct_refl : 
    forall (v : value) (c : constructor),
    vconstruct v c <-> value_to_constructor v = c.
Axiom sub_arity : 
    forall (v : value) (c : constructor),
    vconstruct v c ->
    constructor_arity c = length (sub_values v).
End Language.

(* Example Language with just numbers and pairs *)
Module PairLang <: Language.

Inductive constructor' : Type :=
    | Base
    | Pair.
Definition constructor := constructor'.
Definition constructor_arity (c : constructor) : nat := 
    match c with
    | Base => 0
    | Pair => 2
    end.

Inductive value' : Type :=
    | VBase (n : nat)
    | VPair (v1 v2 :value').
Definition value := value'.

Definition sub_values (v : value) := 
    match v with
    | VBase _ => []
    | VPair v1 v2 => [v1;v2]
    end.

Inductive vconstruct' : value -> constructor -> Prop :=
    | vcbase : forall (n : nat), vconstruct' (VBase n) Base
    | vpair : forall (v1 v2 : value) (c1 c2 : constructor),
        vconstruct' v1 c1 ->
        vconstruct' v2 c2 ->
        vconstruct' (VPair v1 v2) Pair.
Definition vconstruct := vconstruct'.

Definition value_to_constructor (v : value) : constructor :=
    match v with
    | VBase _ => Base
    | VPair _ _ => Pair
    end.

Theorem construct_refl : 
    forall (v : value) (c : constructor),
    vconstruct v c <-> value_to_constructor v = c.
Proof.
    induction v; split; intros;
    try (inversion H; subst; reflexivity).
    - simpl in H; subst; constructor.
    - inversion H; subst. econstructor.
        + apply IHv1. reflexivity.
        + apply IHv2. reflexivity.
Qed.

Theorem sub_arity : 
    forall (v : value) (c : constructor),
    vconstruct v c ->
    constructor_arity c = length (sub_values v).
Proof.
    induction v; intros; inversion H; subst; reflexivity.
Qed.
End PairLang.

Inductive Forall2 (A B : Type) (P : A -> B -> Prop) : list A -> list B -> Prop :=
    | F2_A_nil : forall (lb : list B), Forall2 A B P nil lb
    | F2_B_nil : forall (la : list A), Forall2 A B P la nil
    | F2_cons  : forall (ha : A) (hb : B) (ta : list A) (tb : list B),
        P ha hb -> Forall2 A B P ta tb -> Forall2 A B P (ha::ta) (hb::tb).

(* Exhaustive-Pattern Checking for a Strict Language *)
Module StrictPatterns (L : Language).

Import L.
Module VL := VectorLemmas.

Definition vvec (n : nat) := V.t value n.

(* Pattern Definition *)
Inductive pattern : Type :=
    | Wildcard : pattern
    | VarPattern : string -> pattern
    | Constructor (c : constructor) : V.t pattern (constructor_arity c) -> pattern
    | OrPattern : pattern -> pattern -> pattern.  

Definition pvec (n : nat) := V.t pattern n.

(* Definition 1 (The Instance Relation): *)
Inductive instance (v : value) : pattern -> Prop :=
    | inst_wild : instance v Wildcard
    | inst_var : forall (x : string), 
        instance v (VarPattern x)
    | inst_or : forall (p1 p2 : pattern),
        instance v p1 \/ instance v p2 ->
        instance v (OrPattern p1 p2)
    | inst_construct : 
        forall (c : constructor) 
        (ps : pvec (constructor_arity c)),
        vconstruct v c ->
        Forall2 value pattern instance (sub_values v) (V.to_list ps) ->
        instance v (Constructor c ps).

(* Definition 1 (Vector Instance Relation) *)
Definition vinstance 
    (n : nat) (v : vvec n) (p : pvec n) := 
    Forall2 value pattern instance (V.to_list v) (V.to_list p).

(* An m x n pattern matrix *)
Definition pmatrix (m n : nat) : Type := V.t (pvec n) m.


(* Definition 2 (ML Pattern Matching)
    A Row  i in P filters v iff
    - Pi <= v
    - forall j < i, ~ Pj <= v *)
Definition row_filters 
    (i m n : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m) :=
    (vinstance n v (V.nth p (F.of_nat_lt Him))
    /\ 
    forall (j : nat) (Hji : j < i),
        ~ vinstance n v (V.nth p (F.of_nat_lt (lt_trans j i m Hji Him)))).

(* Definition 3 (Instance Relation for Matrices): *)
Definition minstance
    (m n : nat) (p : pmatrix m n) (v : vvec n) :=
    exists (i : nat) (Him : i < m), 
    vinstance n v (V.nth p (F.of_nat_lt Him)).

Search (_ < _ -> _ <= _).

(* Definition 2 (ML Pattern Matching reformulated with Definition 3) *)
Definition row_filters' 
    (i m n : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m) :=
    (vinstance n v (V.nth p (F.of_nat_lt Him))
    /\ ~ minstance i n (V.take i (lt_le_weak i m Him) p) v).

(* The Versions of Definition 2 are Equivalent *)
Theorem row_filters_equiv : 
    forall (i m n : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m),
    row_filters i m n p v Him <-> row_filters' i m n p v Him.
Proof.
    intros i m n.
    induction p; split;
    intros; try omega.
    - unfold row_filters in H.
        destruct H as [H1 H2].
        unfold row_filters'. split.
        + assumption.
        + unfold not; intros NM.
            inversion NM; subst.
            destruct H as [Hxi H].
            specialize H2 with (j := x) (Hji := Hxi).
            apply H2.
            pose proof VL.nth_take as NT.
            pose proof (NT (pvec n) (S n0) 
                (VectorDef.cons (pvec n) h n0 p) 
                x i Hxi Him) as HY.
            rewrite HY. rewrite HY in H2.
            assumption.
    - unfold row_filters' in H.
        destruct H as [H1 H2].
        unfold row_filters. split.
        + assumption.
        + intros j Hji. 
            unfold not. intros NV.
            inversion NV; subst.
            { unfold vvec in v.
                assert (n = 0).
                - symmetry in H0.
                    apply length_zero_iff_nil in H0.
                    rewrite VL.vec_len in H0. assumption.
                - subst. apply H2. unfold minstance.
                    exists j. exists Hji.
                    pose proof VL.nth_take as NT.
                    pose proof (NT (pvec 0) (S n0) 
                        (VectorDef.cons (pvec 0) h n0 p)
                        j i Hji Him) as HY.
                    rewrite <- HY. 
                    assumption.
            }
            { assert (n = 0).
                - symmetry in H3.
                    apply length_zero_iff_nil in H3.
                    rewrite VL.vec_len in H3. assumption.
                - subst. apply H2. unfold minstance.
                    exists j. exists Hji.
                    pose proof VL.nth_take as NT.
                    pose proof (NT (pvec 0) (S n0) 
                        (VectorDef.cons (pvec 0) h n0 p)
                        j i Hji Him) as HY.
                    rewrite <- HY. 
                    assumption. 
            }
            { unfold vvec in v.
                apply H2. unfold minstance.
                    exists j. exists Hji.
                    pose proof VL.nth_take as NT.
                    pose proof (NT (pvec n) (S n0) 
                        (VectorDef.cons (pvec n) h n0 p)
                        j i Hji Him) as HY.
                    rewrite <- HY. 
                    assumption.
            }
Qed.

End StrictPatterns.