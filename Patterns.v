(* Here are definitions and proofs of an algorithm to 
    verify pattern matching is exhaustive.
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
        ~ vinstance n v (V.nth p (F.of_nat_lt (PeanoNat.Nat.lt_trans j i m Hji Him)))).

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
    /\ ~ minstance i n (V.take i (PeanoNat.Nat.lt_le_incl i m Him) p) v).

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
Admitted.

End StrictPatterns.