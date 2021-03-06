(* Coq 8.9.1 *)

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
Require Import Coq.Sets.Ensembles.
Require Coq.Logic.Classical_Pred_Type.
Module CPT := Coq.Logic.Classical_Pred_Type.
Require Coq.Logic.Classical_Prop.
Module CP := Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Decidable.

Axiom proof_irrelevance : CF.proof_irrelevance.
Axiom excluded_middle : CF.excluded_middle.

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

Lemma to_list_cons :
    forall (A : Type) (n : nat) (v : V.t A n) (h : A),
    V.to_list (V.cons A h n v) = h:: V.to_list v.
Proof. intros. reflexivity. Qed.

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

(* Definition 2 (ML Pattern Matching reformulated with Definition 3) *)
Definition row_filters' 
    (i m n : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m) :=
    (vinstance n v (V.nth p (F.of_nat_lt Him)) /\ 
    ~ minstance i n (V.take i (lt_le_weak i m Him) p) v).

(* The Versions of Definition 2 are Equivalent *)
Theorem row_filters_equiv : 
    forall (i m n : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m),
    row_filters i m n p v Him <-> row_filters' i m n p v Him.
Proof.
    unfold row_filters.
    unfold row_filters'.
    split; intros; destruct H as [H1 H2]; 
    split; try assumption;
    pose proof VL.nth_take as NT.
    - unfold not; intros NM.
        inversion NM; subst.
        destruct H as [Hxi H].
        specialize H2 with (j := x) (Hji := Hxi).
        apply H2.  
        pose proof (NT (pvec n) m p x i Hxi Him) as HY.
        rewrite HY. rewrite HY in H2.
        assumption.
    - intros j Hji. 
        unfold not. intros NV.
        apply H2. unfold minstance.
        exists j. exists Hji.
        pose proof (NT (pvec n) m p j i Hji Him) as HY.
        rewrite <- HY. 
        assumption.
Qed.

(* If P <= v, then there exists a row i in P
    such that i is the first such row to filter v. *)
Lemma minstance_row_filters :
    forall (m n : nat) (p : pmatrix m n) (v : vvec n),
    minstance m n p v <-> 
    exists (i : nat) (Him : i < m), row_filters i m n p v Him.
Proof.
Admitted.

(* Definition 4 (Exhaustiveness): *)
Definition exhaustive' (m n : nat) (p : pmatrix m n) := 
    forall (v : vvec n), exists (i : nat) (Him : i < m),
    row_filters' i m n p v Him.

Definition exhaustive (m n : nat) (p : pmatrix m n) :=
    forall (v : vvec n), exists (i : nat) (Him : i < m),
    row_filters i m n p v Him.

(* Definition 5 (Useless Clause): *)
Definition useless_clause'
    (i m n : nat) (p : pmatrix m n) (Him : i < m) := 
    ~ exists (v : vvec n), row_filters' i m n p v Him.

Definition useless_clause 
    (i m n : nat) (p : pmatrix m n) (Him : i < m) :=
    ~ exists (v : vvec n), row_filters i m n p v Him.

(* Definition 6 (Useful Clause): *)
Definition upred (m n : nat) (p : pmatrix m n) (q : pvec n) (v : vvec n) := 
    (~ minstance m n p v) /\ vinstance n v q.

(* U(p,q): *)
Definition U (m n : nat) (p : pmatrix m n) (q : pvec n) := 
    exists (v : vvec n), upred m n p q v.

(* M(p,q): *)
Definition M (m n : nat) (p : pmatrix m n) (q : pvec n) := {v | upred m n p q v}.

Fixpoint wild_vec (n : nat) : pvec n.
Proof.
    induction n.
    - apply (V.nil pattern).
    - apply (V.cons pattern Wildcard n (wild_vec n)).
Defined.

Lemma wild_vinstance : 
    forall (n : nat) (v : vvec n),
    vinstance n v (wild_vec n).
Proof.
    intros. unfold vinstance.
    induction v.
    - apply F2_A_nil.
    - simpl.
        pose proof VL.to_list_cons as TLC.
        pose proof (TLC value n v h) as TLCV.
        pose proof (TLC pattern n (wild_vec n) Wildcard) as TLCP.
        rewrite TLCV. rewrite TLCP.
        apply F2_cons.
        + apply inst_wild.
        + assumption.
Qed.      

(* Proposition 1.1: *)
Theorem exhaustive_cond' :
    forall (m n : nat) (p : pmatrix m n),
    exhaustive' m n p <-> ~ U m n p (wild_vec n).
Proof.
    split.
    - intros. unfold exhaustive' in H. unfold U.
        unfold upred. unfold not. 
        intros [v [HMI HVI]].
        apply HMI. unfold minstance.
        specialize H with v.
        destruct H as [i [Him [HVI' HNMI]]].
        exists i. exists Him.
        assumption.
    - admit.
Admitted.

Theorem exhaustive_cond : 
    forall (m n : nat) (p : pmatrix m n),
    exhaustive m n p <-> ~ U m n p (wild_vec n).
Proof.
    split; intros.
    - unfold exhaustive in *; unfold U in *; 
        unfold upred in *; 
        unfold not in *. intros [v [Hm Hv]].
        apply Hm.
        specialize H with v.
        destruct H as [i [Him Hrf]].
        unfold row_filters in Hrf.
        destruct Hrf as [Hvn HNvn].
        unfold minstance.
        exists i. exists Him.
        assumption.
    - admit.
Admitted.

(* Proposition 1.2: *)
Theorem useless_cond : 
    forall (i m n : nat) (p : pmatrix m n) (Him : i < m),
    useless_clause i m n p Him <-> 
    ~ U i n (V.take i (lt_le_weak i m Him) p) (V.nth p (F.of_nat_lt Him)).
Admitted.

End StrictPatterns.