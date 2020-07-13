(* Here are definitions and proofs of an algorithm to 
    verify pattern matching is exhaustive.
    See the below for the algorithm specification.
    http://moscova.inria.fr/~maranget/papers/warn/index.html
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Module Type Language.
Parameter constructor : Type.
Parameter value: Type.
Parameter sub_values: value -> list value.
Parameter vconstruct : value -> constructor -> Prop.
Parameter value_to_constructor : value -> constructor.
Axiom construct_refl : 
    forall (v : value) (c : constructor),
    vconstruct v c <-> value_to_constructor v = c.
End Language.

Module PairLang <: Language.
Inductive constructor' : Type :=
    | Base
    | Pair.
Inductive value' : Type :=
    | VBase (n : nat)
    | VPair (v1 v2 :value').
Definition constructor := constructor'.
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
End PairLang.

Fixpoint All (X : Type) (P : X -> Prop) (l : list X ) : Prop :=
    match l with
    | nil => True
    | h::t => P h /\ All X P t
    end.
    
Definition all' (X : Type) (P : X -> Prop) (l : list X) :=
    forall (x : X), In x l -> P x.

Inductive Forall2 (A B : Type) (P : A -> B -> Prop) : list A -> list B -> Prop :=
    | F2_A_nil : forall (lb : list B), Forall2 A B P nil lb
    | F2_B_nil : forall (la : list A), Forall2 A B P la nil
    | F2_cons  : forall (ha : A) (hb : B) (ta : list A) (tb : list B),
        P ha hb -> Forall2 A B P ta tb -> Forall2 A B P (ha::ta) (hb::tb).

Inductive expr :=
    | Tuple (es : list expr).

Inductive checks : expr -> Prop :=
    | ctup : forall (es : list expr),
        Forall checks es -> checks (Tuple es).

Module StrictPatterns (L : Language).

Import L.

Inductive pattern : Type :=
    | Wildcard : pattern
    | VarPattern : string -> pattern
    | Constructor : constructor -> list pattern -> pattern
    | OrPattern : pattern -> pattern -> pattern.  

Inductive instance (v : value) : pattern -> Prop :=
    | inst_wild : instance v Wildcard
    | inst_var : forall (x : string), 
        instance v (VarPattern x)
    | inst_or : forall (p1 p2 : pattern),
        instance v p1 \/ instance v p2 ->
        instance v (OrPattern p1 p2)
    | inst_construct : 
        forall (c : constructor) 
        (ps : list pattern),
        vconstruct v c ->
        Forall2 value pattern instance (sub_values v) ps ->
        instance v (Constructor c ps).

End StrictPatterns.