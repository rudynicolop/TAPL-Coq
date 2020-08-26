(* An extended STLC with subtyping via the Subsumption Rule *)

Require Import String.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.FunctionalExtensionality.
    
Definition id := string.

Definition field (t : Type) : Type := id * t.

Definition fields (t : Type) : Type := list (field t).

Definition predf {U : Type} (P : U -> Prop) : field U -> Prop := fun f => P (snd f).

Definition predfs {U : Type} (P : U -> Prop) (fs : fields U) : Prop := Forall (predf P) fs.

Inductive type : Type :=
    | TTop
    | TFun (t t' : type)
    | TRec (fs : fields type).

(* automatically generated induction principle is weak *)
Check type_ind.
Compute type_ind.
Compute type_rect.

(* custom induction principle for Type type *)
Section TypeInduction.
    
    Variable P : type -> Prop.

    Hypothesis HTop : P TTop.

    Hypothesis HFun : forall (t t' : type),
        P t -> P t' -> P (TFun t t').

    Hypothesis HRec : forall (fs : fields type),
        predfs P fs -> P (TRec fs).

    Fixpoint IHType (t : type) : P t.
    Proof.
        destruct t.
        - assumption.
        - apply HFun; apply IHType.
        - apply HRec. induction fs; constructor.
            + apply IHType.
            + assumption.
    Qed.
End TypeInduction.

Lemma test_type_ind : forall (t : type), t = t.
Proof.
    induction t using IHType.
    - reflexivity.
    - constructor.
    - constructor. (* has correct induction hypothesis! *)
Qed.