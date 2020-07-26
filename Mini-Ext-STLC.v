(* The Simply-Typed Lambda Calculus with minimal extensions,
    with unit, pairs, and either types. 
    
    The algorithm and proof of exhaustive pattern-matching
    is based upon the following one for a strict language:
    http://moscova.inria.fr/~maranget/papers/warn/index.html
    *)

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Coq.Sets.Ensembles.
Module E := Coq.Sets.Ensembles.
Require Coq.Lists.ListSet.
Module LS := Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Vectors.Fin.
Module F := Coq.Vectors.Fin.
Require Coq.Vectors.Vector.
Module V := Coq.Vectors.Vector.
Require Import Omega.
Require Coq.Logic.ClassicalFacts.
Module CF := Coq.Logic.ClassicalFacts.
Require Coq.Logic.Classical_Pred_Type.
Module CPT := Coq.Logic.Classical_Pred_Type.
Require Coq.Logic.Classical_Prop.
Module CP := Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Specif.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.FSets.FMapWeakList.
Module FM := Coq.FSets.FMapWeakList.
Require Import Coq.Logic.FunctionalExtensionality.

(* Helper Definitions and Lemmas *)

Axiom proof_irrelevance : CF.proof_irrelevance.
Axiom excluded_middle : CF.excluded_middle.
Axiom prop_extensionality : CF.prop_extensionality.

Module VectorLemmas.

    Lemma nth_cons : 
        forall (A : Type) (m n : nat) (h : A)
        (v : V.t A n) (Hmn : m < n),
        V.nth_order v Hmn =
        V.nth_order (V.cons A h n v) (lt_n_S m n Hmn).
    Proof.
        intros A; destruct n as [| n];
        destruct m as [| m]; intros;
        try omega; try reflexivity.
        unfold V.nth_order. simpl.
        pose proof_irrelevance as PI.
        unfold CF.proof_irrelevance in PI.
        pose proof (PI (S m < S n) Hmn) as H.
        specialize H with (lt_S_n (S m) (S n) (lt_n_S (S m) (S n) Hmn)).
        rewrite <- H. reflexivity. 
    Qed.

    Lemma nth_take :
        forall (A : Type) (n : nat) (v : V.t A n) (q w : nat)
        (Hqw : q < w) (Hwn : w < n),
        V.nth_order v (lt_trans q w n Hqw Hwn) = 
        V.nth_order (V.take w (lt_le_weak w n Hwn) v) Hqw.
    Proof.
        unfold V.nth_order.
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
            rewrite <- H00 in HR. unfold V.nth_order in *.
            rewrite <- HR. 
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

Definition existsb {n : nat} {A : Type}
    (f : A -> bool) (v : V.t A n) : bool.
Proof.
    induction n.
    - apply false.
    - inversion v; subst. apply (f h || IHn X).
Defined.

Definition forallb {n : nat} {A : Type}
    (f : A -> bool) (va : V.t A n) : bool.
Proof.
    induction n.
    - apply true.
    - inversion va; subst.
        apply (f h && IHn X).
Defined.

Definition forall2b {n : nat} {A B : Type}
    (f : A -> B -> bool) (va : V.t A n) (vb : V.t B n) : bool.
Proof.
    induction n.
    - apply true.
    - inversion va; inversion vb; subst.
        apply ((f h h0) && IHn X X0).
Defined.

Module Type HasRefl.
    Parameter A : Type.
    Parameter P : A -> Prop.
    Parameter f : A -> bool.
    Axiom refl : forall (a : A), P a <-> f a = true.
End HasRefl.

Module NotRefl (M : HasRefl).
    Theorem not_refl : forall (a : M.A), ~ M.P a <-> M.f a = false.
    Proof.
        pose proof M.refl as R.
        unfold not; split; intros.
        - destruct (M.f a) eqn:eq.
            + apply R in eq. contradiction.
            + reflexivity.
        - apply R in H0. rewrite H in H0. discriminate.
    Qed.
End NotRefl.

Module Type HasRefl2.
    Parameter A : Type.
    Parameter B : Type.
    Parameter P : A -> B -> Prop.
    Parameter f : A -> B -> bool.
    Axiom refl : forall (a : A) (b : B), P a b <-> f a b = true.
End HasRefl2.

Module NotRefl2 (M : HasRefl2).
    Theorem not_refl2 : forall (a : M.A) (b : M.B),
        ~ M.P a b <-> M.f a b = false.
    Proof.
        pose proof M.refl as R.
        unfold not; split; intros.
        - destruct (M.f a b) eqn:eq.
            + apply R in eq. contradiction.
            + reflexivity.
        - apply R in H0. rewrite H in H0. discriminate.
    Qed.
End NotRefl2.

(* this is really ass to prove *)
Axiom vect_nil : 
    forall {A : Type} (v : V.t A 0), v = V.nil A.

(* also incredibly ass,
    if you don't believe me
    then try it yourself *)
Axiom vect_cons : forall {A : Type} {n : nat}
    (v : V.t A (S n)), exists (h : A) (t : V.t A n),
    v = V.cons A h n t.

Module VectorForallRefl (M : HasRefl).
    Import V.VectorNotations.
    Theorem forall_refl :
        forall {n : nat} (v : V.t M.A n),
        V.Forall M.P v <-> forallb M.f v = true.
    Proof.
        induction n; split; intros.
        - reflexivity.
        - pose proof (vect_nil v) as V; subst. constructor.
        - pose proof (vect_cons v) as [h [t V]]; subst.
            inversion H; subst.
            pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
            eapply STUPID in H2; try apply Nat.eq_dec; subst.
            simpl. unfold eq_rect_r. simpl.
            apply andb_true_iff. split.
            + apply M.refl. assumption.
            + apply IHn. assumption.
        - pose proof (vect_cons v) as [h [t V]]; subst.
            simpl in H. unfold eq_rect_r in H. simpl in H.
            apply andb_true_iff in H as [H1 H2]. constructor.
            + apply M.refl. assumption.
            + apply IHn. assumption.
    Qed.
End VectorForallRefl.

Module VectorExistsRefl (M : HasRefl).
    Import V.VectorNotations.
    Theorem exists_refl : 
        forall {n : nat} (v : V.t M.A n),
        V.Exists M.P v <-> existsb M.f v = true.
    Proof.
        induction n; split; intros.
        - inversion H.
        - pose proof (vect_nil v) as V; subst. discriminate H.
        - pose proof (vect_cons v) as [h [t V]]; subst.
            pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
            inversion H; subst; simpl; 
            unfold eq_rect_r; simpl;
            apply orb_true_iff.
            + left. apply M.refl. assumption.
            + right. apply IHn. eapply STUPID in H3; 
                subst; try apply Nat.eq_dec.
                assumption.
        - pose proof (vect_cons v) as [h [t V]]; subst.
            pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
            simpl in H. unfold eq_rect_r in H; simpl in H.
            apply orb_true_iff in H. destruct H.
            + apply V.Exists_cons_hd. apply M.refl.
                assumption.
            + apply V.Exists_cons_tl. apply IHn.
                assumption. 
    Qed.
End VectorExistsRefl.

Module VectorForall2Refl (M : HasRefl2).
    Import V.VectorNotations.
    Theorem forall2_refl : 
        forall {n : nat} (va : V.t M.A n) (vb : V.t M.B n),
        V.Forall2 M.P va vb <-> forall2b M.f va vb = true.
    Proof.
        induction n; split; intros.
        - reflexivity.
        - pose proof (vect_nil va) as VA.
            pose proof (vect_nil vb)as VB.
            subst. constructor.
        - pose proof (vect_cons va) as [ha [ta VA]].
            pose proof (vect_cons vb) as [hb [tb VB]].
            subst. inversion H; subst.
            apply IHn in H6. apply M.refl in H4.
            simpl. unfold eq_rect_r. simpl.
            Search (existT _ _ _ = existT _ _ _ -> _ = _).
            pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
            apply STUPID in H2; apply STUPID in H5; 
            subst; try apply Nat.eq_dec.
            rewrite H4. rewrite H6. reflexivity.
        - pose proof (vect_cons va) as [ha [ta VA]].
            pose proof (vect_cons vb) as [hb [tb VB]].
            subst. simpl in H. unfold eq_rect_r in H. simpl in H.
            apply andb_true_iff in H as [H1 H2]. constructor.
            + apply M.refl. assumption.
            + apply IHn. assumption.
    Qed.
End VectorForall2Refl.

Module VL := VectorLemmas.

Fixpoint take {A : Type} (n : nat) (l : list A) :=
    match n with
    | 0 => []
    | S k =>
        match l with
        | [] => []
        | h::t => h :: take k t
        end
    end.

Lemma take_correct :
    forall {A : Type} (n : nat) (l : list A),
        length (take n l) <= n.
Proof.
    intros A. induction n; induction l; 
    simpl in *; try omega.
    specialize IHn with l. omega.
Qed.

Lemma take_complete :
    forall {A : Type} (i n : nat) (l : list A),
    i < n -> nth_error l i = nth_error (take n l) i.
Proof.
    intros A. induction i; 
    destruct n; destruct l; intros;
    simpl in *; try omega; try reflexivity.
    specialize IHi with (n := n) (l := l).
    assert (i < n); try omega. auto.
Qed.

(* Syntax of Partially-Extended STLC *)

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

Module TypeEqRefl <: HasRefl2.
    Definition A := type.
    Definition B := type.
    Definition P (a b : type) := a = b.
    Definition f := type_eqb.
    Theorem refl : forall (a : A) (b : B), P a b <-> f a b = true.
    Proof. intros. apply type_eq_refl. Qed.
End TypeEqRefl.

Module TypeNotEq := NotRefl2(TypeEqRefl).

Theorem type_eq_dec : forall a b : type, { a = b } + { a <> b }.
Proof. 
    intros. destruct (type_eqb a b) eqn:eq.
    - left. apply type_eq_refl. assumption.
    - right. unfold not. intros H.
        apply type_eq_refl in H.
        rewrite H in eq. discriminate.
Qed.

Inductive construct : Type :=
    | CUnit | CPair | CLeft (a b : type) | CRight (a b : type).

Module ConstructEqRefl <: HasRefl2.
    Definition A := construct.
    Definition B := construct.
    Definition P (c1 c2 : construct) := c1 = c2.
    Definition f (c1 c2 : construct) :=
        match c1, c2 with
        | CUnit, CUnit
        | CPair, CPair => true
        | CLeft a1 b1, CLeft a2 b2
        | CRight a1 b1, CRight a2 b2 =>
            type_eqb a1 a2 && type_eqb b1 b2
        | _, _ => false
        end.
    Theorem refl : forall (c1 c2 : construct),
        c1 = c2 <-> f c1 c2 = true.
    Proof.
        destruct c1; destruct c2; split; intros;
        try inversion H; subst; try reflexivity;
        simpl in *;
        try (apply andb_true_iff; split; apply type_eq_refl; reflexivity);
        try (apply andb_true_iff in H1 as [HA HB];
            apply type_eq_refl in HA;
            apply type_eq_refl in HB;
            subst; reflexivity).
    Qed.
End ConstructEqRefl.

Inductive pattern : Type :=
    | PWild
    | PVar (x : id)
    | PUnit
    | PPair (p1 p2 : pattern)
    | PLeft (t1 t2 : type) (p : pattern)
    | PRight (t1 t2 : type) (p : pattern)
    | POr (p1 p2 : pattern).

Module PatternEqRefl : HasRefl2.
    Definition A := pattern.
    Definition B := pattern.
    Definition P (p1 p2 : pattern) := p1 = p2.
    Fixpoint f (p1 p2 : pattern) : bool :=
        match p1, p2 with
        | PWild, PWild
        | PUnit, PUnit => true
        | PVar x1, PVar x2 => (x1 =? x2)%string
        | PPair p11 p12, PPair p21 p22 =>
            f p11 p21 && f p12 p22
        | PLeft a1 b1 p1, PLeft a2 b2 p2
        | PRight a1 b1 p1, PRight a2 b2 p2 =>
            type_eqb a1 a2 && type_eqb b1 b2 && f p1 p2
        | POr p11 p12, POr p21 p22 =>
            f p11 p21 && f p12 p22
        | _, _ => false
        end.
    Theorem refl : forall (p1 p2 : pattern),
    p1 = p2 <-> f p1 p2 = true.
    Proof.
        induction p1; destruct p2; split; intros H;
        try inversion H; subst; try reflexivity;
        simpl in *;
        try (apply andb_true_iff; split;
            try (apply IHp1_1; reflexivity);
            try (apply IHp1_2; reflexivity));
        try (apply andb_true_iff in H1 as [H1 H2];
            apply IHp1_1 in H1; apply IHp1_2 in H2;
            subst; reflexivity);
        try (apply andb_true_iff; split;
            try (apply andb_true_iff; split; 
                apply type_eq_refl; reflexivity);
            try (apply IHp1; reflexivity));
        try (apply andb_true_iff in H1 as [HT Hf];
            apply andb_true_iff in HT as [HT1 HT2];
            apply type_eq_refl in HT1; apply type_eq_refl in HT2;
            apply IHp1 in Hf; subst; reflexivity);
        try (apply type_eq_refl; reflexivity);
        try (apply IHp1; reflexivity).
        - apply String.eqb_eq. reflexivity.
        - apply String.eqb_eq in H; subst. reflexivity.
    Qed.
End PatternEqRefl.

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

Module FV := FM.Make(IdDec).
Definition fvt := FV.t type.
Definition fv_empty := FV.empty type.

Definition set_of_fv (fv : fvt) : E.Ensemble id :=
    FV.fold (fun x _ acc => E.Add id acc x) fv (E.Empty_set id).

Definition id_set_add := LS.set_add IdDec.eq_dec.

Definition lset_of_fv (fv : fvt) : (LS.set id) :=
    FV.fold (fun x _ acc => id_set_add x acc) fv (LS.empty_set id).

Definition id_set_inter := LS.set_inter IdDec.eq_dec.

Definition ls_disjoint (a b : LS.set id) :=
    match id_set_inter a b with
    | nil => true
    | _ => false 
    end.

Lemma disjoint_refl : forall (f1 f2 : fvt),
    E.Disjoint id (set_of_fv f1) (set_of_fv f2) <-> 
    ls_disjoint (lset_of_fv f1) (lset_of_fv f2) = true.
Proof.
Admitted.

Definition add_all (f1 : fvt) (f2 : fvt) : fvt :=
    FV.fold (fun x t acc => FV.add x t acc) f1 f2.

Lemma disjoint_add_all : forall (a b : fvt),
    E.Disjoint id (set_of_fv a) (set_of_fv b) ->
    FV.Equivb type_eqb (add_all a b) (add_all b a).
Proof.
Admitted.

Inductive free_vars : pattern -> type -> fvt -> Prop :=
    | free_wild : forall (t : type), free_vars PWild t fv_empty
    | free_name : forall (x : id) (t : type),
        free_vars (PVar x) t (FV.add x t fv_empty)
    | free_unit : free_vars PUnit TUnit fv_empty
    | free_pair : forall (p1 p2 : pattern) (a b : type) (f1 f2 : fvt),
        free_vars p1 a f1 ->
        free_vars p2 b f2 ->
        E.Disjoint id (set_of_fv f1) (set_of_fv f2) ->
        free_vars (PPair p1 p2) (TPair a b) (add_all f1 f2)
    | free_left : forall (a b : type) (p : pattern) (f : fvt),
        free_vars p a f ->
        free_vars (PLeft a b p) (TEither a b) f
    | free_right : forall (a b : type) (p : pattern) (f : fvt),
        free_vars p b f ->
        free_vars (PRight a b p) (TEither a b) f
    | free_or : forall (p1 p2 : pattern) (t : type) (f1 f2 : fvt),
        free_vars p1 t f1 ->
        free_vars p2 t f2 ->
        FV.Equivb type_eqb f1 f2 ->
        free_vars (POr p1 p2) t f1.

Fixpoint free_varsb (p : pattern) (t : type) : option fvt :=
    match p,t with
    | PWild, _ 
    | PUnit, TUnit => Some fv_empty
    | PVar x, _ => Some (FV.add x t fv_empty)
    | PPair p1 p2, TPair a b =>
        match free_varsb p1 a, free_varsb p2 b with
        | Some f1, Some f2 =>
            if ls_disjoint (lset_of_fv f1) (lset_of_fv f2)
            then Some (add_all f1 f2) else None
        | _, _ => None
        end
    | PLeft a b p, TEither a' b' =>
        if type_eqb a a' && type_eqb b b' 
        then free_varsb p a else None
    | PRight a b p, TEither a' b' =>
        if type_eqb a a' && type_eqb b b' 
        then free_varsb p b else None
    | POr p1 p2, _ =>
        match free_varsb p1 t, free_varsb p2 t with
        | Some f1, Some f2 =>
            if FV.equal type_eqb f1 f2 then Some f1 else None
        | _, _ => None
        end
    | _, _ => None
    end.

Lemma free_vars_refl :
    forall (p : pattern) (t : type) (f : fvt),
    free_vars p t f <-> free_varsb p t = Some f.
Proof.
    induction p; destruct t; split; intros H;
    try inversion H; subst; simpl in *;
    try discriminate H;
    try reflexivity; try constructor.
    - apply IHp1 in H4. apply IHp2 in H6.
        rewrite H4. rewrite H6.
        apply disjoint_refl in H7.
        rewrite H7. reflexivity.
    - destruct (free_varsb p1 t1) eqn:eq1;
        destruct (free_varsb p2 t2) eqn:eq2;
        try discriminate.
        apply IHp1 in eq1. apply IHp2 in eq2.
        destruct (ls_disjoint (lset_of_fv f0) (lset_of_fv f1)) eqn:eqd;
        try discriminate; injection H1; intros; subst.
        apply disjoint_refl in eqd. constructor; assumption.
    - assert (T1: type_eqb t3 t3 = true);
        try (apply type_eq_refl; reflexivity).
        assert (T2 : type_eqb t4 t4 = true);
        try (apply type_eq_refl; reflexivity).
        rewrite T1. rewrite T2. simpl.
        apply IHp. assumption.
    - destruct (type_eqb t1 t3) eqn:eq1;
        destruct (type_eqb t2 t4) eqn:eq2;
        try discriminate. simpl in *.
        apply type_eq_refl in eq1.
        apply type_eq_refl in eq2.
        apply IHp in H1. subst.
        constructor. assumption.
    - assert (T1: type_eqb t3 t3 = true);
        try (apply type_eq_refl; reflexivity).
        assert (T2 : type_eqb t4 t4 = true);
        try (apply type_eq_refl; reflexivity).
        rewrite T1. rewrite T2. simpl.
        apply IHp. assumption.
    - destruct (type_eqb t1 t3) eqn:eq1;
        destruct (type_eqb t2 t4) eqn:eq2;
        try discriminate. simpl in *.
        apply type_eq_refl in eq1.
        apply type_eq_refl in eq2.
        apply IHp in H1. subst.
        constructor. assumption.
    - apply IHp1 in H2. apply IHp2 in H3.
        rewrite H2. rewrite H3.
        apply FV.equal_1 in H6. rewrite H6.
        reflexivity.
    - destruct (free_varsb p1 TUnit) eqn:eq1;
        destruct (free_varsb p2 TUnit) eqn:eq2;
        try discriminate.
        apply IHp1 in eq1. apply IHp2 in eq2.
        destruct (FV.equal type_eqb f0 f1) eqn:eqf;
        try discriminate.
        injection H1; intros; subst.
        apply FV.equal_2 in eqf.
        eapply free_or.
        + assumption.
        + apply eq2.
        + assumption.
    - apply IHp1 in H2. apply IHp2 in H3.
        rewrite H2. rewrite H3.
        apply FV.equal_1 in H6. rewrite H6.
        reflexivity.
    - destruct (free_varsb p1 (TFun t1 t2)) eqn:eq1;
        destruct (free_varsb p2 (TFun t1 t2)) eqn:eq2;
        try discriminate.
        apply IHp1 in eq1. apply IHp2 in eq2.
        destruct (FV.equal type_eqb f0 f1) eqn:eqf;
        try discriminate.
        injection H1; intros; subst.
        apply FV.equal_2 in eqf.
        eapply free_or.
        + assumption.
        + apply eq2.
        + assumption.
    - apply IHp1 in H2. apply IHp2 in H3.
        rewrite H2. rewrite H3.
        apply FV.equal_1 in H6. rewrite H6.
        reflexivity.
    - destruct (free_varsb p1 (TPair t1 t2)) eqn:eq1;
        destruct (free_varsb p2 (TPair t1 t2)) eqn:eq2;
        try discriminate.
        apply IHp1 in eq1. apply IHp2 in eq2.
        destruct (FV.equal type_eqb f0 f1) eqn:eqf;
        try discriminate.
        injection H1; intros; subst.
        apply FV.equal_2 in eqf.
        eapply free_or.
        + assumption.
        + apply eq2.
        + assumption.
    - apply IHp1 in H2. apply IHp2 in H3.
        rewrite H2. rewrite H3.
        apply FV.equal_1 in H6. rewrite H6.
        reflexivity.
    - destruct (free_varsb p1 (TEither t1 t2)) eqn:eq1;
        destruct (free_varsb p2 (TEither t1 t2)) eqn:eq2;
        try discriminate.
        apply IHp1 in eq1. apply IHp2 in eq2.
        destruct (FV.equal type_eqb f0 f1) eqn:eqf;
        try discriminate.
        injection H1; intros; subst.
        apply FV.equal_2 in eqf.
        eapply free_or.
        + assumption.
        + apply eq2.
        + assumption.
Qed.

Inductive pat_type : pattern -> type -> Prop :=
    | pt_wild : forall (t : type),
        pat_type PWild t
    | pt_name : forall (x : id) (t : type),
        pat_type (PVar x) t
    | pt_unit : pat_type PUnit TUnit
    | pt_pair : forall (p1 p2 : pattern) (a b : type) (f1 f2 : fvt),
        pat_type p1 a ->
        pat_type p2 b ->
        free_vars p1 a f1 ->
        free_vars p2 b f2 ->
        E.Disjoint id (set_of_fv f1) (set_of_fv f2) ->
        pat_type (PPair p1 p2) (TPair a b)
    | pt_left : forall (a b : type) (p : pattern),
        pat_type p a ->
        pat_type (PLeft a b p) (TEither a b)
    | pt_right : forall (a b : type) (p : pattern),
        pat_type p b ->
        pat_type (PRight a b p) (TEither a b)
    | pt_or : forall (p1 p2 : pattern) (t : type) (f1 f2 : fvt),
        pat_type p1 t ->
        pat_type p2 t ->
        free_vars p1 t f1 ->
        free_vars p2 t f2 ->
        FV.Equivb type_eqb f1 f2 ->
        pat_type (POr p1 p2) t.

Fixpoint pat_typeb (p : pattern) (t : type) : bool :=
    match p,t with
    | PWild, _ 
    | PVar _, _
    | PUnit, TUnit => true
    | PPair p1 p2, TPair a b =>
        match free_varsb p1 a, free_varsb p2 b with
        | Some f1, Some f2 => 
            if ls_disjoint (lset_of_fv f1) (lset_of_fv f2)
            then pat_typeb p1 a && pat_typeb p2 b
            else false
        | _, _ => false
        end
    | PLeft a b p, TEither a' b' =>
        type_eqb a a' && type_eqb b b' && pat_typeb p a
    | PRight a b p, TEither a' b' =>
        type_eqb a a' && type_eqb b b' && pat_typeb p b
    | POr p1 p2, _ =>
        match free_varsb p1 t, free_varsb p2 t with
        | Some f1, Some f2 =>
            if FV.equal type_eqb f1 f2 
            then pat_typeb p1 t && pat_typeb p2 t
            else false
        | _, _ => false
        end
    | _, _ => false
    end.
    
Lemma pat_type_refl : 
    forall (p : pattern) (t : type),
    pat_type p t <-> pat_typeb p t = true.
Proof.
    induction p; split; intros H;
    try inversion H; subst; simpl in *;
    try (destruct t; try discriminate; constructor);
    try (destruct t; subst; reflexivity);
    try reflexivity.
    - apply free_vars_refl in H4.
        apply free_vars_refl in H5.
        rewrite H4. rewrite H5.
        apply disjoint_refl in H7.
        rewrite H7. apply andb_true_iff.
        apply IHp1 in H2. apply IHp2 in H3.
        split; assumption.
    - destruct t; try discriminate.
        destruct (free_varsb p1 t1) eqn:eqf1;
        destruct (free_varsb p2 t2) eqn:eqf2;
        try discriminate.
        destruct (ls_disjoint (lset_of_fv f) (lset_of_fv f0)) eqn:eqd;
        try discriminate.
        apply andb_true_iff in H1 as [H1 H2].
        apply IHp1 in H1. apply IHp2 in H2.
        apply disjoint_refl in eqd.
        apply free_vars_refl in eqf1.
        apply free_vars_refl in eqf2.
        eapply pt_pair; try assumption.
        + apply eqf1.
        + apply eqf2.
        + assumption.
    - apply andb_true_iff. split.
        + apply andb_true_iff; split; 
            apply type_eq_refl; reflexivity.
        + apply IHp. assumption.
    - destruct t; try discriminate.
        apply andb_true_iff in H1 as [HT HP].
        apply andb_true_iff in HT as [T1 T2].
        apply type_eq_refl in T1.
        apply type_eq_refl in T2.
        apply IHp in HP. subst.
        constructor. assumption.
    - apply andb_true_iff. split.
        + apply andb_true_iff; split; 
            apply type_eq_refl; reflexivity.
        + apply IHp. assumption.
    - destruct t; try discriminate.
        apply andb_true_iff in H1 as [HT HP].
        apply andb_true_iff in HT as [T1 T2].
        apply type_eq_refl in T1.
        apply type_eq_refl in T2.
        apply IHp in HP. subst.
        constructor. assumption.
    - apply free_vars_refl in H4.
        apply free_vars_refl in H5.
        rewrite H4. rewrite H5.
        apply FV.equal_1 in H7. rewrite H7.
        apply IHp1 in H2. apply IHp2 in H3.
        apply andb_true_iff. split; assumption.
    - destruct (free_varsb p1 t) eqn:eq1;
        destruct (free_varsb p2 t) eqn:eq2;
        try discriminate.
        destruct (FV.equal type_eqb f f0) eqn:eqe;
        try discriminate.
        apply free_vars_refl in eq1.
        apply free_vars_refl in eq2.
        apply andb_true_iff in H1 as [H1 H2].
        apply IHp1 in H1. apply IHp2 in H2.
        econstructor; try assumption.
        + apply eq1.
        + apply eq2.
        + apply FV.equal_2. assumption.
Qed.

Definition pjudge (t : type) (p : pattern) := pat_type p t.

(* Definition pvec (n : nat) := V.t pattern n. *)

(* Definition pvec_type {n : nat} (p : pvec n) (t : type) := V.Forall (pjudge t) p. *)

Definition patt (t : type) := {p : pattern | pat_type p t}.

(* Definition pvt {n : nat} (t : type) := {p : pvec n | pvec_type p t}. *)

Definition pvt (n : nat) (t : type) := V.t (patt t) n.

Definition plt (t : type) := list (patt t).

Module PatternDec <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Definition t := pattern.
    Definition eq (p1 p2 : t) := p1 = p2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (p1 p2 : pattern),
        {p1 = p2} + {p1 <> p2}.
    Proof.
        induction p1; destruct p2;
        try (pose proof (IHp1_1 p2_1) as IH1;
            pose proof (IHp1_2 p2_2) as IH2;
            destruct IH1 as [IH1 | IH1]; 
            destruct IH2 as [IH2 | IH2]; subst;
            try (right; intros NE; inversion NE; 
            subst; try apply IH1; try apply IH2; reflexivity));
        try (pose proof (string_dec x x0) as [H | H]; subst;
            try (right; intros NE; inversion NE; subst; apply H; reflexivity));
        try (pose proof (IHp1 p2) as IH;
            pose proof (type_eq_dec t1 t0) as TED1;
            pose proof (type_eq_dec t2 t3) as TED2;
            destruct IH as [IH | IH];
            destruct TED1 as [TED1 | TED1];
            destruct TED2 as [TED2 | TED2]; subst;
            try (right; intros NE; inversion NE; contradiction));
        try (left; reflexivity);
        try (right; intros H; inversion H).
    Qed.
End PatternDec.

Inductive root_construct : pattern -> construct -> Prop :=
    | rc_unit : root_construct PUnit CUnit
    | rc_pair : forall (p1 p2 : pattern),
        root_construct (PPair p1 p2) CPair
    | rc_either_left : forall (a b : type) (p : pattern),
        root_construct (PLeft a b p) (CLeft a b)
    | rc_either_right : forall (a b : type) (p : pattern),
        root_construct (PRight a b p) (CRight a b)
    | rc_or_intros_left : forall (p1 p2 : pattern) (c : construct),
        root_construct p1 c ->
        root_construct (POr p1 p2) c
    | rc_intros_right : forall (p1 p2 : pattern) (c : construct),
        root_construct p2 c ->
        root_construct (POr p1 p2) c.

Definition rct {t : type} (p : patt t) := root_construct (proj1_sig p).

(* Complete Signature Sigma *)
Inductive sigma : forall (t : type), (E.Ensemble (patt t)) -> Prop :=
    | sigma_unit : forall (p : patt TUnit) (e : E.Ensemble (patt TUnit)),
        E.In (patt TUnit) e p -> 
        rct p CUnit -> 
        sigma TUnit e
    | sigma_pair : forall (a b : type) 
        (p : patt (TPair a b)) (e : E.Ensemble (patt (TPair a b))),
        E.In (patt (TPair a b)) e  p ->
        rct p CPair ->
        sigma (TPair a b) e
    | sigma_either : forall (a b : type) 
        (pl pr : patt (TEither a b)) (e : E.Ensemble (patt (TEither a b))),
        E.In (patt (TEither a b)) e pl ->
        E.In (patt (TEither a b)) e pr ->
        rct pl (CLeft a b) ->
        rct pr (CRight a b) ->
        sigma (TEither a b) e.

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

(* Approximate yet Sufficient Typing for values
    for the purposes of proving exhaustive matching *)

Inductive val_judge : value -> type -> Prop :=
    | vj_unit : val_judge VUnit TUnit
    | vj_fun : forall (p : pattern) (t t' : type) 
        (e : expr),
        pjudge t p ->
        val_judge (VFun p t e) (TFun t t')
    | vj_pair : forall (v1 v2 : value) (a b : type),
        val_judge v1 a ->
        val_judge v2 b ->
        val_judge (VPair v1 v2) (TPair a b)
    | vj_left : forall (a b : type) (v : value),
        val_judge v a ->
        val_judge (VLeft a b v) (TEither a b)
    | vj_right : forall (a b : type) (v : value),
        val_judge v b ->
        val_judge (VRight a b v) (TEither a b).

Definition valt (t : type) := {v : value | val_judge v t}.

Definition vjudge (t : type) (v : value) := val_judge v t.

(* Definition 1 (Instance Relation) *)
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
        instance p v -> instance (PRight t1 t2 p) (VRight t1 t2 v)
    | instance_or_left : forall (p1 p2 : pattern) (v : value),
        instance p1 v -> instance (POr p1 p2) v
    | instance_or_right : forall (p1 p2 : pattern) (v : value),
        instance p2 v -> instance (POr p1 p2) v. 

Definition instancet (t : type) (p : patt t) (v : valt t) : Prop :=
    instance (proj1_sig p) (proj1_sig v).

Theorem instance_dec : 
    forall (p : pattern) (v : value),
    {instance p v} + {~ instance p v}.
Proof.
    pose proof type_eq_dec as TED.
    induction p; destruct v;
    try (left; apply instance_wild);
    try (left; apply instance_var);
    try pose proof (IHp1 v1) as IH1;
    try pose proof (IHp2 v2) as IH2;
    try destruct IH1 as [IH1A | IH1B];
    try destruct IH2 as [IH2A | IH2B];
    try (pose proof (TED t1 t0) as TED1;
        pose proof (TED t2 t3) as TED2;
        pose proof (IHp v) as IHI; inversion IHI;
        inversion TED1; inversion TED2; subst);
    try (right; intros HF; inversion HF; auto; assumption);
    try (left; constructor; try assumption).
Qed.

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

Module InstanceRefl <: HasRefl2.
    Definition A := pattern.
    Definition B := value.
    Definition P := instance.
    Definition f := instanceb.
    Theorem refl : forall (a : A) (b : B), P a b <-> f a b = true.
    Proof. intros. apply instance_refl. Qed.
End InstanceRefl.

Module NotInstanceRefl := NotRefl2(InstanceRefl).

Definition vinstancet {n : nat} (t : type) (p : pvt n t) (v : valt t) :=
    exists (i : nat) (Hin : i < n), instancet t (V.nth_order p Hin) v.

Definition linstancet (t : type) (pl : plt t) (v : valt t) :=
    exists (i : nat) (p : patt t), 
        Some p = nth_error pl i /\ instancet t p v.

(* pattern i in p filters v iff
    - p <= v
    - forall j < i, ~ p <= v, i.e. ~ p[0..(i-1)] <= v *)
Definition filters {n : nat} (t : type) (p : pvt n t) (v : valt t) (i : nat) (Hin : i < n) :=
    instancet t (V.nth_order p Hin) v /\
    ~ (vinstancet t (V.take i (lt_le_weak i n Hin) p) v).

Definition filtersl (t : type) (pl : plt t) (v : valt t) (i : nat) :=
    (exists (p : patt t), Some p = nth_error pl i /\ instancet t p v) /\
    ~ (linstancet t (take i pl) v).

(* Definition 4 (Exhaustiveness): *)
Definition exhaustive {n : nat} (t : type) (p : pvt n t) :=
    forall (v : valt t), exists (i : nat) (Hin : i < n),
    filters t p v i Hin.

Definition exhaustivel (t : type) (p : plt t) :=
    forall (v : valt t), exists (i : nat), filtersl t p v i.

(* Definition 5 (Useless Clause): *)
Definition useless_clause 
    {n : nat} (t : type) (p : pvt n t) (i : nat) (Hin : i < n) :=
    ~ exists (v : valt t), filters t p v i Hin.

(* Definition 6 (Useful Clause): *)
Definition upred {n : nat} (t : type) (p : pvt n t) (q : patt t) (v : valt t) := 
    (~ vinstancet t p v) /\ instancet t q v.

Definition upredl (t : type) (p : plt t) (q : patt t) (v : valt t) := 
    (~ linstancet t p v) /\ instancet t q v.

(* U(p,q): *)
Definition U {n : nat} (t : type) (p : pvt n t) (q : patt t) := 
    exists (v : valt t), upred t p q v.

Definition Ul (t : type) (p : plt t) (q : patt t) := 
    exists (v : valt t), upredl t p q v.

(* M(p,q): *)
Definition M {n : nat} (t : type) (p : pvt n t) (q : patt t) := {v : valt t | upred t p q v}.

Lemma Stupid : forall {A : Type} (a : A) (oa : option A),
    oa = Some a -> oa <> None.
Proof.
    unfold not. intros. subst. discriminate.
Qed.

Theorem complete_signature_exhausts :
    forall (t : type) (p : plt t),
    sigma t p <-> ~ Ul t p (exist (pjudge t) PWild (pt_wild t)).
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    unfold Ul. unfold upredl. split; intros.
    { dependent induction H; intros [v [HL HWILD]]; 
        apply HL; unfold linstancet.
        - apply In_nth_error in H as [i NTH].
            exists i. exists (exist (pjudge t) PWild (pt_wild t)).
            symmetry in NTH. split; assumption.
        - apply In_nth_error in H as [i NTH].
            exists i. exists (exist (pjudge t) (PVar x) (pt_name x t)).
            symmetry in NTH. split.
            + assumption.
            + destruct v as [v JV]. 
                unfold instancet. simpl.
                constructor.
        - apply In_nth_error in H as [i NTH].
            exists i. exists (exist (pjudge TUnit) PUnit pt_unit).
            symmetry in NTH. split.
            + assumption.
            + destruct v as [v JV]. inversion JV; subst.
                unfold instancet. simpl. constructor.
        - destruct v as [v JV]. inversion JV; subst.                 
            eapply CPT.not_ex_all_not in IHsigma1 as IH1.
            eapply CPT.not_ex_all_not in IHsigma2 as IH2.
            apply CP.not_and_or in IH1.
            apply CP.not_and_or in IH2.
            destruct IH1 as [IH1 | IH1];
            destruct IH2 as [IH2 | IH2].
            + apply CP.NNPP in IH1. apply CP.NNPP in IH2.
                unfold linstancet

    }



Theorem complete_signature_exhausts' :
    forall (t : type) (p : plt t),
    sigma t p <-> ~ U t (V.of_list p) (exist (pjudge t) PWild (pt_wild t)).
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    unfold U. unfold upred. split; intros.
    { intros [v [HN HI]]. apply HN.
        destruct v as [v JV]. unfold vinstancet.
        induction H.
        - apply In_nth_error in H as [i HIN].
            apply Stupid in HIN as ST.
            apply nth_error_Some in ST.
            exists i. exists ST.
            destruct (V.nth_order (V.of_list p) ST) as [pat JP].
            unfold instancet in *; simpl in *.
            induction JP.
            + assumption.
            + constructor.
            + inversion JV; subst. constructor.
            + inversion JV; subst. constructor.
                *
        unfold instancet in HI. simpl in HI. 
        destruct (V.nth_order (V.of_list p) Hin) as [p JP].
        unfold instancet in *.
         inversion H; subst; try apply STUPID in H0; subst.
        -

      }
    induction t; split; intros. 
    - inversion H; subst; eapply STUPID in H0; subst.
        + intros [v [HV1 HV2]]. apply HV1.
            unfold vinstancet.
            apply In_nth_error in H2.
            destruct H2 as [i NTH]. exists i.
            apply Stupid in NTH as ST.
            apply nth_error_Some in ST.
            exists ST. unfold instancet in *.
            destruct ((V.nth_order (V.of_list p) ST)) eqn:eq.
            simpl in *. destruct x eqn:eqx; try inversion p0; subst.
            * constructor.
            * constructor.
            * destruct v. simpl. inversion v. constructor.
            * destruct v. inversion v; subst. simpl in *.
                induction H2; inversion H3; subst;
                try (constructor; assumption).
                try (apply instance_or_left; constructor);
                try (apply instance_or_right; constructor).
                constructor. constructor.
                constructor. constructor.
                constructor. constructor.
                constructor. constructor.
                constructor. constructor.
                constructor. constructor.
                apply instance_or_right. constructor.
            unfold instancet. simpl. destruct v eqn:eqv.
            destruct x0; try inversion v0; subst. simpl.
            destruct x; try inversion p0; subst.
            * constructor.
            * constructor.
            * constructor.
            * apply instance_or_left. assumption.
            apply instance_unit.
            Search (_ = Some _ <-> _ <> None).
            assert (NOT : nth_error p i <> None).
            * intros H'. 
            
            assert (nth_error p i = nth_error p i).
            reflexivity.
            now rewrite H0 in NTH.
            
            rewrite H' in NTH.
             subst.
            
            remember (nth_error p i) as ne.
Qed.


