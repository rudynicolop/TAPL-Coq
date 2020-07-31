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

Module VL := VectorLemmas.

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
    Module NM := NotRefl2(M).
    Theorem forall2_not_refl : 
        forall {n : nat} (va : V.t M.A n) (vb : V.t M.B n),
        ~ V.Forall2 M.P va vb <-> forall2b M.f va vb = false.
    Proof.
        induction n; split; intros.
        - exfalso. pose proof (vect_nil va) as VA.
            pose proof (vect_nil vb) as VB. apply H.
            subst. constructor.
        - pose proof (vect_nil va) as VA. pose proof (vect_nil vb) as VB.
            subst. discriminate H.
        - pose proof (vect_cons va) as [ha [ta VA]].
            pose proof (vect_cons vb) as [hb [tb VB]].
            subst. simpl. unfold eq_rect_r. simpl.
            destruct (M.f ha hb) eqn:eqf.
            + apply M.refl in eqf. simpl. apply IHn. 
                intros HF. apply H. constructor; assumption.
            + apply andb_false_iff. left. reflexivity.
        - pose proof (vect_cons va) as [ha [ta VA]].
            pose proof (vect_cons vb) as [hb [tb VB]].
            subst. simpl in *. unfold eq_rect_r in H.
            simpl in H. intros HF. inversion HF; subst.
            pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
            apply STUPID in H2; apply STUPID in H5;
            try apply Nat.eq_dec; subst.
            apply M.refl in H4. rewrite H4 in H.
            simpl in H. apply IHn in H. contradiction.
    Qed.  
    Lemma forall2_nth : 
        forall {n : nat} (va : V.t M.A n) (vb : V.t M.B n),
        V.Forall2 M.P va vb -> 
        forall {i : nat} (H : i < n), M.P (V.nth_order va H) (V.nth_order vb H).
    Proof.
        pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
        induction n; intros; try omega.
        pose proof (vect_cons va) as [ha [ta VA]].
        pose proof (vect_cons vb) as [hb [tb VB]].
        subst. inversion H; subst. destruct i as [| i].
        - cbn. assumption.
        - assert (Hin : i < n); try omega.
            pose proof (proof_irrelevance 
                (S i < S n) H0 (lt_n_S i n Hin)) as Hin'.
            rewrite Hin'. rewrite <- VL.nth_cons.
            rewrite <- VL.nth_cons.
            apply STUPID in H3; try apply Nat.eq_dec.
            apply STUPID in H6; try apply Nat.eq_dec.
            subst. specialize IHn with (va := ta) (vb := tb).
            eapply IHn in H7. apply H7.
    Qed.
End VectorForall2Refl.

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

Module IdSet := WS.Make(IdDec).

Definition ws_of_fv (fv : fvt) : (IdSet.t) :=
    FV.fold (fun x _ acc => IdSet.add x acc) fv (IdSet.empty).

Definition ws_disjoint (a b : IdSet.t) := IdSet.is_empty (IdSet.inter a b).

Lemma disjoint_refl : forall (f1 f2 : fvt),
    E.Disjoint id (set_of_fv f1) (set_of_fv f2) <-> 
    ws_disjoint (ws_of_fv f1) (ws_of_fv f2) = true.
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
            if ws_disjoint (ws_of_fv f1) (ws_of_fv f2)
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
        destruct (ws_disjoint (ws_of_fv f0) (ws_of_fv f1)) eqn:eqd;
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
            if ws_disjoint (ws_of_fv f1) (ws_of_fv f2)
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
        destruct (ws_disjoint (ws_of_fv f) (ws_of_fv f0)) eqn:eqd;
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

Module PatternTypeRefl <: HasRefl2.
    Definition A := pattern.
    Definition B := type.
    Definition P := pat_type.
    Definition f := pat_typeb.
    Theorem refl : forall (a : A) (b : B), P a b <-> f a b = true.
    Proof. apply pat_type_refl. Qed.
End PatternTypeRefl.

Definition pjudge (t : type) (p : pattern) := pat_type p t.

Definition patt (t : type) := {p : pattern | pat_type p t}.

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
    | rc_or_intros_right : forall (p1 p2 : pattern) (c : construct),
        root_construct p2 c ->
        root_construct (POr p1 p2) c.

Fixpoint root_constructb (p : pattern) (c : construct) : bool :=
    match p, c with
    | PUnit, CUnit
    | PPair _ _, CPair => true
    | PLeft a b _, CLeft a' b'
    | PRight a b _, CRight a' b' =>
        type_eqb a a' && type_eqb b b'
    | POr p1 p2, _ =>
        root_constructb p1 c || root_constructb p2 c
    | _, _ => false
    end.

Lemma root_construct_refl :
    forall (p : pattern) (c : construct),
    root_construct p c <-> root_constructb p c = true.
Proof.
    induction p; split;
    intros H; try inversion H; subst;
    simpl in *; try discriminate;
    try reflexivity;
    try (apply andb_true_iff; split; apply type_eq_refl; reflexivity);
    try (destruct c; try discriminate; 
        apply andb_true_iff in H1 as [H1 H2];
        apply type_eq_refl in H1; apply type_eq_refl in H2;
        subst; constructor);
    try (apply orb_true_iff; left; apply IHp1; assumption);
    try (apply orb_true_iff; right; apply IHp2; assumption).
    - destruct c; try discriminate; constructor.
    - destruct c; try discriminate; constructor.
    - apply orb_true_iff in H1 as [H1 | H1].
        + apply rc_or_intros_left. apply IHp1. assumption.
        + apply rc_or_intros_right. apply IHp2. assumption.
Qed.

Definition rct {t : type} (p : patt t) := root_construct (proj1_sig p).

Definition rctb {t : type} (p : patt t) := root_constructb (proj1_sig p).

Module PatternWS := WS.Make(PatternDec).
Module PWS := PatternWS.

Definition pws_judge (t : type) (s : PWS.t) :=
    PWS.For_all (pjudge t) s.

(* Complete Signature Sigma *)
Inductive sigma (p : PWS.t) : type -> Prop :=
    | sigma_unit :
        pws_judge TUnit p ->
        PWS.Exists (fun p' => root_construct p' CUnit) p ->
        sigma p TUnit
    | sigma_pair : forall (a b : type),
        pws_judge (TPair a b) p -> 
        PWS.Exists (fun p' => root_construct p' CPair) p ->
        sigma p (TPair a b)
    | sigma_either : forall (a b : type),
        pws_judge (TEither a b) p ->
        PWS.Exists (fun p' => root_construct p' (CLeft a b)) p ->
        PWS.Exists (fun p' => root_construct p' (CRight a b)) p ->
        sigma p (TEither a b).

Definition sigmab (p : PWS.t) (t : type) (H : pws_judge t p) :=
    match t with
    | TUnit => PWS.exists_ (fun p' => root_constructb p' CUnit) p
    | TPair a b => PWS.exists_ (fun p' => root_constructb p' CPair) p
    | TEither a b => 
        PWS.exists_ (fun p' => root_constructb p' (CLeft a b)) p &&
        PWS.exists_ (fun p' => root_constructb p' (CRight a b)) p
    | TFun _ _ => false
    end.

Ltac proper :=
    unfold Morphisms.Proper;
    unfold Morphisms.respectful;
    intros; subst; reflexivity.

Ltac unfold_Exists H :=
    unfold PWS.Exists in *;
    destruct H as [x [HE HZ]]; exists x; 
    apply root_construct_refl in HZ;
    split; assumption.

Lemma sigma_refl :
    forall (t : type) (p : PWS.t) (H : pws_judge t p),
    sigma p t <-> sigmab p t H = true.
Proof.
    destruct t; split; intros HS;
    try inversion HS; subst; simpl in *;
    try discriminate; 
    try constructor;
    try assumption; 
    try (apply andb_true_iff; split);
    try (apply andb_true_iff in H1 as [H1 H2]);
    try apply PWS.exists_spec;
    try apply PWS.exists_spec in H1;
    try apply PWS.exists_spec in H2;
    try proper;
    try unfold_Exists H1;
    try unfold_Exists H2;
    try unfold_Exists H3;
    try unfold_Exists H4.
Qed.       

Lemma sigma_refl_not :
    forall (t : type) (p : PWS.t) (H : pws_judge t p),
    ~ sigma p t <-> sigmab p t H = false.
Proof.
    split; intros.
    - destruct (sigmab p t H) eqn:eq.
        + apply sigma_refl in eq. contradiction.
        + reflexivity.
    - intros H1. apply (sigma_refl t p H) in H1.
        rewrite H0 in H1. discriminate.
Qed.

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
        pat_type p t ->
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

Fixpoint val_judgeb (v : value) (t : type) : bool :=
    match v,t with
    | VUnit, TUnit => true
    | VFun p t' _, TFun t'' _ =>
        type_eqb t' t'' && pat_typeb p t'
    | VPair v1 v2, TPair a b =>
        val_judgeb v1 a && val_judgeb v2 b
    | VLeft a b v, TEither a' b' =>
        type_eqb a a' && type_eqb b b' && val_judgeb v a
    | VRight a b v, TEither a' b' =>
        type_eqb a a' && type_eqb b b' && val_judgeb v b
    | _, _ => false
    end.

Lemma val_judge_refl : forall (v : value) (t : type),
    val_judge v t <-> val_judgeb v t = true.
Proof.
    induction v; destruct t; split; intros H;
    try inversion H; subst; simpl in *;
    try discriminate H; try constructor;
    try reflexivity;
    try (apply andb_true_iff in H1 as [H1 H2];
        apply (IHv1 t1) in H1; apply (IHv2 t2) in H2;
        assumption);
    try (apply andb_true_iff; split;
        try (apply andb_true_iff; split;
        apply type_eq_refl; reflexivity);
        try (apply pat_type_refl; assumption));
    try (destruct t; try discriminate;
        destruct t3 eqn:eq3; try discriminate);
    try (apply pat_type_refl; assumption);
    try (apply IHv1; assumption);
    try (apply IHv2; assumption);
    try (apply IHv; assumption);
    try (apply andb_true_iff in H1 as [HT H3];
        apply andb_true_iff in HT as [H1 H2];
        apply type_eq_refl in H1;
        apply type_eq_refl in H2;
        try apply pat_type_refl in H3; 
        try apply IHv in H3; subst; 
        constructor; assumption).
    destruct t; try discriminate.
    destruct t1 eqn:eq1; try discriminate.
    apply andb_true_iff in H1 as [_ H2].
    constructor. apply pat_type_refl. assumption.
Qed.

Module VJudgeRefl <: HasRefl2.
    Definition A := value.
    Definition B := type.
    Definition P := val_judge.
    Definition f := val_judgeb.
    Theorem refl : forall (a : A) (b : B), P a b <-> f a b = true.
    Proof. intros. apply val_judge_refl. Qed.
End VJudgeRefl.

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

Ltac instance_dec_or IHp1 IHp2 v :=
    pose proof (IHp1 v) as IH1;
    pose proof (IHp2 v) as IH2;
    destruct IH1 as [IH1OA | IH1OB];
    destruct IH2 as [IH2OA | IH2OB];
    try (right; intros HF; inversion HF; auto; assumption);
    left; try (apply instance_or_left; assumption);
    try (apply instance_or_right; assumption).

Theorem instance_dec : 
    forall (p : pattern) (v : value),
    {instance p v} + {~ instance p v}.
Proof.
    pose proof type_eq_dec as TED.
    induction p; 
    destruct v;
    try (left; apply instance_wild);
    try (left; apply instance_var);
    try pose proof (IHp1 v1) as IH1;
    try pose proof (IHp2 v2) as IH2;
    try destruct IH1 as [IH1A | IH1B];
    try destruct IH2 as [IH2A | IH2B];
    try (pose proof (TED t1 t0) as TED1;
        pose proof (TED t2 t3) as TED2;
        pose proof (IHp v) as IHI; inversion IHI;
        inversion TED1; inversion TED2; subst;
        destruct IHI; destruct TED1; destruct TED2; subst);
    try (right; intros HF; inversion HF; auto; assumption);
    try (left; constructor; assumption);
    try instance_dec_or IHp1 IHp2 (VPair v1 v2).
    - instance_dec_or IHp1 IHp2 VUnit.
    - instance_dec_or IHp1 IHp2 (VFun p t e).
    - instance_dec_or IHp1 IHp2 (VLeft t1 t2 v).
    - instance_dec_or IHp1 IHp2 (VRight t1 t2 v).
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
    | POr p1 p2, _ => instanceb p1 v || instanceb p2 v
    | _, _ => false
    end.

Theorem instance_refl : forall (p : pattern) (v : value),
    instance p v <-> instanceb p v = true.
Proof.
    induction p; destruct v; split; intros; 
    try reflexivity;
    try apply instance_wild;
    try apply instance_var;
    try apply instance_unit;
    try apply instance_pair;
    try apply instance_left;
    try apply instance_right;
    try discriminate H; try inversion H; 
    subst; simpl in *;
    try (apply andb_true_iff; split;
        try (apply IHp; assumption);
        apply andb_true_iff; split;
        apply type_eq_refl; reflexivity);
    try (apply andb_true_iff in H as [H1'' H3'];
        apply andb_true_iff in H1'' as [H1' H2'];
        apply type_eq_refl in H1';
        apply type_eq_refl in H2';
        subst; apply IHp in H3';
        constructor; assumption);
    try (apply orb_true_iff;
        try (left; apply IHp1; assumption);
        try (right; apply IHp2; assumption));
    try (apply orb_true_iff in H1 as [H1 | H1];
        try (apply instance_or_left; apply IHp1; assumption);
        try (apply instance_or_right; apply IHp2; assumption)).
    - apply IHp1 in H3. apply IHp2 in H5.
        rewrite H3. rewrite H5. reflexivity.
    - apply IHp1. apply andb_true_iff in H as [H2 _].
        assumption.
    - apply andb_true_iff in H as [_ H2].
        apply IHp2. assumption.
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

Definition instancet {t : type} (p : patt t) (v : valt t) : Prop :=
    instance (proj1_sig p) (proj1_sig v).

Definition instancebt {t : type} (p : patt t) (v : valt t) : bool :=
    instanceb (proj1_sig p) (proj1_sig v).

Theorem instancet_refl :
    forall {t : type} (p : patt t) (v : valt t),
    instancet p v <-> instancebt p v = true.
Proof. intros. apply instance_refl. Qed.

Definition pvec (n : nat) := V.t pattern n.

Definition vvec (n : nat) := V.t value n.

Definition tvec (n : nat) := V.t type n.

Definition pjudge_vec {n : nat} (p : pvec n) (t : @tvec n) :=
    V.Forall2 pat_type p t.

Definition pjudgeb_vec {n : nat} (p : pvec n) (t : @tvec n) :=
    forall2b pat_typeb p t.

Module PatJudgeVecRefl := VectorForall2Refl(PatternTypeRefl).

Lemma pjudge_vec_refl :
    forall {n : nat} (p : pvec n) (t : tvec n),
    pjudge_vec p t <-> pjudgeb_vec p t = true.
Proof. intros. apply PatJudgeVecRefl.forall2_refl. Qed.

Definition vjudge_vec {n : nat} (v : vvec n) (t : @tvec n) :=
    V.Forall2 val_judge v t.

Definition vjudgeb_vec {n : nat} (v : vvec n) (t : @tvec n) :=
    forall2b val_judgeb v t.

Module VJudgeVecRefl := VectorForall2Refl(VJudgeRefl).

Lemma vjudge_vec_refl :
    forall {n : nat} (v : vvec n) (t : tvec n),
    vjudge_vec v t <-> vjudgeb_vec v t = true.
Proof. intros. apply VJudgeVecRefl.forall2_refl. Qed.

Definition pvt {n : nat} (t : tvec n) :=
    {p : @pvec n | pjudge_vec p t}.

Definition vvt {n : nat} (t : tvec n) :=
    {v : @vvec n | vjudge_vec v t}.

Definition pvt_nth {n i : nat} {t : tvec n}
    (p : pvt t) (H : i < n) : patt (V.nth_order t H).
Proof.
    destruct p as [p pj]. simpl in *.
    pose proof (PatJudgeVecRefl.forall2_nth p t pj H) as HT.
    apply (exist (pjudge (V.nth_order t H)) (V.nth_order p H) HT). 
Defined.

Definition vvt_nth {n i : nat} {t : tvec n}
    (v : vvt t) (H : i < n) : valt (V.nth_order t H).
Proof.
    destruct v as [v vj]. simpl in *.
    pose proof (VJudgeVecRefl.forall2_nth v t vj H) as HT.
    apply (exist (vjudge (V.nth_order t H)) (V.nth_order v H) HT). 
Defined.

Definition vinstancet {n : nat} {t : tvec n} (p : pvt t) (v : vvt t) : Prop :=
    V.Forall2 instance (proj1_sig p) (proj1_sig v).

Definition vinstancebt {n : nat} {t : tvec n} (p : pvt t) (v : vvt t) : bool :=
    forall2b instanceb (proj1_sig p) (proj1_sig v).

Module VInstanceRefl := VectorForall2Refl(InstanceRefl).

Theorem vinstancet_refl :
    forall {n : nat} {t : tvec n} (p : pvt t) (v : vvt t),
    vinstancet p v <-> vinstancebt p v = true.
Proof. intros. apply VInstanceRefl.forall2_refl. Qed.

Definition pmt {n : nat} (t : tvec n) := list (@pvt n t).

Definition minstancet {n : nat} {t : tvec n} (p : pmt t) (v : vvt t) :=
    List.Exists (fun p' => vinstancet p' v) p.

Definition minstancebt {n : nat} {t : tvec n} (p : pmt t) (v : vvt t) :=
    List.existsb (fun p' => vinstancebt p' v) p.

Lemma minstancet_refl :
    forall {n : nat} {t : @tvec n} (p : pmt t) (v : vvt t),
    minstancet p v <-> minstancebt p v = true.
Proof.
    unfold minstancet. unfold minstancebt.
    split; intros.
    - apply existsb_exists. apply Exists_exists in H as [x [HIn HIV]].
        exists x. apply vinstancet_refl in HIV. split; assumption.
    - apply Exists_exists. apply existsb_exists in H as [x [HIn HIV]].
        exists x. apply vinstancet_refl in HIV. split; assumption.
Qed.

Definition row_filters {n : nat} {t : tvec n}
    (p : pmt t) (v : vvt t) (i : nat) :=
    (exists (row : pvt t), Some row = nth_error p i
    /\ vinstancet row v) /\ ~ minstancet (take i p) v.

Fixpoint row_filters_op {n : nat} {t : tvec n}
    (p : pmt t) (v : vvt t) : option nat :=
    match p with
    | nil => None
    | ph::pt => 
        if vinstancebt ph v then Some 0 else 
        match row_filters_op pt v with
        | None => None
        | Some k => Some (S k)
        end
    end.

Lemma row_filters_op_minstancebt :
    forall {n : nat} {t : tvec n} (p : pmt t) (v : vvt t),
    minstancebt p v = true <-> exists i, row_filters_op p v = Some i.
Proof.
    intros. dependent induction p; 
    split; intros; try discriminate; simpl in *.
    - destruct H as [i H]. discriminate.
    - specialize IHp with (v := v).
        destruct (vinstancebt a v) eqn:vin.
        + exists 0. reflexivity.
        + simpl in H. apply IHp in H as [i H].
            exists (S i). rewrite H. reflexivity.
    - destruct H as [i H].
        destruct (vinstancebt a v) eqn:vin;
        destruct (row_filters_op p v) eqn:rf;
        simpl in *; try reflexivity; try discriminate.
        apply (IHp v). exists n0. apply rf.
Qed.

Lemma nth_error_nil :
    forall {A : Type} (i : nat),
    @nth_error A [] i = None.
Proof. intros. induction i; try reflexivity. Qed.


Lemma row_filters_refl :
    forall {n : nat} {t : tvec n} (p : pmt t) (v : vvt t) (i : nat),
    row_filters p v i <-> row_filters_op p v = Some i.
Proof.
    intros. dependent induction p; split; intros H;
    simpl in *; try discriminate; try inversion H; subst.
    - destruct H0 as [row [HF _]]. 
        rewrite nth_error_nil in HF. discriminate.
    - destruct H0 as [row [SR HIV]].
        destruct i as [| i]; simpl in *.
        + injection SR; intros; subst.
            apply vinstancet_refl in HIV. 
            rewrite HIV. reflexivity.
        + destruct (vinstancebt a v) eqn:eq.
            { exfalso. apply H1. constructor.
                apply vinstancet_refl. assumption. }
            { assert (HRF : row_filters p v i).
                - unfold row_filters. split.
                    + exists row. split; assumption.
                    + intros HF. apply H1.
                        apply Exists_cons_tl.
                        assumption.
                - apply IHp in HRF. rewrite HRF.
                    reflexivity. }
    - destruct (vinstancebt a v) eqn:eq.
        + injection H1; intros; subst.
            unfold row_filters. split.
            * exists a. split; try reflexivity.
                apply vinstancet_refl. assumption.
            * intros HM. inversion HM.
        + destruct (row_filters_op p v) eqn:eqrf.
            { injection H1; intros; subst.
                apply IHp in eqrf. unfold row_filters in *.
                destruct eqrf as [[row [SR HIV]] NHM].
                split.
                - exists row. split.
                    + simpl. assumption.
                    + assumption.
                - simpl. intros NSHM. apply NHM.
                    inversion NSHM; subst.
                    + apply VInstanceRefl.forall2_not_refl in eq.
                        contradiction.
                    + assumption. }
            { discriminate. }
Qed.

Lemma row_filters_minstancet :
    forall {n : nat} {t : tvec n} (p : pmt t) (v : vvt t),
    minstancet p v <-> exists i, row_filters p v i.
Proof.
    split; intros.
    - apply minstancet_refl in H. 
        apply row_filters_op_minstancebt in H as [i H].
        exists i. apply row_filters_refl. assumption.
    - destruct H as [i H]. apply minstancet_refl.
        apply row_filters_op_minstancebt. exists i.
        apply row_filters_refl. assumption.
Qed.      

(* Definition 4 (Exhaustiveness): *)
Definition exhaustive {n : nat} {t : tvec n} (p : pmt t) :=
    forall (v : vvt t), exists (i : nat), row_filters p v i.

(* Definition 5 (Useless Clause): *)
Definition useless_clause 
    {n : nat} {t : tvec n} (p : pmt t) (i : nat) :=
    ~ exists (v : vvt t), row_filters p v i.

(* Definition 6 (Useful Clause): *)
Definition upred {n : nat} {t : tvec n} (p : pmt t) (q : pvt t) (v : vvt t) := 
    (~ minstancet p v) /\ vinstancet q v.

(* U(p,q): *)
Definition U {n : nat} {t : tvec n} (p : pmt t) (q : pvt t) := 
    exists (v : vvt t), upred p q v.

(* M(p,q): *)
Definition M {n : nat} {t : tvec n} (p : pmt t) (q : pvt t) := {v : vvt t | upred p q v}.

Import V.VectorNotations.

Fixpoint pwild_vec (n : nat) : @pvec n :=
    match n with
    | 0 => []
    | S k => PWild :: pwild_vec k
    end.

Definition pwildt_vec {n : nat} (t : tvec n) : pvt t.
Proof.
    assert (HW : pjudge_vec (pwild_vec n) t).
    - induction t.
        + constructor.
        + constructor.
            * constructor.
            * apply IHt.
    - apply (exist (fun p => pjudge_vec p t) (pwild_vec n) HW).
Defined.

Lemma pwild_vec_instance :
    forall {n : nat} {t : tvec n} (v : vvt t),
    vinstancet (pwildt_vec t) v.
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    intros. destruct v as [v vj]. 
    unfold vinstancet. simpl. induction v.
    - constructor.
    - inversion vj; subst. 
        apply STUPID in H1; try apply Nat.eq_dec.
        apply STUPID in H2; try apply Nat.eq_dec.
        subst. constructor.
        + constructor.
        + eapply IHv. apply H4.
Qed.

Lemma PNNP : forall (P : Prop), P -> ~ ~ P.
Proof. intros. intros NP. apply NP. assumption. Qed.

Theorem exhaustive_wild :
    forall {n : nat} {t : @tvec n} (p : pmt t),
    exhaustive p <-> ~ U p (pwildt_vec t).
Proof.
    unfold exhaustive; unfold U; 
    unfold upred; split; intros.
    - apply CPT.all_not_not_ex. intros v.
        apply CP.or_not_and.
        specialize H with (v := v).
        destruct H as [i [RF1 RF2]].
        destruct RF1 as [row [SR VI]].
        left. apply PNNP. unfold minstancet.
        apply Exists_exists. exists row. split.
        + eapply nth_error_In. symmetry. apply SR.
        + assumption.
    - pose proof CPT.not_ex_all_not as NEAN.
        specialize NEAN with (n := v).
        apply NEAN in H. clear NEAN.
        apply CP.not_and_or in H.
        destruct H as [H | H].
        + apply CP.NNPP in H.
            apply row_filters_minstancet. assumption.
        + exfalso. apply H. apply pwild_vec_instance.
Qed.

Theorem useless_row :
    forall {n : nat} {t : tvec n} (p : pmt t) (i : nat) (row : pvt t),
    nth_error p i = Some row ->
    useless_clause p i <-> ~ U (take i p) row.
Proof.
    unfold useless_clause. unfold U. unfold upred. split; intros.
    - intros [v [NM HIV]]. apply H0. exists v.
        unfold row_filters. split.
        + exists row. symmetry in H. split; assumption.
        + assumption.
    - intros [v [[row' [SR HIV]] NM]]. apply H0.
        exists v. split; try assumption.
        rewrite H in SR. injection SR; intros; 
        subst; assumption.
Qed.

(* The Specialized Matrix *)

Definition empty_pvt : pvt [].
Proof.
    assert (H : pjudge_vec [] []); try constructor.
    apply (exist (fun p' => pjudge_vec p' []) [] H).
Defined.

Definition empty_vvt : vvt [].
Proof.
    assert (H : vjudge_vec [] []); try constructor.
    apply (exist (fun v' => vjudge_vec v' []) [] H).
Defined.

Definition hd_tl_pvt {n : nat} {th : type} {t : tvec n}  (p : pvt (th::t)) : patt th * pvt t.
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    destruct p as [p pj].
    assert (H : pat_type (V.hd p) th /\ pjudge_vec (V.tl p) t).
    - inversion pj; subst.
        apply STUPID in H0;
        apply STUPID in H2;
        try apply Nat.eq_dec; subst.
        simpl; split; assumption.
    - destruct H as [H1 H2].
        apply (exist (pjudge th) (V.hd p) H1, exist (fun p' => pjudge_vec p' t) (V.tl p) H2).
Defined.

Definition cons_pvt {n : nat} {t : tvec n} 
    {a : type} (r : patt a) (p : pvt t) : pvt (a::t).
Proof.
    destruct p as [p pj]. destruct r as [r rj].
    assert (H : pjudge_vec (r::p) (a::t)).
    - constructor; assumption.
    - apply (exist (fun p' => pjudge_vec p' (a::t)) (r::p) H).
Defined.

(* separate first column *)
Fixpoint first_column {n : nat} {th : type} {t : tvec n} 
    (p : pmt (th::t)) : list (patt th * pvt t) :=
    match p with
    | nil => nil
    | (row::rest)%list => 
        (hd_tl_pvt row :: first_column rest)%list
    end.

Definition PWS_first_column {n : nat} {th : type} {t : tvec n} (p : pmt (th::t)) : PWS.t :=
    fold_right (fun r acc => PWS.add (proj1_sig (fst r)) acc) PWS.empty (first_column p).

(* Specialized Matrix for Unit *)

Fixpoint SUnit_row {n : nat} {t : tvec n} (r : pattern) (row : pvt t) : pmt t :=
    match r with
    | PWild 
    | PVar _ 
    | PUnit => [row]%list
    | POr r1 r2 => (SUnit_row r1 row ++ SUnit_row r2 row)%list
    | _ => nil
    end.

Fixpoint SUnit {n : nat} {t : tvec n} (p : list (patt TUnit * (pvt t))) : pmt t :=
    match p with
    | nil => nil
    | ((r,row)::p')%list => (SUnit_row (proj1_sig r) row ++ SUnit p')%list
    end.

(* Specialized Matrix for Pair *)

Fixpoint SPair_row {n : nat} {t : tvec n} 
    {a b : type} (r : pattern) 
    (H : pat_type r (TPair a b)) (row : pvt t) : pmt (a::b::t).
Proof.
    destruct row as [rw rowj] eqn:eqrow. destruct r.
    - assert (HPV : pjudge_vec (PWild::PWild::rw) (a::b::t)).
        + constructor; constructor; try constructor; try assumption.
        + pose proof (exist (fun p' => pjudge_vec p' (a::b::t)) 
            (PWild::PWild::rw) HPV) as A. apply [A]%list.
    - assert (HPV : pjudge_vec (PWild::PWild::rw) (a::b::t)).
        + constructor; constructor; try constructor; try assumption.
        + pose proof (exist (fun p' => pjudge_vec p' (a::b::t)) 
            (PWild::PWild::rw) HPV) as A. apply [A]%list.
    - exfalso. inversion H.
    - assert (HPV : pjudge_vec (r1::r2::rw) (a::b::t)).
        + inversion H; subst. constructor; 
            try constructor; try assumption.
        + pose proof (exist (fun p' => pjudge_vec p' (a::b::t)) 
            (r1::r2::rw) HPV) as A. apply [A]%list.
    - exfalso. inversion H.
    - exfalso. inversion H.
    - assert (HR : pat_type r1 (TPair a b) /\ pat_type r2 (TPair a b)).
        + inversion H; subst; split; assumption.
        + destruct HR as [HR1 HR2]. 
            pose proof (SPair_row n t a b r1 HR1 row) as A.
            pose proof (SPair_row n t a b r2 HR2 row) as B.
            apply (A ++ B)%list.
Defined.

Fixpoint SPair {n : nat} {t : tvec n} {a b : type}
    (p : list (patt (TPair a b) * (pvt t))) : pmt (a::b::t) :=
    match p with
    | nil => nil
    | ((r,row)::p')%list => 
        ((SPair_row (proj1_sig r) (proj2_sig r) row) ++ SPair p')%list
    end.

Fixpoint SLeft_row {n : nat} {t : tvec n} {a b : type}
    (r : pattern) (H : pat_type r (TEither a b)) (row : pvt t) : pmt (a::t).
Proof.
    destruct row as [rw rj] eqn:eqrow. destruct r.
    - assert (HPV : pjudge_vec (PWild::rw) (a::t)).
        + constructor; try constructor; try assumption.
        + pose proof (exist (fun p'=> pjudge_vec p' (a::t))
            (PWild::rw) HPV) as A. apply [A]%list.
    - assert (HPV : pjudge_vec (PWild::rw) (a::t)).
        + constructor; try constructor; try assumption.
        + pose proof (exist (fun p'=> pjudge_vec p' (a::t))
            (PWild::rw) HPV) as A. apply [A]%list.
    - exfalso. inversion H.
    - exfalso. inversion H.
    - assert (HPV : pjudge_vec (r::rw) (a::t)).
        + inversion H; subst. constructor;
            try constructor; assumption.
        + pose proof (exist (fun p' => pjudge_vec p' (a::t)) 
            (r::rw) HPV) as A. apply [A]%list.
    - apply nil.
    - assert (HR : pat_type r1 (TEither a b) 
        /\ pat_type r2 (TEither a b)).
        + inversion H; subst. split; assumption.
        + destruct HR as [HR1 HR2].
            pose proof (SLeft_row n t a b r1 HR1 row) as A.
            pose proof (SLeft_row n t a b r2 HR2 row) as B.
            apply (A ++ B)%list.
Defined.

Fixpoint SLeft {n : nat} {t : tvec n} {a b : type}
    (p : list (patt (TEither a b) * (pvt t))) : pmt (a::t) :=
    match p with
    | nil => nil
    | ((r,row)::p')%list => 
        ((SLeft_row (proj1_sig r) (proj2_sig r) row) ++ SLeft p')%list
    end.

Fixpoint SRight_row {n : nat} {t : tvec n} {a b : type}
    (r : pattern) (H : pat_type r (TEither a b)) (row : pvt t) : pmt (b::t).
Proof.
    destruct row as [rw rj] eqn:eqrow. destruct r.
    - assert (HPV : pjudge_vec (PWild::rw) (b::t)).
        + constructor; try constructor; try assumption.
        + pose proof (exist (fun p'=> pjudge_vec p' (b::t))
            (PWild::rw) HPV) as A. apply [A]%list.
    - assert (HPV : pjudge_vec (PWild::rw) (b::t)).
        + constructor; try constructor; try assumption.
        + pose proof (exist (fun p'=> pjudge_vec p' (b::t))
            (PWild::rw) HPV) as A. apply [A]%list.
    - exfalso. inversion H.
    - exfalso. inversion H.
    - apply nil.
    - assert (HPV : pjudge_vec (r::rw) (b::t)).
        + inversion H; subst. constructor;
            try constructor; assumption.
        + pose proof (exist (fun p' => pjudge_vec p' (b::t)) 
            (r::rw) HPV) as A. apply [A]%list.
    - assert (HR : pat_type r1 (TEither a b) 
        /\ pat_type r2 (TEither a b)).
        + inversion H; subst. split; assumption.
        + destruct HR as [HR1 HR2].
            pose proof (SRight_row n t a b r1 HR1 row) as A.
            pose proof (SRight_row n t a b r2 HR2 row) as B.
            apply (A ++ B)%list.
Defined.

Fixpoint SRight {n : nat} {t : tvec n} {a b : type}
    (p : list (patt (TEither a b) * (pvt t))) : pmt (b::t) :=
    match p with
    | nil => nil
    | ((r,row)::p')%list => 
        ((SRight_row (proj1_sig r) (proj2_sig r) row) ++ SRight p')%list
    end.

Fixpoint D_row {n : nat} {t : tvec n} (r : pattern) (row : pvt t) : pmt t.
    destruct r eqn:eqr.
    - apply [row]%list.
    - apply [row]%list.
    - apply nil.
    - apply nil.
    - apply nil.
    - apply nil.
    - pose proof (D_row n t p1 row) as A.
        pose proof (D_row n t p2 row) as B.
        apply (A ++ B)%list.
Defined.
(* default matrix *)
Fixpoint D {n : nat} {th : type} {t : tvec n} 
    (p : list (patt th * (pvt t))) : pmt t :=
    match p with
    | nil => nil
    | ((r,row)::p')%list => 
        (D_row (proj1_sig r) row ++ D p')%list
    end.

    Inductive URec : forall {n : nat} {t : tvec n}, pmt t -> pvt t -> Prop :=
        (* Base Case, n = 0 *)
        | urec_empty : URec nil empty_pvt
        (* q0 = unit *)
        | urec_q0_unit : forall {n : nat} {t : tvec n} 
            (p : pmt (TUnit::t)) (q : pvt (TUnit::t)) (qt : pvt t),
            (exist _ PUnit pt_unit,qt) = hd_tl_pvt q ->
            URec (SUnit (first_column p)) qt ->
            URec p q
        (* q0 = (r1,r2) *)
        | urec_q0_pair : forall {n : nat} {a b : type} {t : tvec n} 
            (p : pmt ((TPair a b)::t)) (q : pvt ((TPair a b)::t)) 
            (qh : patt (TPair a b)) (qt : pvt t) (r1 : patt a) (r2 : patt b),
            (qh,qt) = hd_tl_pvt q ->
            proj1_sig qh = PPair (proj1_sig r1) (proj1_sig r2) ->
            URec (SPair (first_column p)) (cons_pvt r1 (cons_pvt r2 qt)) ->
            URec p q
        (* q0 = Left a b r *)
        | urec_q0_either_left : forall {n : nat} {a b : type} {t : tvec n} 
            (p : pmt ((TEither a b)::t)) (q : pvt ((TEither a b)::t)) 
            (qh : patt (TEither a b)) (qt : pvt t) (r : patt a),
            (qh,qt) = hd_tl_pvt q ->
            proj1_sig qh = PLeft a b (proj1_sig r) ->
            URec (SLeft (first_column p)) (cons_pvt r qt) ->
            URec p q
        (* q0 = Right a b r *)
        | urec_q0_either_right : forall {n : nat} {a b : type} {t : tvec n} 
            (p : pmt ((TEither a b)::t)) (q : pvt ((TEither a b)::t)) 
            (qh : patt (TEither a b)) (qt : pvt t) (r : patt b),
            (qh,qt) = hd_tl_pvt q ->
            proj1_sig qh = PRight a b (proj1_sig r) ->
            URec (SRight (first_column p)) (cons_pvt r qt) ->
            URec p q
        (* q0 = _ : unit, p's first column's signature is complete *)
        | urec_wild_complete_unit : forall {n : nat} {t : tvec n}
            (p : pmt (TUnit::t)) (q : pvt (TUnit::t)) (qt : pvt t),
            (exist _ PWild (pt_wild TUnit), qt) = hd_tl_pvt q ->
            sigma (PWS_first_column p) TUnit ->
            URec (SUnit (first_column p)) qt ->
            URec p q
        (* q0 = _ : a * b, p's first column's signature is complete *)
        | urec_wild_complete_pair : forall {n : nat} {t : tvec n} {a b : type}
            (p : pmt (TPair a b :: t)) (q : pvt (TPair a b :: t)) (qt : pvt t),
            (exist _ PWild (pt_wild (TPair a b)), qt) = hd_tl_pvt q ->
            sigma (PWS_first_column p) (TPair a b) ->
            URec (SPair (first_column p)) 
                (cons_pvt (exist _ PWild (pt_wild a)) (cons_pvt (exist _ PWild (pt_wild b)) qt)) ->
            URec p q
        (* q0 = _ : a + b, p's first column's signature is complete *)
        | urec_wild_complete_either : forall {n : nat} {t : tvec n} {a b : type}
            (p : pmt (TEither a b :: t)) (q : pvt (TEither a b :: t)) (qt : pvt t),
            (exist _ PWild (pt_wild (TEither a b)), qt) = hd_tl_pvt q ->
            sigma (PWS_first_column p) (TEither a b) ->
            URec (SLeft (first_column p))
                (cons_pvt (exist _ PWild (pt_wild a)) qt) \/
            URec (SRight (first_column p))
                (cons_pvt (exist _ PWild (pt_wild b)) qt) ->
            URec p q
        (* q0 = _, p's first column's signature is incomplete *)
        | urec_wild_incomplete : forall {n : nat} {a : type} {t : tvec n} 
            (p : pmt (a::t)) (q : pvt (a::t)) (qt : pvt t),
            (exist _ PWild (pt_wild a), qt) = hd_tl_pvt q ->
            ~ sigma (PWS_first_column p) a ->
            URec (D (first_column p)) qt ->
            URec p q
        (* q0 = x : unit, p's first column's signature is complete *)
        | urec_var_complete_unit : forall {n : nat} {t : tvec n} (x : id)
            (p : pmt (TUnit::t)) (q : pvt (TUnit::t)) (qt : pvt t),
            (exist _ (PVar x) (pt_name x TUnit), qt) = hd_tl_pvt q ->
            sigma (PWS_first_column p) TUnit ->
            URec (SUnit (first_column p)) qt ->
            URec p q
        (* q0 = x : a * b, p's first column's signature is complete *)
        | urec_var_complete_pair : forall {n : nat} {t : tvec n} {a b : type} (x : id)
            (p : pmt (TPair a b :: t)) (q : pvt (TPair a b :: t)) (qt : pvt t),
            (exist _ (PVar x) (pt_name x (TPair a b)), qt) = hd_tl_pvt q ->
            sigma (PWS_first_column p) (TPair a b) ->
            URec (SPair (first_column p)) 
                (cons_pvt (exist _ PWild (pt_wild a)) (cons_pvt (exist _ PWild (pt_wild b)) qt)) ->
            URec p q
        (* q0 = x : a + b, p's first column's signature is complete *)
        | urec_var_complete_either : forall {n : nat} {t : tvec n} {a b : type} (x : id)
            (p : pmt (TEither a b :: t)) (q : pvt (TEither a b :: t)) (qt : pvt t),
            (exist _ (PVar x) (pt_name x (TEither a b)), qt) = hd_tl_pvt q ->
            sigma (PWS_first_column p) (TEither a b) ->
            URec (SLeft (first_column p))
                (cons_pvt (exist _ PWild (pt_wild a)) qt) \/
            URec (SRight (first_column p))
                (cons_pvt (exist _ PWild (pt_wild b)) qt) ->
            URec p q
        (* q0 = x, p's first column's signature is incomplete *)
        | urec_var_incomplete : forall {n : nat} {a : type} {t : tvec n} (x : id)
            (p : pmt (a::t)) (q : pvt (a::t)) (qt : pvt t),
            (exist _ (PVar x) (pt_name x a), qt) = hd_tl_pvt q ->
            ~ sigma (PWS_first_column p) a ->
            URec (D (first_column p)) qt ->
            URec p q
        (* q0 is an or-pattern *)
        | urec_or_pat : forall {n : nat} {a : type} {t : tvec n} 
            (p : pmt (a::t)) (q : pvt (a::t)) (qh : patt a) (qt : pvt t) 
            (r1 r2 : patt a),
            (qh,qt) = hd_tl_pvt q ->
            proj1_sig qh = POr (proj1_sig r1) (proj1_sig r2) ->
            URec p (cons_pvt r1 qt) \/ URec p (cons_pvt r2 qt) ->
            URec p q.

Lemma first_column_pws_judge :
    forall {n : nat} {a : type} {t : tvec n} (p : pmt (a::t)),
    pws_judge a (PWS_first_column p).
Proof.
Admitted.

Ltac irrelevant_pat_type_proof eqhtq qhj p t pf :=
    rewrite eqhtq; pose proof (proof_irrelevance 
        (pat_type p t) qhj pf) as PIH;
    rewrite PIH; reflexivity.

Ltac irrelevant_wild_pat_type_proof eqhtq qhj t :=
    irrelevant_pat_type_proof eqhtq qhj PWild t (pt_wild t).

Ltac wild_urec_simpl eqhtq qhj t :=
    try irrelevant_wild_pat_type_proof eqhtq qhj t;
    try assumption.

Ltac irrelevant_var_type_proof eqhtq qhj t x :=
    irrelevant_pat_type_proof eqhtq qhj (PVar x) t (pt_name x t).

Ltac var_urec_simpl eqhtq qhj t x :=
    try irrelevant_var_type_proof eqhtq qhj t x;
    try assumption.

Lemma U_SUnit : forall {n : nat} {t : tvec n} 
    (p : pmt (TUnit::t)) (q : pvt (TUnit::t)) 
    (qh : patt TUnit) (qt : pvt t),
    (qh,qt) = hd_tl_pvt q ->
    U p q <-> U (SUnit (first_column p)) qt.
Proof.
Admitted.

Lemma U_SPair : forall {n : nat} {t : tvec n} {a b : type}
    (p : pmt (TPair a b :: t)) (q : pvt (TPair a b :: t)) 
    (qh : patt (TPair a b)) (qt : pvt t) 
    (r1 : patt a) (r2 : patt b) (qt : pvt t),
    (qh,qt) = hd_tl_pvt q ->
    proj1_sig qh = PPair (proj1_sig r1) (proj1_sig r2) ->
    U p q <-> U (SPair (first_column p)) (cons_pvt r1 (cons_pvt r2 qt)).
Proof.
Admitted.

Lemma U_SLeft : forall {n : nat} {a b : type} {t : tvec n} 
    (p : pmt ((TEither a b)::t)) (q : pvt ((TEither a b)::t)) 
    (qh : patt (TEither a b)) (qt : pvt t) (r : patt a),
    (qh,qt) = hd_tl_pvt q ->
    proj1_sig qh = PLeft a b (proj1_sig r) ->
    U p q <-> U (SLeft (first_column p)) (cons_pvt r qt).
Proof.
Admitted.

Lemma U_SRight : forall {n : nat} {a b : type} {t : tvec n} 
    (p : pmt ((TEither a b)::t)) (q : pvt ((TEither a b)::t)) 
    (qh : patt (TEither a b)) (qt : pvt t) (r : patt b),
    (qh,qt) = hd_tl_pvt q ->
    proj1_sig qh = PRight a b (proj1_sig r) ->
    U p q <-> U (SRight (first_column p)) (cons_pvt r qt).
Proof.
Admitted.

Lemma U_SPair_wild : forall {n : nat} {t : tvec n} {a b : type}
    (p : pmt (TPair a b :: t)) (q : pvt (TPair a b :: t)) (qt : pvt t),
    (exist _ PWild (pt_wild (TPair a b)), qt) = hd_tl_pvt q ->
    U p q <->
    U (SPair (first_column p)) 
        (cons_pvt (exist _ PWild (pt_wild a)) (cons_pvt (exist _ PWild (pt_wild b)) qt)).
Proof.
Admitted.

Lemma U_SPair_var : forall {n : nat} {t : tvec n} {a b : type} (x : id)
    (p : pmt (TPair a b :: t)) (q : pvt (TPair a b :: t)) (qt : pvt t),
    (exist _ (PVar x) (pt_name x (TPair a b)), qt) = hd_tl_pvt q ->
    U p q <->
    U (SPair (first_column p)) 
        (cons_pvt (exist _ PWild (pt_wild a)) (cons_pvt (exist _ PWild (pt_wild b)) qt)).
Proof.
Admitted.

Lemma U_SEither_wild : forall {n : nat} {t : tvec n} {a b : type}
    (p : pmt (TEither a b :: t)) (q : pvt (TEither a b :: t)) (qt : pvt t),
    (exist _ PWild (pt_wild (TEither a b)), qt) = hd_tl_pvt q ->
    U p q <->
    U (SLeft (first_column p))
        (cons_pvt (exist _ PWild (pt_wild a)) qt) \/
    U (SRight (first_column p))
        (cons_pvt (exist _ PWild (pt_wild b)) qt).
Proof.
Admitted.

Lemma U_SEither_var : forall {n : nat} {t : tvec n} {a b : type} {x : id}
    (p : pmt (TEither a b :: t)) (q : pvt (TEither a b :: t)) (qt : pvt t),
    (exist _ (PVar x) (pt_name x (TEither a b)), qt) = hd_tl_pvt q ->
    U p q <->
    U (SLeft (first_column p))
        (cons_pvt (exist _ PWild (pt_wild a)) qt) \/
    U (SRight (first_column p))
        (cons_pvt (exist _ PWild (pt_wild b)) qt).
Proof.
Admitted.

Theorem URec_correct :
    forall {n : nat} {t : tvec n} (p : pmt t) (q : pvt t), 
    U p q <-> URec p q. 
Proof.
    pose proof proof_irrelevance as PI. unfold CF.proof_irrelevance in PI.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    intros n. induction t; split; intros.
    - destruct q as [q qj]. destruct p.
        + inversion qj. apply STUPID in H0; try apply Nat.eq_dec; subst.
            pose proof urec_empty as URE. unfold empty_pvt in URE. 
            pose proof (PI (pjudge_vec [] []) qj (V.Forall2_nil pat_type)) as PEqj.
            rewrite PEqj. assumption.
        + unfold U in H. unfold upred in H.
            destruct H as [v [NM HIV]].
            destruct v as [v vj]. exfalso.
            apply NM. apply minstancet_refl.
            reflexivity.
    - destruct q as [q qj]. destruct p.
        + unfold U. exists empty_vvt.
            unfold upred. split.
            * intros HM. apply minstancet_refl in HM.
                simpl in HM. discriminate.
            * unfold vinstancet. simpl.
                pose proof (vect_nil q) as QN; subst.
                constructor.
        + inversion H.
    - destruct (hd_tl_pvt q) as [qh qt] eqn:eqhtq. 
        destruct qh as [qh' qhj] eqn:eqqh. destruct qh'.
        { pose proof (first_column_pws_judge p) as FCPWS.
            destruct (sigmab (PWS_first_column p) h FCPWS) eqn:eqsigma.
            - apply sigma_refl in eqsigma. destruct h.
                + apply (urec_wild_complete_unit p q qt); 
                    wild_urec_simpl eqhtq qhj TUnit.
                    apply IHt. eapply U_SUnit.
                    * symmetry. apply eqhtq.
                    * assumption.
                + inversion eqsigma.
                + apply (urec_wild_complete_pair p q qt);
                    wild_urec_simpl eqhtq qhj (TPair h1 h2). admit.
                + apply (urec_wild_complete_either p q qt);
                    wild_urec_simpl eqhtq qhj (TEither h1 h2). admit.
            - apply sigma_refl_not in eqsigma.
                apply (urec_wild_incomplete p q qt);
                wild_urec_simpl eqhtq qhj h. admit. }
        { pose proof (first_column_pws_judge p) as FCPWS.
            destruct (sigmab (PWS_first_column p) h FCPWS) eqn:eqsigma.
            - apply sigma_refl in eqsigma. destruct h.
                + apply (urec_var_complete_unit x p q qt);
                    var_urec_simpl eqhtq qhj TUnit x.
                    apply IHt. eapply U_SUnit.
                    * symmetry. apply eqhtq.
                    * assumption.
                + inversion eqsigma.
                + apply (urec_var_complete_pair x p q qt);
                    var_urec_simpl eqhtq qhj (TPair h1 h2) x. admit.
                + apply (urec_var_complete_either x p q qt);
                    var_urec_simpl eqhtq qhj (TEither h1 h2) x. admit.
            - apply sigma_refl_not in eqsigma.
                apply (urec_var_incomplete x p q qt);
                var_urec_simpl eqhtq qhj h x. admit. }
        { inversion qhj; subst. apply (urec_q0_unit p q qt);
            try irrelevant_pat_type_proof eqhtq qhj PUnit TUnit pt_unit. 
            apply IHt.
            admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
    -
Admitted.

Definition pat_to_pvt (t : type) (p : pattern) (H : pat_type p t) : pvt [t].
Proof.
    assert (HV : pjudge_vec [p] [t]).
    - constructor.
        + assumption.
        + constructor.
    - apply (exist (fun p' => pjudge_vec p' [t]) [p] HV).
Defined.

Fixpoint pats_to_pmt (t : type) (ps : list pattern) (H : Forall (pjudge t) ps) : pmt [t].
Proof.
    destruct ps.
    - apply nil.
    - assert (HP : pat_type p t /\ Forall (pjudge t) ps).
        + inversion H; subst. split; assumption.
        + destruct HP as [HP HPS].
            apply (pat_to_pvt t p HP :: pats_to_pmt t ps HPS)%list.
Defined.

Inductive exhausts 
    (t : type) (ps : list pattern) : Prop :=
    exhaust : forall (H : Forall (pjudge t) ps),
        exhaustive (pats_to_pmt t ps H) -> 
        exhausts t ps.

(* Gamma *)
Definition gamma := id -> option type.

Definition empty : gamma := fun x => None.

Definition bind (x : id) (t : type) (g : gamma) : gamma :=
    fun y => if String.eqb x y then Some t else g y.

Lemma bind_correct : 
    forall (x : id) (t : type) (g : gamma),
    bind x t g x = Some t.
Proof.
    intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
    - reflexivity.
    - apply eqb_neq in eq. contradiction.
Qed. 

Lemma bind_complete :
    forall (x x' : id) (t t' : type) (g : gamma),
    x' <> x -> (g x = Some t <-> bind x' t' g x = Some t). 
Proof.
    intros. unfold bind. apply eqb_neq in H. 
    rewrite H. split; intros; apply H0.
Qed.

Lemma rebind_correct : 
    forall (x : id) (t t' : type) (g : gamma),
    bind x t g = bind x t (bind x t' g).
Proof.
    intros. apply functional_extensionality. intros y.
    unfold bind. destruct ((x =? y)%string); reflexivity.
Qed.

Lemma bind_diff_comm : 
    forall (x y : id) (u v : type) (g : gamma),
    x <> y ->
    bind x u (bind y v g) = bind y v (bind x u g).
Proof.
    - intros. apply functional_extensionality. intros z.
        unfold bind. destruct ((x =? z)%string) eqn:eq.
        + apply String.eqb_eq in eq; subst.
            destruct ((y =? z)%string) eqn:eeq.
            * apply String.eqb_eq in eeq; subst. contradiction.
            * reflexivity.
        + apply eqb_neq in eq. destruct ((y =? z)%string) eqn:eeq; reflexivity.
Qed.

Inductive pat_bind (g : gamma) : pattern -> type -> gamma -> Prop :=
    | pb_wild : forall (t : type), 
        pat_bind g PWild t g
    | pb_name : forall (x : id) (t : type),
        pat_bind g (PVar x) t (bind x t g)
    | pb_unit : pat_bind g PUnit TUnit g
    | pb_pair : forall (p1 p2 : pattern) (a b : type) (f1 f2 : fvt) (g' g'' : gamma),
        free_vars p1 a f1 ->
        free_vars p2 b f2 ->
        E.Disjoint id (set_of_fv f1) (set_of_fv f2) ->
        pat_bind g p1 a g' ->
        pat_bind g' p2 b g'' ->
        pat_bind g (PPair p1 p2) (TPair a b) g''.

Inductive check (g : gamma) : expr -> type -> Prop :=
    | check_unit : check g EUnit TUnit
    | check_name : forall (x : id) (t : type), 
        g x = Some t -> check g (EVar x) t
    | check_fun : forall (p : pattern) (t t' : type) (e : expr) (g' : gamma),
        pat_type p t -> 
        exhausts t [p] -> 
        pat_bind g p t g' ->
        check g' e t' ->
        check g (EFun p t e) (TFun t t').

(* Inductive expr : Type :=
| EFun (p : pattern) (t : type) (e : expr)
| EApp (e1 e2 : expr)
| EPair (e1 e2 : expr)
| EProj (e : expr) (n : nat)
| ELeft (t1 t2 : type) (e : expr)
| ERight (t1 t2 : type) (e : expr)
| EMatch (e : expr) (cases : list (pattern * expr)). *)
