(* The Simply-Typed Lambda Calculus with minimal extensions,
    with unit, pairs, and either types. 
    
    The algorithm and proof of exhaustive pattern-matching
    is based upon the following one for a strict language:
    http://moscova.inria.fr/~maranget/papers/warn/index.html
    *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Coq.Vectors.Fin.
Module F := Coq.Vectors.Fin.
Require Coq.Vectors.Vector.
Module V := Coq.Vectors.Vector.
Require Import Omega.
Require Coq.Logic.ClassicalFacts.
Module CF := Coq.Logic.ClassicalFacts.
Require Import Coq.Sets.Ensembles.
Require Coq.Logic.Classical_Pred_Type.
Module CPT := Coq.Logic.Classical_Pred_Type.
Require Coq.Logic.Classical_Prop.
Module CP := Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.

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

Module Type HasRefl2.
Parameter A : Type.
Parameter B : Type.
Parameter P : A -> B -> Prop.
Parameter f : A -> B -> bool.
Axiom refl : forall (a : A) (b : B), P a b <-> f a b = true.
End HasRefl2.

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

Definition pvec (n : nat) := V.t pattern n.

Definition pmatrix (m n : nat) := V.t (pvec n) m.

Definition vvec (n : nat) := V.t value n.

(* Definition 1 (Vector Instance Relation) *)
Definition vinstance 
    {n : nat} (p : pvec n) (v : vvec n) := 
    V.Forall2 instance p v.

Definition vinstanceb 
    {n : nat} (p : pvec n) (v : vvec n) : bool :=
    forall2b instanceb p v.

Module InstanceRefl <: HasRefl2.
Definition A := pattern.
Definition B := value.
Definition P := instance.
Definition f := instanceb.
Theorem refl : forall (a : A) (b : B), P a b <-> f a b = true.
Proof. apply instance_refl. Qed.
End InstanceRefl.

Module PV := VectorForall2Refl(InstanceRefl).

Theorem vinstance_refl : forall {n : nat} (p : pvec n) (v : vvec n),
    vinstance p v <-> vinstanceb p v = true. 
Proof. intros. apply (PV.forall2_refl p v). Qed.

(* Definition 2 (ML Pattern Matching)
    A Row  i in P filters v iff
    - Pi <= v
    - forall j < i, ~ Pj <= v *)
Definition row_filters 
    {m n : nat} (i : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m) :=
    (vinstance (V.nth p (F.of_nat_lt Him)) v /\ 
    forall (j : nat) (Hji : j < i),
    ~ vinstance (V.nth p (F.of_nat_lt (lt_trans j i m Hji Him))) v).

(* Definition 3 (Instance Relation for Matrices): *)
Definition minstance
    {m n : nat} (p : pmatrix m n) (v : vvec n) :=
    exists (i : nat) (Him : i < m), 
    vinstance (V.nth p (F.of_nat_lt Him)) v.

Definition minstanceb
    {m n : nat} (p : pmatrix m n) (v : vvec n) : bool :=
    existsb (fun p' => vinstanceb p' v) p.

Theorem minstance_refl : 
    forall {m n : nat} (p : pmatrix m n) (v : vvec n),
    minstance p v <-> minstanceb p v = true.
Proof.
    unfold minstance. unfold minstanceb. 
    induction m; split; intros.
    - destruct H as [i [Him HV]].
        inversion Him.
    - discriminate H.
    - destruct H as [i [Him HV]].
        pose proof (vect_cons p) as [h [t VC]]; subst.
        simpl. unfold eq_rect_r. simpl.
        apply orb_true_iff.
        induction i.
        + simpl in HV. left. apply vinstance_refl.
            assumption.
        + right. apply IHm. exists i.
            assert (HO : i < m); try omega.
            exists HO. simpl in HV.
            pose proof proof_irrelevance as PI.
            unfold CF.proof_irrelevance in PI.
            pose proof (PI (i < m) HO ((lt_S_n i m Him))) as PIHim.
            rewrite PIHim. assumption.
    - pose proof (vect_cons p) as [h [t VC]]; subst.
        simpl in H. unfold eq_rect_r in H.
        simpl in H. apply orb_true_iff in H as [H| H].
        + exists 0. assert (Him : 0 < S m); try omega.
            exists Him. simpl. apply vinstance_refl.
            assumption.
        + apply IHm in H. destruct H as [i [Him H]].
            exists (S i). assert (HSiSm : S i < S m); try omega.
            exists HSiSm. 
            pose proof proof_irrelevance as PI.
            unfold CF.proof_irrelevance in PI.
            pose proof VL.nth_cons as NC.
            pose proof (NC (pvec n) i m h t Him).
            pose proof (PI (S i < S m) HSiSm (lt_n_S i m Him)).
            rewrite H1. rewrite <- H0.
            assumption.
Qed.

(* Definition 2 (ML Pattern Matching reformulated with Definition 3) *)
Definition row_filters' {m n : nat} 
    (i : nat) (p : pmatrix m n) (v : vvec n) (Him : i < m) :=
    (vinstance (V.nth p (F.of_nat_lt Him)) v /\ 
    ~ minstance (V.take i (lt_le_weak i m Him) p) v).

(* The Versions of Definition 2 are Equivalent *)
Theorem row_filters_equiv : 
    forall {m n : nat} (p : pmatrix m n) (v : vvec n) (i : nat) (Him : i < m),
    row_filters i p v Him <-> row_filters' i p v Him.
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

(* Definition 4 (Exhaustiveness): *)
Definition exhaustive' {m n : nat} (p : pmatrix m n) := 
    forall (v : vvec n), exists (i : nat) (Him : i < m),
    row_filters' i p v Him.

Definition exhaustive {m n : nat} (p : pmatrix m n) :=
    forall (v : vvec n), exists (i : nat) (Him : i < m),
    row_filters i p v Him.

(* Definition 5 (Useless Clause): *)
Definition useless_clause'
    {m n : nat} (p : pmatrix m n) (i : nat) (Him : i < m) := 
    ~ exists (v : vvec n), row_filters' i p v Him.

Definition useless_clause 
    {m n : nat} (p : pmatrix m n) (i : nat) (Him : i < m) :=
    ~ exists (v : vvec n), row_filters i p v Him.

(* Definition 6 (Useful Clause): *)
Definition upred {m n : nat} (p : pmatrix m n) (q : pvec n) (v : vvec n) := 
    (~ minstance p v) /\ vinstance q v.

(* U(p,q): *)
Definition U {m n : nat} (p : pmatrix m n) (q : pvec n) := 
    exists (v : vvec n), upred p q v.

(* M(p,q): *)
Definition M {m n : nat} (p : pmatrix m n) (q : pvec n) := {v : vvec n | upred p q v}.

(* If P <= v, then there exists a row i in P
    such that i is the first such row to filter v. *)
Theorem minstance_row_filters :
    forall {m n : nat} (p : pmatrix m n) (v : vvec n),
    minstance p v <-> 
    exists (i : nat) (Him : i < m), row_filters i p v Him.
Proof.
Admitted.