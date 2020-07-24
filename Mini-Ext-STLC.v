(* The Simply-Typed Lambda Calculus with minimal extensions,
    with unit, pairs, and either types. 
    
    The algorithm and proof of exhaustive pattern-matching
    is based upon the following one for a strict language:
    http://moscova.inria.fr/~maranget/papers/warn/index.html
    *)

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
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
Require Coq.Sets.Ensembles.
Module E := Coq.Sets.Ensembles.
Module L := Coq.Lists.List.
Require Import Coq.Lists.List.
Import ListNotations.

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

Inductive pattern : Type :=
    | PWild
    | PVar (x : id)
    | PUnit
    | PPair (p1 p2 : pattern)
    | PLeft (t1 t2 : type) (p : pattern)
    | PRight (t1 t2 : type) (p : pattern)
    | POr (p1 p2 : pattern).

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

Definition add_all (f1 : fvt) (f2 : fvt) : fvt :=
    FV.fold (fun x t acc => FV.add x t acc) f1 f2.

Lemma disjoint_add_all : forall (a b : fvt),
    E.Disjoint id (set_of_fv a) (set_of_fv b) ->
    FV.Equal (add_all a b) (add_all b a).
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
        FV.Equal f1 f2 ->
        free_vars (POr p1 p2) t f1.

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
        FV.Equal f1 f2 ->
        pat_type (POr p1 p2) t.

Definition pjudge (t : type) (p : pattern) := pat_type p t.

Definition pvec (n : nat) := V.t pattern n.

Definition pvec_type {n : nat} (p : pvec n) (t : type) := V.Forall (pjudge t) p.

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

Definition filter_pairs' (a b : type) 
    (p : patt (TPair a b)) (acc : (plt a) * (plt b)) : (plt a) * (plt b).
Proof. inversion p. destruct x.
    - apply acc.
    - apply acc.
    - apply acc.
    - assert (H12 : pat_type x1 a /\ pat_type x2 b).
        + inversion H; subst. split; assumption.
        + destruct acc as [av bv]. destruct H12 as [H1 H2].
            apply ((exist (pjudge a) x1 H1)::av,(exist (pjudge b) x2 H2)::bv).
    - apply acc.
    - apply acc.
    - apply acc.
Defined.

Definition filter_pairs (a b : type) : plt (TPair a b) -> (plt a) * (plt b) :=
    fold_right (filter_pairs' a b) ([],[]).

Definition filter_eithers' (a b : type)
    (p : patt (TEither a b)) (acc : (plt a) * (plt b)) : (plt a) * (plt b).
Proof. inversion p. destruct x.
    - apply acc.
    - apply acc.
    - apply acc.
    - apply acc.
    - assert (HL : pat_type x a).
        + inversion H; subst; assumption.
        + destruct acc as [av bv].
            apply ((exist (pjudge a) x HL)::av,bv).
    - assert (HR : pat_type x b).
        + inversion H; subst; assumption.
        + destruct acc as [av bv].
            apply (av,(exist (pjudge b) x HR)::bv).
    - apply acc.
Defined.

Definition filter_eithers (a b : type) : plt (TEither a b) -> (plt a) * (plt b) :=
    fold_right (filter_eithers' a b) ([],[]).

Definition flatten_ors' (t : type) (p : patt t) (acc : plt t) : plt t.
Proof. inversion p. destruct x.
- apply acc.
- apply acc.
- apply acc.
- apply acc.
- apply acc.
- apply acc.
- assert (H12 : pat_type x1 t /\ pat_type x2 t).
    + inversion H; subst; split; assumption.
    + destruct H12 as [H1 H2].
        apply ((exist (pjudge t) x1 H1)::(exist (pjudge t) x2 H2)::acc).
Defined.

Definition flatten_ors (t : type) : plt t -> plt t := 
    fold_right (flatten_ors' t) [].

(* Complete Signature Sigma:
    This was not defined explicitly so I have
    invented a definition to suit my purposes.
    Note this relation does not enforce type-checking,
    this is completeness not correctness. 
    The notion of correctness will be defined
    separately with the typing judgment. *)
Inductive sigma : forall (t : type), plt t -> Prop :=
    | sigma_wild : forall (t : type) (p : list (patt t)),
        In (exist (pjudge t) PWild (pt_wild t)) p -> 
        sigma t p
    | sigma_name : forall (t : type) (p : plt t) (x : id),
        In (exist (pjudge t) (PVar x) (pt_name x t)) p ->
        sigma t p
    | sigma_unit : forall (p : plt TUnit),
        In (exist (pjudge TUnit) PUnit pt_unit) p -> 
        sigma TUnit p
    | sigma_pair : forall (a b : type) (p : plt (TPair a b)) (pa : plt a) (pb : plt b),
        (pa,pb) = filter_pairs a b p ->
        sigma a pa -> 
        sigma b pb ->
        sigma (TPair a b) p
    | sigma_either : forall (a b : type) (p : plt (TEither a b)) (pa : plt a) (pb : plt b),
        (pa,pb) = filter_eithers a b p ->
        sigma a pa ->
        sigma b pb ->
        sigma (TEither a b) p
    | sigma_or : forall (t : type) (p : plt t),
        sigma t (flatten_ors t p) ->
        sigma t p.

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
    | vj_fun : forall (p : pattern) (t t' : type) (e : expr) (H : pat_type p t),
        sigma t [exist (pjudge t) p H] ->
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
        instance p v -> instance (PRight t1 t2 p) (VRight t1 t2 v).

Definition instancet (t : type) (p : patt t) (v : valt t) : Prop :=
    instance (proj1_sig p) (proj1_sig v).

(* Definition 1 (Instance Relation)
Inductive instance : forall (t : type), patt t -> valt t -> Prop :=
    | instance_wild : forall (t : type) (v : valt t), 
        instance t (exist (pjudge t) PWild (pt_wild t)) v
    | instance_name : forall (t : type) (x : id) (v : valt t), 
        instance t (exist (pjudge t) (PVar x) (pt_name x t)) v
    | instance_unit : 
        instance TUnit 
            (exist (pjudge TUnit) PUnit pt_unit) 
            (exist (vjudge TUnit) VUnit vj_unit)
    | instance_pair : forall (a b : type) 
        (pa : patt a) (pb : patt b) (p1 p2 : pattern)
        (H1 : pat_type p1 a) (H2 : pat_type p2 b)
        (f1 f2 : fvt) (HF1 : free_vars p1 a f1) (HF2 : free_vars p2 b f2)
        (HD : E.Disjoint id (set_of_fv f1) (set_of_fv f2))
        (va : valt a) (vb : valt b) (v1 v2 : value)
        (HV1 : val_judge v1 a) (HV2 : val_judge v2 a),
        p1 = proj1_sig pa -> 
        p2 = proj1_sig pb ->
        H1 = proj2_sig pa ->
        H2 = proj2_sig pb ->
        v1 = proj1_sig va ->
        v2 = proj1_sig vb ->
        HV1 = proj2_sig va ->
        HV2 = proj2_sig vb ->
        instance pa va -> 
        instance pb vb -> 
        instance (TPair a b)
            (exist (pjudge (TPair a b)) (PPair p1 p2) (pt_pair p1 p2 a b f1 f2 H1 H2 HF1 HF2))
            (exist (vjudge (TPair a b)) (VPair v1 v2) (vj_pair v1 v2 a b HV1 HV2)).
    | instance_left : forall (t1 t2 : type) (p : pattern) (v : value),
        instance p v -> instance (PLeft t1 t2 p) (VLeft t1 t2 v)
    | instance_right : forall (t1 t2 : type) (p : pattern) (v : value),
        instance p v -> instance (PRight t1 t2 p) (VRight t1 t2 v). *)

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

(* Baby steps for more general exhaustiveness for matrices *)
Module BabyExhaustiveness.

Definition pvec_typeb {n : nat} (p : pvec n) (t : type) :=
    forallb (fun p => pat_typeb p t) p.

Theorem pvec_type_refl : 
    forall {n : nat} (p : pvec n) (t : type),
    pvec_type p t <-> pvec_typeb p t = true.
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    intros n. induction p; split; intros H.
    - reflexivity.
    - constructor.
    - inversion H; subst.
        apply STUPID in H2; try apply Nat.eq_dec; subst.
        simpl. unfold eq_rect_r. simpl.
        apply andb_true_iff. split.
        + apply pat_type_refl. assumption.
        + apply IHp. assumption.
    - simpl in H. unfold eq_rect_r in H. simpl in H.
        apply andb_true_iff in H as [H1 H2].
        constructor.
        + apply pat_type_refl. assumption.
        + apply IHp. assumption. 
Qed.

(* Definition 2 (ML Pattern Matching)
    A Row  i in P filters v iff
    - Pi <= v
    - forall j < i, ~ Pj <= v *)
Definition filters {n : nat} (p : pvec n) (v : value) (i : nat) (Hin : i < n) :=
    instance (V.nth_order p Hin) v /\
    forall (j : nat) (Hji : j < i), ~ instance (V.nth_order p (lt_trans j i n Hji Hin)) v.

(* Definition 3: (Vector Instance Relation) *)
Definition vinstance {n : nat} (ps : pvec n) (v : value) :=
    V.Exists (fun p => instance p v) ps.

Theorem vinstance_dec :
    forall {n : nat} (ps : pvec n) (v : value),
    {vinstance ps v} + {~ vinstance ps v}.
Proof.
    intros. induction ps.
    - right. intros H. inversion H.
    - destruct IHps as [IH | IH].
        + left. apply V.Exists_cons_tl.
            assumption.
        + pose proof (instance_dec h v) as ID.
            destruct ID as [I | NI].
            * left. apply V.Exists_cons_hd.
                assumption.
            * right. intros H. inversion H; subst.
                apply NI. assumption.
                pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
                apply STUPID in H3; try apply Nat.eq_dec; subst.
                apply IH. assumption.
Qed.

Definition vinstanceb {n : nat} (ps : pvec n) (v : value) := 
    existsb (fun p => instanceb p v) ps.

Theorem vinstance_refl : forall {n : nat} (ps : pvec n) (v : value),
    vinstance ps v <-> vinstanceb ps v = true.
Proof.
    intros. unfold vinstance. unfold vinstanceb.
    induction ps; split; intros.
    - inversion H.
    - discriminate H.
    - simpl. unfold eq_rect_r. simpl.
        apply orb_true_iff.
        pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
        inversion H; subst.
        + left. apply instance_refl. assumption.
        + right. apply IHps.
            apply STUPID in H3; subst;
            try apply Nat.eq_dec. assumption.
    - simpl in H. unfold eq_rect_r in H. simpl in H.
        apply orb_true_iff in H as [H | H].
        + apply V.Exists_cons_hd. apply instance_refl.
            assumption.
        + apply V.Exists_cons_tl. apply IHps.
            assumption.
Qed.

Definition vinstance_row {n : nat} (ps : pvec n) (v : value) :=
    exists (i : nat) (Hin : i < n), 
    instance (V.nth_order ps Hin) v.

Import V.VectorNotations.

Fixpoint vinstanceb_row {n : nat} (ps : pvec n) (v : value) : (option nat) :=
    match ps with
    | [] => None
    | h::t =>
        match instanceb h v with
        | true => Some 0
        | false =>
            match vinstanceb_row t v with
            | None => None
            | Some k => Some (S k)
            end
        end
    end.

Lemma vinstance_vinstance_row_refl :
    forall {n : nat} (ps : pvec n) (v : value),
    vinstance ps v <-> vinstance_row ps v.
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    pose proof_irrelevance as PI.
    unfold CF.proof_irrelevance in PI.
    intros. induction ps; split; intros;
    inversion H; subst.
    - destruct H0 as [Hin _]. inversion Hin.
    - apply STUPID in H3; try apply Nat.eq_dec; subst.
        unfold vinstance_row. exists 0. 
        assert (H0Sn : 0 < S n); try omega.
        exists H0Sn. unfold V.nth_order.
        simpl. assumption.
    - apply STUPID in H3; try apply Nat.eq_dec; subst.
        apply IHps in H2. unfold vinstance_row in H2.
        destruct H2 as [i [Hin HI]].
        unfold vinstance_row. exists (S i).
        assert (HSiSn : S i < S n); try omega.
        exists HSiSn. unfold V.nth_order.
        simpl. unfold V.nth_order in HI.
        pose proof (PI (i < n) Hin (lt_S_n i n HSiSn)) as HPI; subst.
        assumption.
    - destruct H0 as [Hin HI].
        unfold vinstance in *.
        unfold vinstance_row in *.
        destruct x as [| x]; cbn in HI.
        + apply V.Exists_cons_hd. assumption.
        + apply V.Exists_cons_tl. apply IHps.
            exists x. exists ((lt_S_n x n Hin)).
            unfold V.nth_order. assumption.
Qed.

Lemma vinstanceb_vinstanceb_row_refl :
    forall {n : nat} (ps : pvec n) (v : value),
    vinstanceb ps v = true <-> 
    exists (i : nat) (Hin : i < n), vinstanceb_row ps v = Some i.
Proof.
    intros. induction ps; split; intros.
    - discriminate H.
    - destruct H as [i [Hi0 _]]. omega.
    - simpl in H. unfold eq_rect_r in H. simpl in H.
        pose proof (instance_dec h v) as ID.
        apply orb_true_iff in H.
        destruct ID as [I | NI] eqn:eqi;
        destruct H as [H' | H'] eqn:eqh; subst.
        + exists 0. assert (H0Sn : 0 < S n); try omega.
            exists H0Sn. simpl.
            rewrite H'. reflexivity.
        + exists 0. assert (H0Sn : 0 < S n); try omega.
            exists H0Sn. simpl.
            apply instance_refl in I.
            rewrite I. reflexivity.
        + apply instance_refl in H'. contradiction.
        + apply IHps in H'. destruct H' as [i [Hin HIV]].
            exists (S i). assert (HSiSn : S i < S n); try omega.
            exists HSiSn. simpl.
            apply NotInstanceRefl.not_refl2 in NI.
            unfold InstanceRefl.f in NI.
            rewrite NI. rewrite HIV.
            reflexivity.
    - destruct H as [i [HiSn HIVR]]. simpl.
        unfold eq_rect_r. simpl. apply orb_true_iff.
        simpl in HIVR. destruct (instanceb h v) eqn:eqib.
        + left. reflexivity.
        + right. destruct (vinstanceb_row ps v) eqn:eqvbr.
            injection HIVR; intros; subst.
            * apply IHps. exists n0.
                assert (Hn0n : n0 < n); try omega.
                exists Hn0n. auto.
            * discriminate.
Qed.

Lemma vinstance_row_refl :
    forall {n : nat} (ps : pvec n) (v : value),
    vinstance_row ps v <-> exists (i : nat) (Hin : i < n), vinstanceb_row ps v = Some i.
Proof.
    split; intros.
    - apply vinstanceb_vinstanceb_row_refl. apply vinstance_refl.
        apply vinstance_vinstance_row_refl. assumption.
    - apply vinstance_vinstance_row_refl. apply vinstance_refl.
        apply vinstanceb_vinstanceb_row_refl. assumption.
Qed.

Lemma vinstanceb_row_bounded :
    forall {n : nat} (ps : pvec n) (v : value) (i : nat),
    vinstanceb_row ps v = Some i -> i < n.
Proof.
    intros. dependent induction ps.
    - discriminate H.
    - simpl in H. destruct (instanceb h v).
        + injection H; intros; subst. omega.
        + destruct (vinstanceb_row ps v) eqn:eq.
            * injection H; intros; subst.
                apply IHps in eq. omega.
            * discriminate H.
Qed.

Lemma vinstance_take_cons :
    forall {n : nat} (p : pattern) (ps : pvec n) 
    (v : value) (m : nat) (HmSn : m <= n),
    ~ instance p v ->
    vinstance (V.take (S m) (le_n_S m n HmSn) (p::ps)) v ->
    vinstance (V.take m HmSn ps) v.
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    intros. dependent induction ps.
    - assert (m = 0); try omega; subst.
        simpl in H0. exfalso. apply H.
        inversion H0; subst.
        + assumption.
        + apply STUPID in H4; try apply Nat.eq_dec; subst.
            inversion H3.
    - destruct m as [| m].
        + cbn in H0. inversion H0; 
            subst; apply STUPID in H4; 
            try apply Nat.eq_dec; subst.
            * contradiction.
            * inversion H3.
        + simpl. simpl in H0. 
            pose proof (instance_dec h v) as [I | NI].
            * apply V.Exists_cons_hd. assumption.
            * apply V.Exists_cons_tl.
                apply IHps; try assumption.
                inversion H0; subst.
                { contradiction. }
                { apply STUPID in H4; try apply Nat.eq_dec; subst.
                    inversion H3; subst. 
                    - contradiction.
                    - apply STUPID in H5; try apply Nat.eq_dec; subst.
                    simpl. apply V.Exists_cons_tl.
                    pose proof proof_irrelevance as PI.
                    unfold CF.proof_irrelevance in PI.
                    pose proof (PI (S m <= S n) 
                        (le_n_S m n (le_S_n m n HmSn)) 
                        (le_S_n (S m) (S n) (le_n_S (S m) (S n) HmSn))) as POOF.
                        rewrite POOF. assumption. }
Qed.

Lemma vinstanceb_row_first :
    forall {n : nat} (ps : pvec n) (v : value) (i : nat),
    vinstanceb_row ps v = Some i ->
    exists (Hin : i <= n), ~ vinstance (V.take i Hin ps) v.
Proof.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    pose proof_irrelevance as PI.
    unfold CF.proof_irrelevance in PI.
    intros. dependent induction ps.
    - discriminate H.
    - apply vinstanceb_row_bounded in H as VB.
        assert (Hin : i <= S n); try omega.
        exists Hin. intros HF.
        cbn in H. destruct (instanceb h v) eqn:eqib.
        + injection H; intros; subst. 
            simpl in HF. inversion HF.
        + destruct (vinstanceb_row ps v) eqn:eqvbr.
            { injection H; intros; subst.
                simpl in HF.
                apply vinstance_refl in HF.
                simpl in HF. unfold eq_rect_r in HF.
                simpl in HF. apply orb_true_iff in HF.
                destruct HF as [HH | HT].
                - rewrite HH in eqib. discriminate.
                - apply vinstance_refl in HT.
                    pose proof (IHps v n0 eqvbr) as [Hn0n IH].
                    apply IH. pose proof (PI (n0 <= n) Hn0n (le_S_n n0 n Hin)).
                    rewrite H0. assumption. }
            { discriminate. } 
Qed.

(* Definition 2 (ML Pattern Matching reformulated with Definition 3) *)
Definition filters' {n : nat} 
    (p : pvec n) (v : value) (i : nat) (Hin : i < n) :=
    (instance (V.nth_order p Hin) v /\ 
    ~ vinstance (V.take i (lt_le_weak i n Hin) p) v).

(* The Versions of Definition 2 are Equivalent *)
Theorem filters_equiv : 
    forall {n : nat} (p : pvec n) (v : value) (i : nat) (Hin : i < n),
    filters p v i Hin <-> filters' p v i Hin.
Proof.
    pose proof VL.nth_take as NT.
    pose proof Eqdep_dec.inj_pair2_eq_dec as STUPID.
    unfold filters. unfold filters'.
    split; intros; destruct H as [H1 H2]; 
    split; try assumption.
    - unfold not. intros NV.
        apply vinstance_vinstance_row_refl in NV.
        unfold vinstance_row in NV.
        destruct NV as [j [Hji HIV]].
        pose proof (H2 j Hji). apply H.
        pose proof (NT pattern n p j i Hji Hin) as NTH.
        rewrite NTH. assumption.
    - intros. intros VI. apply H2.
        pose proof (NT pattern n p j i Hji Hin) as NTH.
        apply vinstance_vinstance_row_refl.
        unfold vinstance_row. exists j. exists Hji.
        rewrite <- NTH. assumption.
Qed.

(* Definition 4 (Exhaustiveness): *)
Definition exhaustive {n : nat} (p : pvec n) :=
    forall (v : value), exists (i : nat) (Hin : i < n),
    filters p v i Hin.

(* Correct, well-typed, Exhaustiveness *)
Definition exhaustive_typed {n : nat} (p : pvec n) (t : type) :=
    pvec_type p t ->
    forall (v : value) (vt : value_type),
    value_judge v vt -> vtt t vt ->
    exists (i : nat) (Hin : i < n), filters p v i Hin.

(* Definition 5 (Useless Clause): *)
Definition useless_clause 
    {n : nat} (p : pvec n) (i : nat) (Hin : i < n) :=
    ~ exists (v : value), filters p v i Hin.

(* Correct, well-typed, Useless Clause *)
Definition useless_clause_typed 
    {n : nat} (p : pvec n) (t : type) (i : nat) (Hin : i < n) :=
    pvec_type p t -> ~ exists (v : value) (vt : value_type),
    value_judge v vt -> vtt t vt -> filters p v i Hin.

(* Definition 6 (Useful Clause): *)
Definition upred {n : nat} (p : pvec n) (q : pattern) (v : value) := 
    (~ vinstance p v) /\ instance q v.

(* Well-typed Useful Clause *)
Definition upred_typed 
    {n : nat} (p : pvec n) (q : pattern) 
    (t : type) (v : value) (vt : value_type) := 
    pvec_type p t -> pat_type q t ->
    value_judge v vt -> vtt t vt ->
    (~ vinstance p v) /\ instance q v.

(* U(p,q): *)
Definition U {n : nat} (p : pvec n) (q : pattern) := 
    exists (v : value), upred p q v.

(* Well-typed U(p,q) *)
Definition UT {n : nat} (p : pvec n) (q : pattern) (t : type) := 
    exists (v : value) (vt : value_type), upred_typed p q t v vt.

(* M(p,q): *)
Definition M {n : nat} (p : pvec n) (q : pattern) := {v : value | upred p q v}.

(* Well-typed M(p,q): *)
Definition MT {n : nat} (p : pvec n) (q : pattern) (t : type) := 
    {v : value | exists (vt : value_type), upred_typed p q t v vt}.

Lemma vinstanceb_row_instance :
    forall {n : nat} (p : pvec n) (v : value) (i : nat) (Hin : i < n),
    vinstanceb_row p v = Some i -> instance (V.nth_order p Hin) v.
Proof.
    intros. dependent induction p; try omega.
    simpl in H. destruct (instanceb h v) eqn:eqihv.
    - injection H; intros; subst. cbn. 
        apply instance_refl. assumption.
    - destruct (vinstanceb_row p v) eqn:eqvrow.
        + injection H; intros; subst.
            cbn. apply IHp. assumption.
        + discriminate.
Qed.

(* Proposition 1.1: *)
Theorem exhaustive_cond : 
    forall {n : nat} (p : pvec n),
    exhaustive p <-> ~ U p PWild.
Proof.
    unfold exhaustive; unfold U; unfold upred; 
    split; intros.
    - intros [v UP]. specialize H with (v := v).
        destruct H as [i [Hin [H1 H2]]].
        apply UP. apply vinstance_vinstance_row_refl.
        exists i. exists Hin. assumption.
    - eapply CPT.not_ex_all_not in H.
        eapply CP.not_and_or in H as [H | H].
        + apply CP.NNPP in H.
            unfold vinstance in H.
            eapply vinstance_vinstance_row_refl in H.
            eapply vinstance_row_refl in H as VRR.
            destruct VRR as [i [Hin VBR]].
            exists i. exists Hin. apply filters_equiv. split.
            * apply vinstanceb_row_instance. apply VBR.
            * apply vinstanceb_row_first in VBR.
                destruct VBR as [Hin' NV].
                pose proof_irrelevance as PI.
                pose proof (PI (i <= n) Hin' (Nat.lt_le_incl i n Hin)).
                rewrite <- H0. apply NV.
        + exfalso. apply H. constructor.
Qed.

(* Well-typed Proposition 1.1: *)
Theorem exhaustive_cond_typed :
    forall {n : nat} (p : pvec n) (t : type),
    exhaustive_typed p t <-> ~ UT p PWild t.
Proof.
    unfold exhaustive_typed; unfold UT; 
    unfold upred_typed; split; intros.
    - intros [v [vt POP]].
        specialize H with (v := v). 
Admitted.
    
(* Proposition 1.2: *)
Theorem useless_cond : 
    forall {n : nat} (p : pvec n) (i : nat) (Hin : i < n),
    useless_clause p i Hin <-> 
    ~ U (V.take i (lt_le_weak i n Hin) p) (V.nth p (F.of_nat_lt Hin)).
Proof.
    unfold useless_clause; unfold U; 
    unfold upred; split; intros.
    - intros [v [NV IP]]. apply H. exists v.
        apply filters_equiv. split; try assumption.
    - intros [v FH]. apply filters_equiv in FH. 
        apply H. exists v. 
        destruct FH as [FH1 FH2]. split; assumption. 
Qed.

(* Well-typed Proposition 1.2: *)
Theorem useless_cond_typed :
    forall {n : nat} (p : pvec n) (t : type) (i : nat) (Hin : i < n),
    useless_clause_typed p t i Hin <->
    ~ UT (V.take i (lt_le_weak i n Hin) p) (V.nth p (F.of_nat_lt Hin)) t.
Proof.
Admitted. 

(* is a pattern a constructed pattern? *)
Inductive cp : pattern -> Prop :=
    | cp_unit : cp PUnit
    | cp_pair : forall (p1 p2 : pattern), cp (PPair p1 p2)
    | cp_left : forall (t1 t2 : type) (p : pattern), cp (PLeft t1 t2 p)
    | cp_right : forall (t1 t2 : type) (p : pattern), cp (PRight t1 t2 p).

Definition cpb (p : pattern) : bool :=
    match p with
    | PUnit 
    | PPair _ _
    | PLeft _ _ _
    | PRight _ _ _ => true
    | PWild 
    | PVar _ => false
    end.

Theorem cp_refl : forall (p : pattern), cp p <-> cpb p = true.
Proof.
    destruct p; split; intros; 
    try inversion H; try discriminate;
    try reflexivity; try constructor.
Qed.

Definition constructor_pattern := {p : pattern | cp p}.

End BabyExhaustiveness.

(* Below are is the full-formulation of 
    exhaustiveness, as a matrix based 
    algoeithm. It is simply an asbtracted
    formulation of exhaustiveness *)
Module AdvancedExhaustiveness.

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
    (vinstance (V.nth_order p Him) v /\ 
    forall (j : nat) (Hji : j < i),
    ~ vinstance (V.nth_order p (lt_trans j i m Hji Him)) v).

(* Definition 3 (Instance Relation for Matrices): *)
Definition minstance
    {m n : nat} (p : pmatrix m n) (v : vvec n) :=
    exists (i : nat) (Him : i < m), 
    vinstance (V.nth_order p Him) v.

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
    (vinstance (V.nth_order p Him) v /\ 
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

Import V.VectorNotations.

Fixpoint minstance_row 
    {m n : nat} (pmat : pmatrix m n) (v : vvec n) : option nat :=
    match pmat with
    | [] => None
    | p::t => 
        if vinstanceb p v then Some 0
        else match minstance_row t v with
        | None => None
        | Some k => Some (S k)
        end
    end.

(* If P <= v, then there exists a row i in P
    such that i is the first such row to filter v. *)
Theorem minstance_row_filters :
    forall {m n : nat} (p : pmatrix m n) (v : vvec n),
    minstance p v <-> 
    exists (i : nat) (Him : i < m), row_filters i p v Him.
Proof.
    (* intros. dependent induction p; split; intros.
    - inversion H; subst. destruct H0 as [Him _].
        inversion Him.
    - destruct H as [i [Him _]].
        inversion Him.
    - inversion H. destruct H0 as [Him HV].
        apply minstance_refl in H as MR.
        simpl in MR. unfold eq_rect_r in MR. 
        simpl in MR. apply orb_true_iff in MR as [MR | MR].
        + exists 0. assert (HiSn0 : 0 < S n0); try omega.
            exists HiSn0. unfold row_filters. split.
            * simpl. apply vinstance_refl. assumption.
            * intros. inversion Hji.
        + destruct x as [| i].
            { exists 0. exists Him.
                unfold row_filters. split.
                - assumption.
                - intros. inversion Hji. }
            { exists (S i). exists Him.
                apply minstance_refl in MR as MRR.
                apply IHp in MRR as IH.
                unfold row_filters. split.
                + assumption.
                + intros. unfold not. intros HVI.
                    destruct IH as [k [Hkn0 [IH1 IH2]]].
                    eapply IH2.
            }
        
        exists x. exists Him.
            unfold row_filters.
        destruct x as [| i].
        + exists 0. exists Him.
            unfold row_filters. split.
            * simpl. simpl in HV. assumption.
            * intros. inversion Hji.
        + simpl in HV.
            apply minstance_refl in H as MR.   
            exists (S i). exists Him.
            simpl in MR. unfold eq_rect_r in MR.
            simpl in MR. apply orb_true_iff in MR.
            destruct MR.
            * simpl in HV.
            unfold row_filters. split.
            * assumption.
            * intros. unfold not.
                intros HVI. *)
Admitted.

Fixpoint wild_vec (n : nat) : pvec n :=
    match n with
    | 0 => []
    | S k => PWild::wild_vec k
    end.

Lemma wild_vinstance : 
    forall (n : nat) (v : vvec n),
    vinstance (wild_vec n) v.
Proof.
    intros. induction v; constructor.
    - apply instance_wild.
    - fold wild_vec. unfold vinstance in IHv.
        assumption.
Qed.

(* Proposition 1.1: *)
Theorem exhaustive_cond' :
    forall {m n : nat} (p : pmatrix m n),
    exhaustive' p <-> ~ U p (wild_vec n).
Proof.
Admitted.

Theorem exhaustive_cond : 
    forall {m n : nat} (p : pmatrix m n),
    exhaustive p <-> ~ U p (wild_vec n).
Proof.
Admitted.

(* Proposition 1.2: *)
Theorem useless_cond : 
    forall {m n : nat} (p : pmatrix m n) (i : nat) (Him : i < m),
    useless_clause p i Him <-> 
    ~ U (V.take i (lt_le_weak i m Him) p) (V.nth p (F.of_nat_lt Him)).
Proof.
Admitted.

End AdvancedExhaustiveness.