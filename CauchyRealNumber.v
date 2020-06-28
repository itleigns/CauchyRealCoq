Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.IndefiniteDescription.
Require Export QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Coq.Logic.PropExtensionality.

Lemma sig_map : forall {T : Type} (P : T -> Prop) (x : {x : T | P x}) (y : {x : T | P x}),
proj1_sig x = proj1_sig y -> x = y.
Proof.
intros A P x y.
case x.
intros xv xp.
case y.
intros yv yp .
simpl.
intro H1.
subst xv.
rewrite (proof_irrelevance (P yv) yp xp).
reflexivity.
Qed.

Record EquivalenceRelation : Type := mkEquivalenceRelation
{
T   : Type;
Rela : T -> T -> Prop;
Refl : forall (a : T), (Rela a a);
Symm : forall (a b : T), (Rela a b) -> (Rela b a);
Tran : forall (a b c : T), (Rela a b) -> (Rela b c) -> (Rela a c)
}.

Definition EquivalenceClass := 
fun (ER : EquivalenceRelation) (a : T ER) => (fun b : T ER => (Rela ER a b)).

Definition EquivalenceClassSet (ER : EquivalenceRelation) := {s : Ensemble (T ER) | exists (a : T ER), (EquivalenceClass ER a) = s}. 

Lemma ToEquivalenceClassSub : forall (ER : EquivalenceRelation) (a : T ER), exists (b : T ER), (EquivalenceClass ER b) = (EquivalenceClass ER a).
Proof.
intros ER a.
exists a.
reflexivity.
Qed.

Definition ToEquivalenceClass (ER : EquivalenceRelation) := fun (a : T ER) => (exist (fun (s : Ensemble (T ER)) => exists (a : T ER), (EquivalenceClass ER a) = s) (EquivalenceClass ER a) (ToEquivalenceClassSub ER a)).

Lemma EquivalenceSame : forall (ER : EquivalenceRelation) (a b : T ER), (Rela ER a b) <-> (EquivalenceClass ER a) = (EquivalenceClass ER b).
Proof.
intros ER a b.
apply conj.
intros H1.
apply (Extensionality_Ensembles (T ER) (EquivalenceClass ER a) (EquivalenceClass ER b)).
apply conj.
intros x H2.
apply (Tran ER b a x).
apply (Symm ER a b H1).
apply H2.
intros x H2.
apply (Tran ER a b x).
apply H1.
apply H2.
intro H1.
cut (In (T ER) (EquivalenceClass ER a) b).
intro H2.
apply H2.
rewrite H1.
apply (Refl ER b).
Qed.

Lemma EquivalenceWellDefined : forall (ER : EquivalenceRelation) (S : Type) (f : (T ER) -> S),
(forall (a b : T ER), (Rela ER a b) -> (f a) = (f b)) -> (exists! (F : (EquivalenceClassSet ER) -> S), forall (A : (EquivalenceClassSet ER)) (a : (T ER)), (In (T ER) (proj1_sig A) a) -> (F A) = (f a)).
Proof.
intros ER S f H1.
apply (proj1 (unique_existence (fun F : EquivalenceClassSet ER -> S => forall (A : EquivalenceClassSet ER) (a : T ER), In (T ER) (proj1_sig A) a -> F A = f a))).
apply conj.
cut (forall A : (EquivalenceClassSet ER), exists! s : S, forall a : (T ER), In (T ER) (proj1_sig A) a -> s = (f a)).
intro H2.
exists (fun A : EquivalenceClassSet ER => proj1_sig (constructive_definite_description (fun s : S => forall a : T ER, In (T ER) (proj1_sig A) a -> s = f a) (H2 A))).
intros A a H3.
apply (proj2_sig (constructive_definite_description (fun s : S => forall a0 : T ER, In (T ER) (proj1_sig A) a0 -> s = f a0) (H2 A)) a H3).
intro A.
apply (proj1 (unique_existence (fun s : S => forall a : T ER, In (T ER) (proj1_sig A) a -> s = f a))).
apply conj.
elim (proj2_sig A).
intros a H2.
exists (f a).
rewrite<- H2.
intros b H3.
apply (H1 a b H3).
intros s1 s2 H2 H3.
elim (proj2_sig A).
intros a H4.
rewrite (H2 a).
rewrite (H3 a).
reflexivity.
rewrite<- H4.
apply (Refl ER a).
rewrite<- H4.
apply (Refl ER a).
intros F1 F2 H2 H3.
apply (functional_extensionality F1 F2).
intro A.
elim (proj2_sig A).
intros a H4.
rewrite (H2 A a).
rewrite (H3 A a).
reflexivity.
rewrite<- H4.
apply (Refl ER a).
rewrite<- H4.
apply (Refl ER a).
Qed.

Definition ToEquivalenceFunction (ER : EquivalenceRelation) (S : Type) := fun f : {g : (T ER) -> S | forall (a b : T ER), (Rela ER a b) -> (g a) = (g b)} => proj1_sig (constructive_definite_description (fun F : (EquivalenceClassSet ER) -> S => forall (A : (EquivalenceClassSet ER)) (a : (T ER)), (In (T ER) (proj1_sig A) a) -> (F A) = ((proj1_sig f) a)) (EquivalenceWellDefined ER S (proj1_sig f) (proj2_sig f))).

Lemma ToEquivalenceFunctionNature : forall (ER : EquivalenceRelation) (S : Type) (f : {g : (T ER) -> S | forall (a b : T ER), (Rela ER a b) -> (g a) = (g b)}), forall (A : (EquivalenceClassSet ER)) (a : (T ER)), (In (T ER) (proj1_sig A) a) -> (ToEquivalenceFunction ER S f A) = ((proj1_sig f) a).
Proof.
intros ER S f.
apply (proj2_sig (constructive_definite_description (fun F : (EquivalenceClassSet ER) -> S => forall (A : (EquivalenceClassSet ER)) (a : (T ER)), (In (T ER) (proj1_sig A) a) -> (F A) = ((proj1_sig f) a)) (EquivalenceWellDefined ER S (proj1_sig f) (proj2_sig f)))).
Qed.

Lemma EquivalenceWellDefinedBinary : forall (ER1 ER2 : EquivalenceRelation) (S : Type) (f : (T ER1) -> (T ER2) -> S),
(forall (a1 b1 : T ER1) (a2 b2 : T ER2), (Rela ER1 a1 b1) -> (Rela ER2 a2 b2) -> (f a1 a2) = (f b1 b2)) -> (exists! (F : (EquivalenceClassSet ER1) -> (EquivalenceClassSet ER2) -> S), forall (A1 : (EquivalenceClassSet ER1)) (A2 : (EquivalenceClassSet ER2)) (a1 : (T ER1)) (a2 : (T ER2)), (In (T ER1) (proj1_sig A1) a1) -> (In (T ER2) (proj1_sig A2) a2) -> (F A1 A2) = (f a1 a2)).
Proof.
intros ER1 ER2 S f H1.
apply (proj1 (unique_existence (fun F : EquivalenceClassSet ER1 -> EquivalenceClassSet ER2 -> S => forall (A1 : EquivalenceClassSet ER1) (A2 : EquivalenceClassSet ER2) (a1 : T ER1) (a2 : T ER2), In (T ER1) (proj1_sig A1) a1 -> In (T ER2) (proj1_sig A2) a2 -> F A1 A2 = f a1 a2))).
apply conj.
cut (forall (a : T ER1) (a1 b1 : T ER2), Rela ER2 a1 b1 -> f a a1 = f a b1).
intro H2.
cut (let Fsub := fun a : (T ER1) => (ToEquivalenceFunction ER2 S (exist (fun g : (T ER2) -> S => forall (a b : T ER2), (Rela ER2 a b) -> (g a) = (g b)) (f a) (H2 a))) in
(forall (a : T ER1) (a1 b1 : T ER2), Rela ER2 a1 b1 -> f a a1 = f a b1) ->
exists x : EquivalenceClassSet ER1 -> EquivalenceClassSet ER2 -> S,
  forall (A1 : EquivalenceClassSet ER1) (A2 : EquivalenceClassSet ER2) (a1 : T ER1) (a2 : T ER2),
  In (T ER1) (proj1_sig A1) a1 -> In (T ER2) (proj1_sig A2) a2 -> x A1 A2 = f a1 a2).
intro H3.
apply H3.
apply H2.
intro Fsub.
intro H3.
cut (forall a b : (T ER1), (Rela ER1 a b) -> (Fsub a) = (Fsub b)).
intro H4.
exists (ToEquivalenceFunction ER1 (EquivalenceClassSet ER2 -> S) (exist (fun g : (T ER1) -> (EquivalenceClassSet ER2) -> S => forall (a b : T ER1), (Rela ER1 a b) -> (g a) = (g b)) Fsub H4)).
intros A1 A2 a1 a2 H5 H6.
rewrite (ToEquivalenceFunctionNature ER1 (EquivalenceClassSet ER2 -> S) (exist (fun g : T ER1 -> EquivalenceClassSet ER2 -> S => forall a b : T ER1, Rela ER1 a b -> g a = g b) Fsub H4) A1 a1).
unfold proj1_sig.
unfold Fsub.
rewrite (ToEquivalenceFunctionNature ER2 S (exist (fun g : T ER2 -> S => forall a0 b : T ER2, Rela ER2 a0 b -> g a0 = g b) (f a1) (H2 a1)) A2 a2).
unfold proj1_sig.
reflexivity.
apply H6.
apply H5.
intros a1 a2 H4.
apply (functional_extensionality (Fsub a1) (Fsub a2)).
intro B1.
elim (proj2_sig B1).
intros b H5.
unfold Fsub.
rewrite (ToEquivalenceFunctionNature ER2 S (exist (fun g : T ER2 -> S => forall a0 b : T ER2, Rela ER2 a0 b -> g a0 = g b) (f a1) (H2 a1)) B1 b).
rewrite (ToEquivalenceFunctionNature ER2 S (exist (fun g : T ER2 -> S => forall a0 b : T ER2, Rela ER2 a0 b -> g a0 = g b) (f a2) (H2 a2)) B1 b).
unfold proj1_sig.
apply (H1 a1 a2 b b).
apply H4.
apply (Refl ER2 b).
rewrite<- H5.
apply (Refl ER2 b).
rewrite<- H5.
apply (Refl ER2 b).
intros a a1 b1 H4.
apply (H1 a a a1 b1).
apply (Refl ER1 a).
apply H4.
intros F1 F2 H2 H3.
apply (functional_extensionality F1 F2).
intro A1.
apply (functional_extensionality (F1 A1) (F2 A1)).
intro A2.
elim (proj2_sig A1).
elim (proj2_sig A2).
intros a2 H4 a1 H5.
rewrite (H2 A1 A2 a1 a2).
rewrite (H3 A1 A2 a1 a2).
reflexivity.
rewrite<- H5.
apply (Refl ER1 a1).
rewrite<- H4.
apply (Refl ER2 a2).
rewrite<- H5.
apply (Refl ER1 a1).
rewrite<- H4.
apply (Refl ER2 a2).
Qed.

Definition ToEquivalenceFunctionBinary (ER1 ER2 : EquivalenceRelation) (S : Type) := fun f : {g : (T ER1) -> (T ER2) -> S | forall (a1 b1 : T ER1) (a2 b2 : T ER2), (Rela ER1 a1 b1) -> (Rela ER2 a2 b2) -> (g a1 a2) = (g b1 b2)} => proj1_sig (constructive_definite_description (fun F : (EquivalenceClassSet ER1) -> (EquivalenceClassSet ER2) -> S => forall (A1 : (EquivalenceClassSet ER1)) (A2 : (EquivalenceClassSet ER2)) (a1 : (T ER1)) (a2 : (T ER2)), (In (T ER1) (proj1_sig A1) a1) -> (In (T ER2) (proj1_sig A2) a2) -> (F A1 A2) = ((proj1_sig f) a1 a2)) (EquivalenceWellDefinedBinary ER1 ER2 S (proj1_sig f) (proj2_sig f))).

Lemma ToEquivalenceFunctionBinaryNature : forall (ER1 ER2 : EquivalenceRelation) (S : Type) (f : {g : (T ER1) -> (T ER2) -> S | forall (a1 b1 : T ER1) (a2 b2 : T ER2), (Rela ER1 a1 b1) -> (Rela ER2 a2 b2) -> (g a1 a2) = (g b1 b2)}), forall (A1 : (EquivalenceClassSet ER1)) (a1 : (T ER1)) (A2 : (EquivalenceClassSet ER2)) (a2 : (T ER2)), (In (T ER1) (proj1_sig A1) a1) -> (In (T ER2) (proj1_sig A2) a2) -> (ToEquivalenceFunctionBinary ER1 ER2 S f A1 A2) = ((proj1_sig f) a1 a2).
Proof.
intros ER1 ER2 S f A1 a1 A2 a2 H1 H2.
apply (proj2_sig (constructive_definite_description (fun F : (EquivalenceClassSet ER1) -> (EquivalenceClassSet ER2) -> S => forall (A1 : (EquivalenceClassSet ER1)) (A2 : (EquivalenceClassSet ER2)) (a1 : (T ER1)) (a2 : (T ER2)), (In (T ER1) (proj1_sig A1) a1) -> (In (T ER2) (proj1_sig A2) a2) -> (F A1 A2) = ((proj1_sig f) a1 a2)) (EquivalenceWellDefinedBinary ER1 ER2 S (proj1_sig f) (proj2_sig f)))).
apply H1.
apply H2.
Qed.

Definition SequenceQ := (nat -> Q).

Definition Cv_Q := fun (a : SequenceQ) (q : Q) => forall (eps : Q), eps > 0 -> exists (N : nat), forall (n : nat), (n >= N)%nat -> (Qabs (q - (a n)) < eps).

Definition SequenceQPlus := fun (a b : SequenceQ) => (fun n : nat => (a n) + (b n)).

Definition SequenceQOpp := fun (a : SequenceQ) => (fun n : nat => - (a n)).

Definition SequenceQMul := fun (a b : SequenceQ) => (fun n : nat => (a n) * (b n)).

Lemma SequenceQInvAltUnique : forall (a : SequenceQ), exists! (ainv : SequenceQ),
((Cv_Q a 0) -> (forall n : nat, ainv n = 0)) /\ (~(Cv_Q a 0) -> (forall n : nat, ainv n = / (a n))).
Proof.
intro a.
apply (proj1 (unique_existence (fun b : SequenceQ => (Cv_Q a 0 -> forall n : nat, b n = 0) /\ (~ Cv_Q a 0 -> forall n : nat, b n = / a n)))).
apply conj.
elim (classic (Cv_Q a 0)).
intro H1.
exists (fun n : nat => 0).
apply conj.
auto.
intro H2.
apply False_ind.
apply (H2 H1).
intro H1.
exists (fun n : nat => / a n).
apply conj.
intro H2.
apply False_ind.
apply (H1 H2).
intro H2.
auto.
intros a1 a2 H1 H2.
apply (functional_extensionality a1 a2).
elim (classic (Cv_Q a 0)).
intro H3.
intro n.
rewrite (proj1 H1 H3 n).
rewrite (proj1 H2 H3 n).
reflexivity.
intro H3.
intro n.
rewrite (proj2 H1 H3 n).
rewrite (proj2 H2 H3 n).
reflexivity.
Qed.

Definition SequenceQInvAlt := fun (a : SequenceQ) => proj1_sig (constructive_definite_description (fun (ainv : SequenceQ) =>
((Cv_Q a 0) -> (forall n : nat, ainv n = 0)) /\ (~(Cv_Q a 0) -> (forall n : nat, ainv n = / (a n)))) (SequenceQInvAltUnique a)).

Lemma SequenceQInvAltNature : forall (a : SequenceQ), ((Cv_Q a 0) -> (forall n : nat, (SequenceQInvAlt a n) = 0)) /\ (~(Cv_Q a 0) -> (forall n : nat, (SequenceQInvAlt a) n = / (a n))).
Proof.
intro a.
apply (proj2_sig (constructive_definite_description (fun (ainv : SequenceQ) =>
((Cv_Q a 0) -> (forall n : nat, ainv n = 0)) /\ (~(Cv_Q a 0) -> (forall n : nat, ainv n = / (a n)))) (SequenceQInvAltUnique a))).
Qed.

Definition Cauchy_Q := fun (a : SequenceQ) => forall (eps : Q), eps > 0 -> exists (N : nat), forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> (Qabs ((a n) - (a m)) < eps).

Lemma double_Q : forall q : Q, (q / inject_Z 2) + (q / inject_Z 2) == q.
Proof.
intro q.
unfold Qeq.
unfold inject_Z.
unfold Qplus.
simpl.
rewrite (Z.mul_1_r (Qnum q)).
rewrite<- (Z.mul_add_distr_l (Qnum q) (' (Qden q * 2)) (' (Qden q * 2))).
rewrite<- (Z.mul_assoc (Qnum q) (' (Qden q * 2) + ' (Qden q * 2)) (' Qden q)).
rewrite<- (Z.mul_1_r (' (Qden q * 2))).
rewrite<- (Z.mul_add_distr_l (' (Qden q * 2)) 1 1).
rewrite<- (Z.mul_assoc (' (Qden q * 2)) (1 + 1) (' Qden q)).
rewrite (Z.mul_comm (1 + 1) (' Qden q)).
auto.
Qed.

Lemma Cauchy_Q_Plus : (forall a b : SequenceQ, (Cauchy_Q a) -> (Cauchy_Q b) -> (Cauchy_Q (SequenceQPlus a b))).
Proof.
intros a b H1 H2.
intros eps H3.
elim (H1 (eps / (inject_Z 2))).
intros n1 H4.
elim (H2 (eps / (inject_Z 2))).
intros n2 H5.
exists (max n1 n2).
intros n m H6 H7.
cut ((SequenceQPlus a b n - SequenceQPlus a b m) == ((a n) - (a m)) + ((b n) - (b m))).
intro H8.
rewrite H8.
apply (Qle_lt_trans (Qabs (a n - a m + (b n - b m))) (Qabs (a n - a m) + Qabs (b n - b m)) eps).
apply (Qabs_triangle (a n - a m) (b n - b m)).
apply (Qlt_trans (Qabs (a n - a m) + Qabs (b n - b m)) (Qabs (a n - a m) + (eps / inject_Z 2)) eps).
apply (Qplus_lt_r (Qabs (b n - b m)) (eps / inject_Z 2) (Qabs (a n - a m))).
apply (H5 n m).
apply (le_trans n2 (max n1 n2) n).
apply (Nat.le_max_r n1 n2).
apply H6.
apply (le_trans n2 (max n1 n2) m).
apply (Nat.le_max_r n1 n2).
apply H7.
apply (Qlt_le_trans (Qabs (a n - a m) + eps / inject_Z 2) (eps / inject_Z 2 + eps / inject_Z 2) eps).
apply (Qplus_lt_l (Qabs (a n - a m)) (eps / inject_Z 2) (eps / inject_Z 2)).
apply (H4 n m).
apply (le_trans n1 (max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H6.
apply (le_trans n1 (max n1 n2) m).
apply (Nat.le_max_l n1 n2).
apply H7.
rewrite (double_Q eps).
apply (Qle_refl eps).
rewrite<- (Qplus_assoc (a n) (b n) (- SequenceQPlus a b m)).
rewrite (Qopp_plus (a m) (b m)).
rewrite (Qplus_assoc (b n) (- a m) (- b m)).
rewrite (Qplus_comm (b n) (- a m)).
rewrite<- (Qplus_assoc (- a m) (b n) (- b m)).
apply (Qplus_assoc (a n) (- a m) (b n + - b m)).
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = (inject_Z 0)).
intro H5.
rewrite H5.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H3.
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = (inject_Z 0)).
intro H5.
rewrite H5.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H3.
Qed.

Lemma Cauchy_Q_Opp : (forall a : SequenceQ, (Cauchy_Q a) -> (Cauchy_Q (SequenceQOpp a))).
Proof.
intros a H1.
intros eps H2.
elim (H1 eps H2).
intros N H3.
exists N.
intros n m H4 H5.
rewrite (Qabs_wd (SequenceQOpp a n - SequenceQOpp a m) (a m - a n)).
apply (H3 m n H5 H4).
unfold SequenceQOpp.
unfold Qminus.
rewrite (Qopp_involutive (a m)).
apply (Qplus_comm (- a n) (a m)).
Qed.

Lemma Cauchy_Q_Bounded : (forall a : SequenceQ, (Cauchy_Q a) -> exists M : Q, forall n : nat, (Qabs (a n)) <= M).
Proof.
cut (forall a : SequenceQ, forall N : nat, (exists M : Q, forall n : nat, (n >= N)%nat -> Qabs (a n) <= M) -> exists M : Q, forall n : nat, Qabs (a n) <= M).
intros H1 a H2.
elim (H2 (inject_Z 1)).
intros N H3.
apply (H1 a N).
exists (Qabs (a N) + (inject_Z 1)).
intros n H4.
rewrite<- (Qplus_0_l (Qabs (a n))).
rewrite<- (Qplus_opp_r (Qabs (a N))).
rewrite<- (Qplus_assoc (Qabs (a N)) (- Qabs (a N)) (Qabs (a n))).
apply (Qplus_le_r (- Qabs (a N) + Qabs (a n)) (inject_Z 1) (Qabs (a N))).
rewrite (Qplus_comm (- Qabs (a N)) (Qabs (a n))).
apply (Qle_trans (Qabs (a n) + - Qabs (a N)) (Qabs (a n - a N)) (inject_Z 1)).
apply (Qabs_triangle_reverse (a n) (a N)).
apply (Qlt_le_weak (Qabs (a n - a N)) (inject_Z 1)).
apply (H3 n N).
apply H4.
apply (le_n N).
cut (0 = (inject_Z 0)).
intro H3.
rewrite H3.
apply (inj_lt 0 1).
apply (le_n 1).
auto.
intros a N.
elim N.
intro H1.
elim H1.
intros q H2.
exists q.
intro n.
apply (H2 n).
apply (le_0_n n).
intros n H1 H2.
apply H1.
elim H2.
intros q H3.
exists (q + (Qabs (a n))).
intros n0 H4.
elim (le_or_lt (S n) n0).
intros H5.
apply (Qle_trans (Qabs (a n0)) q (q + Qabs (a n))).
apply (H3 n0 H5).
rewrite<- (Qplus_0_r q) at 1.
apply (Qplus_le_r 0 (Qabs (a n)) q).
apply (Qabs_nonneg (a n)).
intro H5.
rewrite<- (Qplus_0_l (Qabs (a n0))) at 1.
cut (n = n0).
intro H6.
rewrite H6.
apply (Qplus_le_l 0 q (Qabs (a n0))).
apply (Qle_trans 0 (Qabs (a (S n))) q).
apply (Qabs_nonneg (a (S n))).
apply (H3 (S n)).
apply (le_n (S n)).
apply (le_antisym n n0).
apply H4.
apply (le_S_n n0 n H5).
Qed.

Lemma Cauchy_Q_Mult : (forall a b : SequenceQ, (Cauchy_Q a) -> (Cauchy_Q b) -> (Cauchy_Q (SequenceQMul a b))).
Proof.
intros a b H1 H2.
intros eps H3.
elim (Cauchy_Q_Bounded a H1).
intros M1 H4.
elim (Cauchy_Q_Bounded b H2).
intros M2 H5.
elim (H1 (eps / ((M2 + 1) * inject_Z 2))).
intros N1 H6.
elim (H2 (eps / ((M1 + 1) * inject_Z 2))).
intros N2 H7.
exists (max N1 N2).
intros n1 n2 H8 H9.
apply (Qle_lt_trans (Qabs (SequenceQMul a b n1 - SequenceQMul a b n2)) ((Qabs ((a n1) * (b n1 - b n2))) + (Qabs ((a n1 - a n2) * b n2))) eps).
unfold SequenceQMul.
rewrite (Qabs_wd (a n1 * b n1 - a n2 * b n2) ((a n1 * (b n1 - b n2)) + ((a n1 - a n2) * b n2))).
apply (Qabs_triangle (a n1 * (b n1 - b n2)) ((a n1 - a n2) * b n2)).
rewrite (Qmult_plus_distr_r (a n1) (b n1) (- b n2)).
rewrite (Qmult_plus_distr_l (a n1) (- a n2) (b n2)).
rewrite<- (Qplus_assoc (a n1 * b n1) (a n1 * - b n2) (a n1 * b n2 + - a n2 * b n2)).
rewrite (Qplus_assoc (a n1 * - b n2) (a n1 * b n2) (- a n2 * b n2)).
rewrite<- (Qmult_plus_distr_r (a n1) (- b n2) (b n2)).
rewrite (Qplus_comm (- b n2) (b n2)).
rewrite (Qplus_opp_r (b n2)).
rewrite (Qmult_0_r (a n1)).
rewrite (Qplus_0_l (- a n2 * b n2)).
cut ((- (a n2 * b n2)) == (- a n2 * b n2)).
intro H10. 
unfold Qminus.
rewrite H10.
reflexivity.
apply (Qplus_inj_l (- (a n2 * b n2)) (- a n2 * b n2) (a n2 * b n2)).
rewrite (Qplus_opp_r (a n2 * b n2)).
rewrite<- (Qmult_plus_distr_l (a n2) (- a n2) (b n2)).
rewrite (Qplus_opp_r (a n2)).
rewrite (Qmult_0_l (b n2)).
reflexivity.
cut (M1 + 1 > 0).
intro H10.
cut (M2 + 1 > 0).
intro H11.
rewrite<- (double_Q eps).
apply (Qlt_trans (Qabs (a n1 * (b n1 - b n2)) + Qabs ((a n1 - a n2) * b n2)) (Qabs (a n1 * (b n1 - b n2)) + eps / inject_Z 2) (eps / inject_Z 2 + eps / inject_Z 2)).
apply (Qplus_lt_r (Qabs ((a n1 - a n2) * b n2)) (eps / inject_Z 2) (Qabs (a n1 * (b n1 - b n2)))).
rewrite (Qabs_Qmult (a n1 - a n2) (b n2)).
apply (Qle_lt_trans (Qabs (a n1 - a n2) * Qabs (b n2)) (Qabs (a n1 - a n2) * (M2 + 1)) (eps / inject_Z 2)).
rewrite (Qmult_comm (Qabs (a n1 - a n2)) (Qabs (b n2))).
rewrite (Qmult_comm (Qabs (a n1 - a n2)) (M2 + 1)).
apply (Qmult_le_compat_r (Qabs (b n2)) (M2 + 1) (Qabs (a n1 - a n2))).
apply (Qle_trans (Qabs (b n2)) M2 (M2 + 1)).
apply (H5 n2).
rewrite<- (Qplus_0_r M2) at 1.
apply (Qplus_le_r 0 1 M2).
cut (0 = (inject_Z 0)).
intro H12.
rewrite H12.
cut (1 = (inject_Z 1)).
intro H13.
rewrite H13.
rewrite<- (Zle_Qle 0 1).
apply (inj_le 0 1).
apply (le_S 0).
apply (le_n 0).
auto.
auto.
apply (Qabs_nonneg (a n1 - a n2)).
apply (Qmult_lt_r (Qabs (a n1 - a n2) * (M2 + 1)) (eps / inject_Z 2) (/ (M2 + 1))).
apply (Qinv_lt_0_compat (M2 + 1)).
apply (Qle_lt_trans 0 M2 (M2 + 1)).
apply (Qle_trans 0 (Qabs (b O)) M2).
apply (Qabs_nonneg (b O)).
apply (H5 O).
rewrite<- (Qplus_0_r M2) at 1.
apply (Qplus_lt_r 0 1 M2).
cut (0 = (inject_Z 0)).
intro H12.
rewrite H12.
cut (1 = (inject_Z 1)).
intro H13.
rewrite H13.
rewrite<- (Zlt_Qlt 0 1).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
rewrite<- (Qmult_assoc (Qabs (a n1 - a n2)) (M2 + 1) (/ (M2 + 1))).
rewrite (Qmult_inv_r (M2 + 1)).
rewrite (Qmult_1_r (Qabs (a n1 - a n2))).
rewrite<- (Qmult_assoc eps (/ inject_Z 2) (/ (M2 + 1))).
rewrite<- (Qinv_mult_distr (inject_Z 2) (M2 + 1)).
rewrite (Qmult_comm (inject_Z 2) (M2 + 1)).
apply (H6 n1 n2).
apply (le_trans N1 (max N1 N2) n1).
apply (Nat.le_max_l N1 N2).
apply H8.
apply (le_trans N1 (max N1 N2) n2).
apply (Nat.le_max_l N1 N2).
apply H9.
intro H12.
apply (Qlt_irrefl (M2 + 1)).
rewrite H12 at 1.
apply H11.
apply (Qplus_lt_l (Qabs (a n1 * (b n1 - b n2))) (eps / inject_Z 2) (eps / inject_Z 2)).
rewrite (Qabs_Qmult (a n1) (b n1 - b n2)).
apply (Qle_lt_trans (Qabs (a n1) * Qabs (b n1 - b n2)) ((M1 + 1) * Qabs (b n1 - b n2)) (eps / inject_Z 2)).
apply (Qmult_le_compat_r (Qabs (a n1)) (M1 + 1) (Qabs (b n1 - b n2))).
apply (Qle_trans (Qabs (a n1)) M1 (M1 + 1)).
apply (H4 n1).
rewrite<- (Qplus_0_r M1) at 1.
apply (Qplus_le_r 0 1 M1).
cut (0 = (inject_Z 0)).
intro H12.
rewrite H12.
cut (1 = (inject_Z 1)).
intro H13.
rewrite H13.
rewrite<- (Zle_Qle 0 1).
apply (inj_le 0 1).
apply (le_S 0).
apply (le_n 0).
auto.
auto.
apply (Qabs_nonneg (b n1 - b n2)).
apply (Qmult_lt_l ((M1 + 1) * Qabs (b n1 - b n2)) (eps / inject_Z 2) (/ (M1 + 1))).
apply (Qinv_lt_0_compat (M1 + 1)).
apply H10.
rewrite (Qmult_assoc (/ (M1 + 1)) (M1 + 1) (Qabs (b n1 - b n2))).
rewrite (Qmult_comm (/ (M1 + 1)) (M1 + 1)).
rewrite (Qmult_inv_r (M1 + 1)).
rewrite (Qmult_1_l (Qabs (b n1 - b n2))).
rewrite (Qmult_assoc (/ (M1 + 1)) eps (/ inject_Z 2)).
rewrite (Qmult_comm (/ (M1 + 1)) eps).
rewrite<- (Qmult_assoc eps (/ (M1 + 1)) (/ inject_Z 2)).
rewrite<- (Qinv_mult_distr (M1 + 1) (inject_Z 2)).
apply (H7 n1 n2).
apply (le_trans N2 (max N1 N2) n1).
apply (Nat.le_max_r N1 N2).
apply H8.
apply (le_trans N2 (max N1 N2) n2).
apply (Nat.le_max_r N1 N2).
apply H9.
intro H12.
apply (Qlt_irrefl (M1 + 1)).
rewrite H12 at 1.
apply H10.
apply (Qle_lt_trans 0 M2 (M2 + 1)).
apply (Qle_trans 0 (Qabs (b O)) M2).
apply (Qabs_nonneg (b O)).
apply (H5 O).
rewrite<- (Qplus_0_r M2) at 1.
apply (Qplus_lt_r 0 1 M2).
cut (0 = (inject_Z 0)).
intro H11.
rewrite H11.
cut (1 = (inject_Z 1)).
intro H12.
rewrite H12.
rewrite<- (Zlt_Qlt 0 1).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
apply (Qle_lt_trans 0 M1 (M1 + 1)).
apply (Qle_trans 0 (Qabs (a O)) M1).
apply (Qabs_nonneg (a O)).
apply (H4 O).
rewrite<- (Qplus_0_r M1) at 1.
apply (Qplus_lt_r 0 1 M1).
cut (0 = (inject_Z 0)).
intro H10.
rewrite H10.
cut (1 = (inject_Z 1)).
intro H11.
rewrite H11.
rewrite<- (Zlt_Qlt 0 1).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
apply (Qlt_shift_div_l 0 eps ((M1 + 1) * inject_Z 2)).
rewrite<- (Qmult_0_l (inject_Z 2)).
apply (Qmult_lt_compat_r 0 (M1 + 1) (inject_Z 2)).
cut (0 = (inject_Z 0)).
intro H7.
rewrite H7.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
apply (Qle_lt_trans 0 M1 (M1 + 1)).
apply (Qle_trans 0 (Qabs (a O)) M1).
apply (Qabs_nonneg (a O)).
apply (H4 O).
rewrite<- (Qplus_0_r M1) at 1.
apply (Qplus_lt_r 0 1 M1).
cut (0 = (inject_Z 0)).
intro H10.
rewrite H10.
cut (1 = (inject_Z 1)).
intro H11.
rewrite H11.
rewrite<- (Zlt_Qlt 0 1).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
rewrite (Qmult_0_l ((M1 + 1) * inject_Z 2)).
apply H3.
apply (Qlt_shift_div_l 0 eps ((M2 + 1) * inject_Z 2)).
rewrite<- (Qmult_0_l (inject_Z 2)).
apply (Qmult_lt_compat_r 0 (M2 + 1) (inject_Z 2)).
cut (0 = (inject_Z 0)).
intro H6.
rewrite H6.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
apply (Qle_lt_trans 0 M2 (M2 + 1)).
apply (Qle_trans 0 (Qabs (b O)) M2).
apply (Qabs_nonneg (b O)).
apply (H5 O).
rewrite<- (Qplus_0_r M2) at 1.
apply (Qplus_lt_r 0 1 M2).
cut (0 = (inject_Z 0)).
intro H6.
rewrite H6.
cut (1 = (inject_Z 1)).
intro H7.
rewrite H7.
rewrite<- (Zlt_Qlt 0 1).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
rewrite (Qmult_0_l ((M2 + 1) * inject_Z 2)).
apply H3.
Qed.

Lemma Cv_0_Q_nature : (forall a : SequenceQ, (Cauchy_Q a) -> (~ Cv_Q a 0) -> (exists M : Q, M > 0 /\ (exists N1 : nat, forall n : nat, (n >= N1)%nat -> (Qabs (a n)) > M))).
Proof.
intros a H1 H2.
cut (exists M : Q, 0 < M /\ (forall N1 : nat, exists n : nat, (n >= N1)%nat /\ (M <= Qabs (a n)))).
intro H3.
elim H3.
intros M H4.
exists (M / inject_Z 2).
apply conj.
apply (Qlt_shift_div_l 0 M (inject_Z 2)).
cut (0 = inject_Z 0).
intro H5.
rewrite H5.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply (proj1 H4).
elim (H1 (M / inject_Z 2)).
intros n1 H5.
elim (proj2 H4 n1).
intros n2 H6.
exists n2.
intros n H7.
apply (Qle_lt_trans (M / inject_Z 2) (Qabs (a n2) - (M / inject_Z 2)) (Qabs (a n))).
apply (Qplus_le_l (M / inject_Z 2) (Qabs (a n2) - M / inject_Z 2) (M / inject_Z 2)).
rewrite (double_Q M).
rewrite<- (Qplus_assoc (Qabs (a n2)) (- (M / inject_Z 2)) (M / inject_Z 2)).
rewrite (Qplus_comm (- (M / inject_Z 2)) (M / inject_Z 2)).
rewrite (Qplus_opp_r (M / inject_Z 2)).
rewrite (Qplus_0_r (Qabs (a n2))).
apply (proj2 H6).
rewrite<- (Qplus_0_r (Qabs (a n))).
rewrite<- (Qplus_opp_r (M / inject_Z 2)).
rewrite (Qplus_assoc (Qabs (a n)) (M / inject_Z 2) (- (M / inject_Z 2))).
apply (Qplus_lt_l (Qabs (a n2)) (Qabs (a n) + M / inject_Z 2) (- (M / inject_Z 2))).
apply (Qle_lt_trans (Qabs (a n2)) (Qabs (a n) + Qabs (a n - a n2)) (Qabs (a n) + M / inject_Z 2)).
rewrite (Qabs_Qminus (a n) (a n2)).
rewrite (Qabs_wd (a n2) (a n + (a n2 - a n))).
apply (Qabs_triangle (a n) (a n2 - a n)).
rewrite (Qplus_comm (a n) (a n2 - a n)).
rewrite<- (Qplus_assoc (a n2) (- a n) (a n)).
rewrite (Qplus_comm (- a n) (a n)).
rewrite (Qplus_opp_r (a n)).
rewrite (Qplus_0_r (a n2)).
reflexivity.
apply (Qplus_lt_r (Qabs (a n - a n2)) (M / inject_Z 2) (Qabs (a n))).
apply (H5 n n2).
apply (le_trans n1 n2 n).
apply (proj1 H6).
apply H7.
apply (proj1 H6).
apply (Qlt_shift_div_l 0 M (inject_Z 2)).
cut (0 = inject_Z 0).
intro H7.
rewrite H7.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply (proj1 H4).
apply (NNPP (exists M : Q,
  0 < M /\ (forall N1 : nat, exists n : nat, (n >= N1)%nat /\ M <= Qabs (a n)))).
intro H3.
apply H2.
intros eps2 H4.
apply (NNPP (exists N : nat, forall n : nat, (n >= N)%nat -> Qabs (0 - a n) < eps2)).
intro H5.
apply H3.
exists eps2.
apply conj.
apply H4.
intros N.
apply (NNPP (exists n : nat, (n >= N)%nat /\ eps2 <= Qabs (a n))).
intro H6.
apply H5.
exists N.
intros n H7.
rewrite (Qabs_Qminus 0 (a n)).
rewrite (Qabs_wd (a n - 0) (a n)).
apply (Qnot_le_lt eps2 (Qabs (a n))).
intro H8.
apply H6.
exists n.
apply conj.
apply H7.
apply H8.
rewrite<- (Qplus_0_r (a n)) at 2.
rewrite<- (Qplus_opp_r 0) at 2.
rewrite (Qplus_assoc (a n) 0 (- 0)).
rewrite (Qplus_0_r (a n)).
reflexivity.
Qed.

Lemma Cauchy_Q_InvAlt : (forall a : SequenceQ, (Cauchy_Q a) -> (Cauchy_Q (SequenceQInvAlt a))).
Proof.
intros a H1.
cut (((Cv_Q a 0) -> (forall n : nat, (SequenceQInvAlt a n) = 0)) /\ (~(Cv_Q a 0) -> (forall n : nat, (SequenceQInvAlt a) n = / (a n)))).
intro H2.
elim (classic (Cv_Q a 0)).
intro H3.
intros eps H4.
exists O.
intros n m H5 H6.
rewrite (proj1 H2 H3 n).
rewrite (proj1 H2 H3 m).
simpl.
apply H4.
intro H3.
intros eps H4.
cut (exists M : Q, M > 0 /\ (exists N1 : nat, forall n : nat, (n >= N1)%nat -> (Qabs (a n)) > M)).
intros H5.
elim H5.
intros M H6.
elim (proj2 H6).
intros N1 H7.
elim (H1 (eps * (M * M))).
intros N2 H8.
exists (max N1 N2).
intros n m H9 H10.
rewrite (proj2 H2 H3 n).
rewrite (proj2 H2 H3 m).
cut (~ a n == 0).
intro H11.
cut (~ a m == 0).
intro H12.
rewrite (Qabs_wd (/ a n - / a m) ((a m - a n) / (a n * a m))).
rewrite (Qabs_Qmult (a m - a n) (/ (a n * a m))).
apply (Qle_lt_trans (Qabs (a m - a n) * Qabs (/ (a n * a m))) (eps * (M * M) * Qabs (/ (a n * a m))) eps).
apply (Qmult_le_compat_r (Qabs (a m - a n)) (eps * (M * M)) (Qabs (/ (a n * a m)))).
apply (Qlt_le_weak (Qabs (a m - a n)) (eps * (M * M))).
apply (H8 m n).
apply (le_trans N2 (max N1 N2) m).
apply (Nat.le_max_r N1 N2).
apply H10.
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H9.
apply (Qabs_nonneg (/ (a n * a m))).
rewrite<- (Qmult_1_r eps) at 2.
rewrite<- (Qmult_assoc eps (M * M) (Qabs (/ (a n * a m)))).
apply (Qmult_lt_l ((M * M) * Qabs (/ (a n * a m))) 1 eps H4).
apply (Qmult_lt_r ((M * M) * Qabs (/ (a n * a m))) 1 (Qabs (a n * a m))).
case (proj1 (Qle_lteq 0 (Qabs (a n * a m))) (Qabs_nonneg (a n * a m))).
auto.
apply (Qabs_case (a n * a m)).
intros H13 H14.
apply False_ind.
apply H12.
apply (Qmult_integral_l (a n) (a m) H11).
rewrite H14.
reflexivity.
intros H13 H14.
apply False_ind.
apply H12.
apply (Qmult_integral_l (a n) (a m) H11).
rewrite<- (Qopp_involutive (a n * a m)).
rewrite<- H14.
auto.
rewrite<- (Qplus_0_l (- 0)).
apply (Qplus_opp_r 0).
rewrite<- (Qmult_assoc (M * M) (Qabs (/ (a n * a m))) (Qabs (a n * a m))).
rewrite (Qmult_comm (Qabs (/ (a n * a m))) (Qabs (a n * a m))).
rewrite<- (Qabs_Qmult (a n * a m) (/ (a n * a m))).
rewrite (Qabs_wd (a n * a m * / (a n * a m)) 1).
unfold Qabs at 1.
unfold Z.abs.
rewrite (Qmult_1_r (M * M)).
rewrite (Qmult_1_l (Qabs (a n * a m))).
rewrite (Qabs_Qmult (a n) (a m)).
apply (Qlt_trans (M * M) (M * Qabs (a m)) (Qabs (a n) * Qabs (a m))).
apply (Qmult_lt_l M (Qabs (a m)) M).
apply (proj1 H6).
apply (H7 m).
apply (le_trans N1 (max N1 N2) m).
apply (Nat.le_max_l N1 N2).
apply H10.
apply (Qmult_lt_r M (Qabs (a n)) (Qabs (a m))).
apply (Qlt_trans 0 M (Qabs (a m))).
apply (proj1 H6).
apply (H7 m).
apply (le_trans N1 (max N1 N2) m).
apply (Nat.le_max_l N1 N2).
apply H10.
apply (H7 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H9.
rewrite (Qmult_inv_r (a n * a m)).
reflexivity.
intro H13.
apply H12.
apply (Qmult_integral_l (a n) (a m) H11 H13).
rewrite<- (Qmult_1_l (/ a n)).
rewrite<- (Qmult_inv_r (a m)).
rewrite<- (Qmult_1_l (/ a m)) at 2.
rewrite<- (Qmult_inv_r (a n)).
rewrite<- (Qmult_assoc (a m) (/ a m) (/ a n)).
unfold Qminus at 1.
cut (- (a n * / a n * / a m) == (- a n) * (/ a n * / a m)).
intro H13.
rewrite H13.
rewrite (Qmult_comm (/ a m) (/ a n)).
rewrite<- (Qmult_plus_distr_l (a m) (- a n) (/ a n * / a m)).
rewrite<- (Qinv_mult_distr (a n) (a m)).
unfold Qminus.
unfold Qdiv.
reflexivity.
apply (Qplus_inj_l (- (a n * / a n * / a m)) (- a n * (/ a n * / a m)) (a n * / a n * / a m)).
rewrite (Qplus_opp_r (a n * / a n * / a m)).
rewrite<- (Qmult_assoc (a n) (/ a n) (/ a m)).
rewrite<- (Qmult_plus_distr_l (a n) (- a n) (/ a n * / a m)).
rewrite (Qplus_opp_r (a n)).
rewrite (Qmult_0_l (/ a n * / a m)).
reflexivity.
apply H11.
apply H12.
intro H12.
apply (Qlt_not_le M 0).
cut (0 == Qabs 0).
intro H13.
rewrite H13.
rewrite (Qabs_wd 0 (a m)).
apply (H7 m).
apply (le_trans N1 (max N1 N2) m).
apply (Nat.le_max_l N1 N2).
apply H10.
rewrite H12.
reflexivity.
simpl.
reflexivity.
apply (Qlt_le_weak 0 M (proj1 H6)).
intro H11.
apply (Qlt_not_le M 0).
cut (0 == Qabs 0).
intro H12.
rewrite H12.
rewrite (Qabs_wd 0 (a n)).
apply (H7 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H9.
rewrite H11.
reflexivity.
simpl.
reflexivity.
apply (Qlt_le_weak 0 M (proj1 H6)).
rewrite<- (Qmult_0_l (M * M)).
apply (Qmult_lt_compat_r 0 eps (M * M)).
rewrite<- (Qmult_0_l M).
apply (Qmult_lt_compat_r 0 M).
apply (proj1 H6).
apply (proj1 H6).
apply H4.
apply (Cv_0_Q_nature a H1 H3).
apply (SequenceQInvAltNature a).
Qed.

Lemma Cv_Q_plus_0_0 : forall (a b : SequenceQ), (Cv_Q a 0) -> (Cv_Q b 0) -> (Cv_Q (SequenceQPlus a b) 0).
Proof.
intros a b H1 H2.
intros eps H3.
elim (H1 (eps / (inject_Z 2))).
intros n1 H4.
elim (H2 (eps / (inject_Z 2))).
intros n2 H5.
exists (max n1 n2).
intros n H6.
cut ((0 - SequenceQPlus a b n) == (0 - (a n)) + (0 - (b n))).
intro H7.
rewrite H7.
apply (Qle_lt_trans (Qabs (0 - a n + (0 - b n))) (Qabs (0 - a n) + Qabs (0 - b n)) eps).
apply (Qabs_triangle (0 - a n) (0 - b n)).
apply (Qlt_trans (Qabs (0 - a n) + Qabs (0 - b n)) (Qabs (0 - a n) + (eps / inject_Z 2)) eps).
apply (Qplus_lt_r (Qabs (0 - b n)) (eps / inject_Z 2) (Qabs (0 - a n))).
apply (H5 n).
apply (le_trans n2 (max n1 n2) n).
apply (Nat.le_max_r n1 n2).
apply H6.
rewrite<- (double_Q eps) at 2.
apply (Qplus_lt_l (Qabs (0 - a n)) (eps / inject_Z 2) (eps / inject_Z 2)).
apply (H4 n).
apply (le_trans n1 (max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H6.
unfold Qminus at 1.
rewrite (Qopp_plus (a n) (b n)).
rewrite (Qplus_assoc 0 (- a n) (- b n)).
rewrite (Qplus_0_l (- b n)).
reflexivity.
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = (inject_Z 0)).
intro H5.
rewrite H5.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H3.
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = (inject_Z 0)).
intro H5.
rewrite H5.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H3.
Qed.

Lemma Cv_Q_mult_0_bounded : forall (a b : SequenceQ), (Cv_Q a 0) -> (exists M : Q, forall n : nat, (Qabs (b n)) <= M) -> (Cv_Q (SequenceQMul a b) 0).
Proof.
intros a b H1 H2.
elim H2.
intros M H3.
elim (Qlt_le_dec 0 M).
intro H4.
intros eps H5.
elim (H1 (eps / M)).
intros n1 H6.
exists n1.
intros n H7.
rewrite (Qabs_wd (0 - SequenceQMul a b n) ((0 - a n) * (b n))).
rewrite (Qabs_Qmult (0 - a n) (b n)).
case (Qle_lt_or_eq 0 (Qabs (b n)) (Qabs_nonneg (b n))).
intro H8.
apply (Qlt_le_trans (Qabs (0 - a n) * Qabs (b n)) (eps / M * (Qabs (b n))) eps).
apply (Qmult_lt_compat_r (Qabs (0 - a n)) (eps / M) (Qabs (b n))).
apply H8.
apply (H6 n H7).
rewrite<- (Qmult_1_r eps) at 2.
rewrite<- (Qmult_inv_r M).
rewrite (Qmult_comm M (/ M)).
rewrite (Qmult_assoc eps (/ M) M).
apply (Qmult_le_l (Qabs (b n)) M (eps * / M)).
apply (Qlt_shift_div_l 0 eps M).
apply H4.
rewrite (Qmult_0_l M).
apply H5.
apply (H3 n).
intro H9.
apply (Qlt_not_eq 0 M H4).
rewrite H9.
reflexivity.
intro H8.
rewrite<- H8.
rewrite (Qmult_0_r (Qabs (0 - a n))).
apply H5.
rewrite<- (Qmult_0_l (b n)) at 1.
rewrite (Qmult_plus_distr_l 0 (- a n) (b n)).
cut (- (a n * b n) == - a n * b n).
intro H8.
rewrite<- H8.
reflexivity.
apply (Qplus_inj_l (- (a n * b n)) (- a n * b n) (a n * b n)).
rewrite (Qplus_opp_r (a n * b n)).
rewrite<- (Qmult_plus_distr_l (a n) (- a n) (b n)).
rewrite (Qplus_opp_r (a n)).
rewrite (Qmult_0_l (b n)).
reflexivity.
apply (Qlt_shift_div_l 0 eps M).
apply H4.
rewrite (Qmult_0_l M).
apply H5.
intros H4 eps H5.
exists O.
intros n H6.
rewrite (Qabs_wd (0 - SequenceQMul a b n) ((0 - a n) * (b n))).
rewrite (Qabs_Qmult (0 - a n) (b n)).
apply (Qle_lt_trans (Qabs (0 - a n) * (Qabs (b n))) 0 eps).
rewrite<- (Qmult_0_r (Qabs (0 -  a n))) at 2.
rewrite (Qmult_comm (Qabs (0 - a n)) (Qabs (b n))).
rewrite (Qmult_comm (Qabs (0 - a n)) 0).
apply (Qmult_le_compat_r (Qabs (b n)) 0 (Qabs (0 - a n))).
apply (Qle_trans (Qabs (b n)) M 0).
apply (H3 n).
apply H4.
apply (Qabs_nonneg (0 - a n)).
apply H5.
rewrite<- (Qmult_0_l (b n)) at 1.
rewrite (Qmult_plus_distr_l 0 (- a n) (b n)).
cut (- (a n * b n) == - a n * b n).
intro H7.
rewrite<- H7.
reflexivity.
apply (Qplus_inj_l (- (a n * b n)) (- a n * b n) (a n * b n)).
rewrite (Qplus_opp_r (a n * b n)).
rewrite<- (Qmult_plus_distr_l (a n) (- a n) (b n)).
rewrite (Qplus_opp_r (a n)).
rewrite (Qmult_0_l (b n)).
reflexivity.
Qed.

Definition CauchySequenceQSet := {a : SequenceQ | Cauchy_Q a}.

Definition CauchySequenceQPlus := fun (a b : CauchySequenceQSet) => (exist Cauchy_Q (SequenceQPlus (proj1_sig a) (proj1_sig b)) (Cauchy_Q_Plus (proj1_sig a) (proj1_sig b) (proj2_sig a) (proj2_sig b))).

Definition CauchySequenceQOpp := fun (a : CauchySequenceQSet) => (exist Cauchy_Q (SequenceQOpp (proj1_sig a)) (Cauchy_Q_Opp (proj1_sig a) (proj2_sig a))).

Definition CauchySequenceQMult := fun (a b : CauchySequenceQSet) => (exist Cauchy_Q (SequenceQMul (proj1_sig a) (proj1_sig b)) (Cauchy_Q_Mult (proj1_sig a) (proj1_sig b) (proj2_sig a) (proj2_sig b))).

Definition CauchySequenceQInv := fun (a : CauchySequenceQSet) => (exist Cauchy_Q (SequenceQInvAlt (proj1_sig a)) (Cauchy_Q_InvAlt (proj1_sig a) (proj2_sig a))).

Definition CauchySequenceQLt := fun (a b : CauchySequenceQSet) => (exists eps : Q, eps > 0 /\ exists N : nat, forall n : nat, (n >= N)%nat -> ((proj1_sig a n) + eps <= (proj1_sig b n))).

Definition CauchySequenceEquivalence := fun (a b : CauchySequenceQSet) => (Cv_Q (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b))) 0).

Lemma CauchySequenceQLeNature : forall (a b : CauchySequenceQSet), (~ CauchySequenceQLt a b) -> forall (eps : Q), eps > 0 -> exists (N : nat), forall (n : nat), (n >= N)%nat -> (proj1_sig b n) < (proj1_sig a n) + eps.
Proof.
intros a b H1 eps H2.
apply NNPP.
intro H3.
apply H1.
exists (eps / (inject_Z 2) / (inject_Z 2)).
apply conj.
apply (Qlt_shift_div_l 0 (eps / (inject_Z 2)) (inject_Z 2)).
cut (0 = inject_Z 0).
intro H4.
rewrite H4.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = inject_Z 0).
intro H4.
rewrite H4.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H2.
cut (forall (N : nat), exists (n : nat), (n >= N)%nat /\ proj1_sig a n + eps <= proj1_sig b n).
intro H4.
elim (proj2_sig a (eps / inject_Z 2 / inject_Z 2)).
intros N1 H5.
elim (proj2_sig b (eps / inject_Z 2)).
intros N2 H6.
elim (H4 (max N1 N2)).
intros N3 H7.
exists N3.
intros n H8.
apply (Qle_trans (proj1_sig a n + eps / inject_Z 2 / inject_Z 2) (proj1_sig a N3 + eps / inject_Z 2) (proj1_sig b n)).
rewrite<- (double_Q (eps / inject_Z 2)) at 2.
rewrite (Qplus_assoc (proj1_sig a N3) (eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2 / inject_Z 2)).
apply (Qplus_le_l (proj1_sig a n) (proj1_sig a N3 + eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_comm (proj1_sig a N3) (eps / inject_Z 2 / inject_Z 2)).
apply (Qplus_le_l (proj1_sig a n) (eps / inject_Z 2 / inject_Z 2 + proj1_sig a N3) (- proj1_sig a N3)).
rewrite<- (Qplus_assoc (eps / inject_Z 2 / inject_Z 2) (proj1_sig a N3) (- proj1_sig a N3)).
rewrite (Qplus_opp_r (proj1_sig a N3)).
rewrite (Qplus_0_r (eps / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (proj1_sig a n + - proj1_sig a N3) (Qabs (proj1_sig a n + - proj1_sig a N3)) (eps / inject_Z 2 / inject_Z 2)).
apply (Qle_Qabs (proj1_sig a n + - proj1_sig a N3)).
apply (Qlt_le_weak (Qabs (proj1_sig a n + - proj1_sig a N3)) (eps / inject_Z 2 / inject_Z 2)).
apply (H5 n N3).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply (le_trans (max N1 N2) N3 n).
apply (proj1 H7).
apply H8.
apply (le_trans N1 (max N1 N2) N3).
apply (Nat.le_max_l N1 N2).
apply (proj1 H7).
apply (Qle_trans (proj1_sig a N3 + eps / inject_Z 2) (proj1_sig b N3 - eps / inject_Z 2) (proj1_sig b n)).
apply (Qplus_le_l (proj1_sig a N3 + eps / inject_Z 2) (proj1_sig b N3 - eps / inject_Z 2) (eps / inject_Z 2)).
rewrite<- (Qplus_assoc (proj1_sig a N3) (eps / inject_Z 2) (eps / inject_Z 2)).
rewrite<- (Qplus_assoc (proj1_sig b N3) (- (eps / inject_Z 2)) (eps / inject_Z 2)).
rewrite (Qplus_comm (- (eps / inject_Z 2)) (eps / inject_Z 2)).
rewrite (Qplus_opp_r (eps / inject_Z 2)).
rewrite (Qplus_0_r (proj1_sig b N3)).
rewrite (double_Q eps).
apply (proj2 H7).
apply (Qplus_le_l (proj1_sig b N3 - eps / inject_Z 2) (proj1_sig b n) (eps / inject_Z 2)).
rewrite<- (Qplus_assoc (proj1_sig b N3) (- (eps / inject_Z 2)) (eps / inject_Z 2)).
rewrite (Qplus_comm (- (eps / inject_Z 2)) (eps / inject_Z 2)).
rewrite (Qplus_opp_r (eps / inject_Z 2)).
rewrite (Qplus_0_r (proj1_sig b N3)).
rewrite (Qplus_comm (proj1_sig b n) (eps / inject_Z 2)).
apply (Qplus_le_l (proj1_sig b N3) (eps / inject_Z 2 + proj1_sig b n) (- proj1_sig b n)).
rewrite<- (Qplus_assoc (eps / inject_Z 2) (proj1_sig b n) (- proj1_sig b n)).
apply (Qle_trans (proj1_sig b N3 + - proj1_sig b n) (Qabs (proj1_sig b N3 + - proj1_sig b n)) (eps / inject_Z 2 + (proj1_sig b n + - proj1_sig b n))).
apply (Qle_Qabs (proj1_sig b N3 + - proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig b n)).
rewrite (Qplus_0_r (eps / inject_Z 2)).
apply (Qlt_le_weak (Qabs (proj1_sig b N3 + - proj1_sig b n)) (eps / inject_Z 2)).
apply (H6 N3 n).
apply (le_trans N2 (max N1 N2) N3).
apply (Nat.le_max_r N1 N2).
apply (proj1 H7).
apply (le_trans N2 N3 n).
apply (le_trans N2 (max N1 N2) N3).
apply (Nat.le_max_r N1 N2).
apply (proj1 H7).
apply H8.
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = inject_Z 0).
intro H6.
rewrite H6.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H2.
apply (Qlt_shift_div_l 0 (eps / (inject_Z 2)) (inject_Z 2)).
cut (0 = inject_Z 0).
intro H6.
rewrite H6.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
cut (0 = inject_Z 0).
intro H6.
rewrite H6.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
rewrite (Qmult_0_l (inject_Z 2)).
apply H2.
intro N.
apply NNPP.
intro H4.
apply H3.
exists N.
intros n H5.
apply (Qnot_le_lt (proj1_sig a n + eps) (proj1_sig b n)).
intro H6.
apply H4.
exists n.
apply conj.
apply H5.
apply H6.
Qed.

Lemma CauchySequenceEquivalenceRefl : forall (a : CauchySequenceQSet), (CauchySequenceEquivalence a a).
Proof.
intro a.
intros eps H1.
exists O.
intros n H2.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig a)) n) 0).
simpl.
apply H1.
rewrite (Qplus_opp_r (proj1_sig a n)).
apply (Qplus_opp_r 0).
Qed.

Lemma CauchySequenceEquivalenceSymm : forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (CauchySequenceEquivalence b a).
Proof.
intros a b H1.
intros eps H2.
elim (H1 eps H2).
intros N H3.
exists N.
intros n H4.
rewrite (Qabs_Qminus 0 (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig a)) n)).
rewrite (Qabs_wd (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig a)) n - 0) (0 - SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n)).
apply (H3 n H4).
rewrite (Qplus_0_l (- 0)) at 1.
unfold Qminus at 1.
rewrite (Qopp_involutive 0).
rewrite (Qplus_0_r (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig a)) n)).
rewrite (Qplus_0_l (- SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n)).
rewrite (Qplus_comm (proj1_sig b n) (- proj1_sig a n)).
apply (Qplus_inj_l (- proj1_sig a n + proj1_sig b n) (- SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n) (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n)).
rewrite (Qplus_opp_r (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n)).
rewrite (Qplus_assoc (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n) (- proj1_sig a n) (proj1_sig b n)).
rewrite (Qplus_comm (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n) (- proj1_sig a n)).
rewrite (Qplus_assoc (- proj1_sig a n) (proj1_sig a n) (SequenceQOpp (proj1_sig b) n)).
rewrite (Qplus_comm (- proj1_sig a n) (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
rewrite (Qplus_0_l (SequenceQOpp (proj1_sig b) n)).
rewrite (Qplus_comm (- proj1_sig b n) (proj1_sig b n)).
apply (Qplus_opp_r (proj1_sig b n)).
Qed.

Lemma CauchySequenceEquivalenceTran : forall (a b c : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (CauchySequenceEquivalence b c) -> (CauchySequenceEquivalence a c).
Proof.
intros a b c H1 H2.
unfold CauchySequenceEquivalence.
cut (Cv_Q (SequenceQPlus (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b))) (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig c)))) 0).
intros H3.
intros eps H4.
elim (H3 eps H4).
intros N H5.
exists N.
intros n H6.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig c)) n) (0 - SequenceQPlus (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b))) (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig c))) n)).
apply (H5 n H6).
cut ((SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig c)) n) == (SequenceQPlus (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)))
  (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig c))) n)).
intro H7.
rewrite H7.
reflexivity.
rewrite (Qplus_assoc (proj1_sig a n + - proj1_sig b n) (proj1_sig b n) (- proj1_sig c n)).
rewrite<- (Qplus_assoc (proj1_sig a n) (- proj1_sig b n) (proj1_sig b n)).
rewrite (Qplus_comm (- proj1_sig b n) (proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig b n)).
rewrite (Qplus_0_r (proj1_sig a n)).
reflexivity.
apply (Cv_Q_plus_0_0 (SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b))) (SequenceQPlus (proj1_sig b) (SequenceQOpp (proj1_sig c))) H1 H2).
Qed.

Definition CauchySequenceEquivalenceRelation 
:= mkEquivalenceRelation CauchySequenceQSet CauchySequenceEquivalence CauchySequenceEquivalenceRefl CauchySequenceEquivalenceSymm CauchySequenceEquivalenceTran.

Lemma CRealPlusWellDefined : (forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQPlus a1 a2)) = ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQPlus b1 b2))).
Proof.
intros a1 b1 a2 b2 H1 H2.
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
apply (proj1 (EquivalenceSame CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2) (CauchySequenceQPlus b1 b2))).
cut (Cv_Q (SequenceQPlus (SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1))) (SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2)))) 0).
intro H3.
intros eps H4.
elim (H3 eps H4).
intros N H5.
exists N.
intros n H6.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQPlus a1 a2)) (SequenceQOpp (proj1_sig (CauchySequenceQPlus b1 b2))) n) (0 - SequenceQPlus (SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1))) (SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2))) n)).
apply (H5 n H6).
simpl.
unfold SequenceQPlus.
unfold SequenceQOpp.
cut ((proj1_sig a1 n + proj1_sig a2 n + - (proj1_sig b1 n + proj1_sig b2 n)) == (proj1_sig a1 n + - proj1_sig b1 n + (proj1_sig a2 n + - proj1_sig b2 n))).
intro H7.
rewrite H7.
reflexivity.
apply (Qplus_inj_r (proj1_sig a1 n + proj1_sig a2 n + - (proj1_sig b1 n + proj1_sig b2 n)) (proj1_sig a1 n + - proj1_sig b1 n + (proj1_sig a2 n + - proj1_sig b2 n)) (proj1_sig b1 n + proj1_sig b2 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n + proj1_sig a2 n) (- (proj1_sig b1 n + proj1_sig b2 n)) (proj1_sig b1 n + proj1_sig b2 n)).
rewrite (Qplus_comm (- (proj1_sig b1 n + proj1_sig b2 n)) (proj1_sig b1 n + proj1_sig b2 n)).
rewrite (Qplus_opp_r (proj1_sig b1 n + proj1_sig b2 n)).
rewrite (Qplus_0_r (proj1_sig a1 n + proj1_sig a2 n)).
rewrite (Qplus_assoc (proj1_sig a1 n + - proj1_sig b1 n) (proj1_sig a2 n) (- proj1_sig b2 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n) (- proj1_sig b1 n) (proj1_sig a2 n)).
rewrite (Qplus_comm (- proj1_sig b1 n) (proj1_sig a2 n)).
rewrite (Qplus_assoc (proj1_sig a1 n) (proj1_sig a2 n) (- proj1_sig b1 n)).
rewrite (Qplus_comm (proj1_sig b1 n) (proj1_sig b2 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n + proj1_sig a2 n + - proj1_sig b1 n) (- proj1_sig b2 n) (proj1_sig b2 n + proj1_sig b1 n)).
rewrite (Qplus_assoc (- proj1_sig b2 n) (proj1_sig b2 n) (proj1_sig b1 n)).
rewrite (Qplus_comm (- proj1_sig b2 n) (proj1_sig b2 n)).
rewrite (Qplus_opp_r (proj1_sig b2 n)).
rewrite (Qplus_0_l (proj1_sig b1 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n + proj1_sig a2 n) (- proj1_sig b1 n) (proj1_sig b1 n)).
rewrite (Qplus_comm (- proj1_sig b1 n) (proj1_sig b1 n)).
rewrite (Qplus_opp_r (proj1_sig b1 n)).
rewrite (Qplus_0_r (proj1_sig a1 n + proj1_sig a2 n)).
reflexivity.
apply (Cv_Q_plus_0_0 (SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1))) (SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2))) H1 H2).
Qed.

Lemma CRealOppWellDefined : (forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQOpp a)) = ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQOpp b))).
Proof.
intros a b H1.
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
apply (proj1 (EquivalenceSame CauchySequenceEquivalenceRelation (CauchySequenceQOpp a) (CauchySequenceQOpp b))).
intros eps H2.
elim (H1 eps H2).
intros N H3.
exists N.
intros n H4.
rewrite (Qplus_0_l (- SequenceQPlus (proj1_sig (CauchySequenceQOpp a)) (SequenceQOpp (proj1_sig (CauchySequenceQOpp b))) n)).
rewrite (Qabs_opp (SequenceQPlus (proj1_sig (CauchySequenceQOpp a)) (SequenceQOpp (proj1_sig (CauchySequenceQOpp b))) n)).
rewrite (Qabs_wd (SequenceQPlus (proj1_sig (CauchySequenceQOpp a)) (SequenceQOpp (proj1_sig (CauchySequenceQOpp b))) n) (0 - SequenceQPlus (proj1_sig a) (SequenceQOpp (proj1_sig b)) n)).
apply (H3 n H4).
simpl.
unfold SequenceQPlus.
unfold SequenceQOpp.
apply (Qplus_inj_r (- proj1_sig a n + - - proj1_sig b n) (0 - (proj1_sig a n + - proj1_sig b n)) (proj1_sig a n + - proj1_sig b n)).
rewrite (Qplus_0_l (- (proj1_sig a n + - proj1_sig b n))).
rewrite (Qplus_comm (- (proj1_sig a n + - proj1_sig b n)) (proj1_sig a n + - proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig a n + - proj1_sig b n)).
rewrite (Qplus_assoc (- proj1_sig a n + - - proj1_sig b n) (proj1_sig a n) (- proj1_sig b n)).
rewrite (Qplus_comm (- proj1_sig a n) (- - proj1_sig b n)).
rewrite<- (Qplus_assoc (- - proj1_sig b n) (- proj1_sig a n) (proj1_sig a n)).
rewrite (Qplus_comm (- proj1_sig a n) (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
rewrite (Qplus_0_r (- - proj1_sig b n)).
rewrite (Qplus_comm (- - proj1_sig b n) (- proj1_sig b n)).
apply (Qplus_opp_r (- proj1_sig b n)).
Qed.

Lemma CRealMultWellDefined : (forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQMult a1 a2)) = ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQMult b1 b2))).
Proof.
intros a1 b1 a2 b2 H1 H2.
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
apply (proj1 (EquivalenceSame CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2) (CauchySequenceQMult b1 b2))).
cut (Cv_Q (fun n : nat => (proj1_sig a1 n - proj1_sig b1 n) * (proj1_sig a2 n) + (proj1_sig a2 n - proj1_sig b2 n) * (proj1_sig b1 n)) 0).
intros H3.
intros eps H4.
elim (H3 eps H4).
intros N H5.
exists N.
intros n H6.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQMult a1 a2)) (SequenceQOpp (proj1_sig (CauchySequenceQMult b1 b2))) n) (0 - ((proj1_sig a1 n - proj1_sig b1 n) * proj1_sig a2 n + (proj1_sig a2 n - proj1_sig b2 n) * proj1_sig b1 n))).
apply (H5 n H6).
unfold CauchySequenceQMult.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold SequenceQMul.
simpl.
cut ((proj1_sig a1 n * proj1_sig a2 n + - (proj1_sig b1 n * proj1_sig b2 n)) == ((proj1_sig a1 n - proj1_sig b1 n) * proj1_sig a2 n + (proj1_sig a2 n - proj1_sig b2 n) * proj1_sig b1 n)).
intros H7.
rewrite H7.
reflexivity.
apply (Qplus_inj_r (proj1_sig a1 n * proj1_sig a2 n + - (proj1_sig b1 n * proj1_sig b2 n)) ((proj1_sig a1 n - proj1_sig b1 n) * proj1_sig a2 n + (proj1_sig a2 n - proj1_sig b2 n) * proj1_sig b1 n) (proj1_sig b1 n * proj1_sig b2 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n * proj1_sig a2 n) (- (proj1_sig b1 n * proj1_sig b2 n)) (proj1_sig b1 n * proj1_sig b2 n)).
rewrite (Qplus_comm (- (proj1_sig b1 n * proj1_sig b2 n)) (proj1_sig b1 n * proj1_sig b2 n)).
rewrite (Qplus_opp_r (proj1_sig b1 n * proj1_sig b2 n)).
rewrite (Qplus_0_r (proj1_sig a1 n * proj1_sig a2 n)).
rewrite (Qmult_plus_distr_l (proj1_sig a1 n) (- proj1_sig b1 n) (proj1_sig a2 n)).
rewrite (Qmult_plus_distr_l (proj1_sig a2 n) (- proj1_sig b2 n) (proj1_sig b1 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n * proj1_sig a2 n + - proj1_sig b1 n * proj1_sig a2 n) (proj1_sig a2 n * proj1_sig b1 n + - proj1_sig b2 n * proj1_sig b1 n) (proj1_sig b1 n * proj1_sig b2 n)).
rewrite<- (Qplus_assoc (proj1_sig a2 n * proj1_sig b1 n) (- proj1_sig b2 n * proj1_sig b1 n) (proj1_sig b1 n * proj1_sig b2 n)).
rewrite (Qplus_comm (- proj1_sig b2 n * proj1_sig b1 n) (proj1_sig b1 n * proj1_sig b2 n)).
rewrite (Qmult_comm (proj1_sig b1 n) (proj1_sig b2 n)).
rewrite<- (Qmult_plus_distr_l (proj1_sig b2 n) (- proj1_sig b2 n) (proj1_sig b1 n)).
rewrite (Qplus_opp_r (proj1_sig b2 n)).
rewrite (Qmult_0_l (proj1_sig b1 n)).
rewrite (Qplus_0_r (proj1_sig a2 n * proj1_sig b1 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n * proj1_sig a2 n) (- proj1_sig b1 n * proj1_sig a2 n) (proj1_sig a2 n * proj1_sig b1 n)).
rewrite (Qmult_comm (proj1_sig a2 n) (proj1_sig b1 n)).
rewrite<- (Qmult_plus_distr_l (- proj1_sig b1 n) (proj1_sig b1 n) (proj1_sig a2 n)).
rewrite (Qplus_comm (- proj1_sig b1 n) (proj1_sig b1 n)).
rewrite (Qplus_opp_r (proj1_sig b1 n)).
rewrite (Qmult_0_l (proj1_sig a2 n)).
rewrite (Qplus_0_r (proj1_sig a1 n * proj1_sig a2 n)).
reflexivity.
apply (Cv_Q_plus_0_0 (fun n : nat => (proj1_sig a1 n - proj1_sig b1 n) * proj1_sig a2 n) (fun n : nat => (proj1_sig a2 n - proj1_sig b2 n) * proj1_sig b1 n)).
apply (Cv_Q_mult_0_bounded (fun n : nat => proj1_sig a1 n - proj1_sig b1 n) (fun n : nat => proj1_sig a2 n)).
apply H1.
apply (Cauchy_Q_Bounded (proj1_sig a2) (proj2_sig a2)).
apply (Cv_Q_mult_0_bounded (fun n : nat => proj1_sig a2 n - proj1_sig b2 n) (fun n : nat => proj1_sig b1 n)).
apply H2.
apply (Cauchy_Q_Bounded (proj1_sig b1) (proj2_sig b1)).
Qed.

Lemma CRealInvWellDefined : (forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQInv a)) = ((ToEquivalenceClass CauchySequenceEquivalenceRelation) (CauchySequenceQInv b))).
Proof.
cut (forall a b : CauchySequenceQSet, (Cv_Q (proj1_sig a) 0) -> (CauchySequenceEquivalence a b) -> (Cv_Q (proj1_sig b) 0)).
intros H1.
intros a b H2.
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
elim (classic (Cv_Q (proj1_sig a) 0)).
intro H3.
apply (proj1 (EquivalenceSame CauchySequenceEquivalenceRelation (CauchySequenceQInv a) (CauchySequenceQInv b))).
intros eps H4.
exists O.
intros n H5.
unfold CauchySequenceQInv.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig at 1.
unfold proj1_sig at 2.
rewrite (proj1 (SequenceQInvAltNature (proj1_sig a)) H3).
rewrite (proj1 (SequenceQInvAltNature (proj1_sig b))).
simpl.
apply H4.
apply (H1 a b H3 H2).
intros H3.
apply (proj1 (EquivalenceSame CauchySequenceEquivalenceRelation (CauchySequenceQInv a) (CauchySequenceQInv b))).
cut (~ Cv_Q (proj1_sig b) 0).
intro H4.
simpl.
unfold CauchySequenceEquivalence.
unfold CauchySequenceQInv.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig at 1.
unfold proj1_sig at 2.
cut (Cv_Q (fun n : nat => (proj1_sig b n - proj1_sig a n) * (/ proj1_sig a n * / proj1_sig b n)) 0).
intros H5.
intros eps H6.
elim (H5 eps H6).
intros N H7.
elim (Cv_0_Q_nature (proj1_sig a) (proj2_sig a) H3).
intros M1 H8.
elim (Cv_0_Q_nature (proj1_sig b) (proj2_sig b) H4).
intros M2 H9.
elim (proj2 H8).
intros N1 H10.
elim (proj2 H9).
intros N2 H11.
exists (max N (max N1 N2)).
intros n H12.
rewrite (proj2 (SequenceQInvAltNature (proj1_sig a)) H3).
rewrite (proj2 (SequenceQInvAltNature (proj1_sig b)) H4).
cut (~ proj1_sig a n == 0).
intro H13.
cut (~ proj1_sig b n == 0).
intro H14.
rewrite (Qabs_wd (0 - (/ proj1_sig a n + - / proj1_sig b n)) (0 - (proj1_sig b n - proj1_sig a n) * (/ proj1_sig a n * / proj1_sig b n))).
apply (H7 n).
apply (le_trans N (max N (max N1 N2)) n).
apply (Nat.le_max_l N (max N1 N2)).
apply H12.
rewrite (Qmult_plus_distr_l (proj1_sig b n) (- proj1_sig a n) (/ proj1_sig a n * / proj1_sig b n)).
rewrite (Qmult_comm (/ proj1_sig a n) (/ proj1_sig b n)).
rewrite (Qmult_assoc (proj1_sig b n) (/ proj1_sig b n) (/ proj1_sig a n)).
rewrite (Qmult_inv_r (proj1_sig b n) H14).
rewrite (Qmult_1_l (/ proj1_sig a n)).
cut (- / proj1_sig b n == - proj1_sig a n * (/ proj1_sig b n * / proj1_sig a n)).
intro H15.
rewrite H15.
reflexivity.
apply (Qplus_inj_l (- / proj1_sig b n) (- proj1_sig a n * (/ proj1_sig b n * / proj1_sig a n)) (proj1_sig a n * (/ proj1_sig b n * / proj1_sig a n))).
rewrite<- (Qmult_plus_distr_l (proj1_sig a n) (- proj1_sig a n) (/ proj1_sig b n * / proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
rewrite (Qmult_0_l (/ proj1_sig b n * / proj1_sig a n)).
rewrite (Qmult_comm (/ proj1_sig b n) (/ proj1_sig a n)).
rewrite (Qmult_assoc (proj1_sig a n) (/ proj1_sig a n) (/ proj1_sig b n)).
rewrite (Qmult_inv_r (proj1_sig a n) H13).
rewrite (Qmult_1_l (/ proj1_sig b n)).
apply (Qplus_opp_r (/ proj1_sig b n)).
intro H14.
apply (Qlt_not_eq 0 (Qabs (proj1_sig b n))).
apply (Qlt_trans 0 M2 (Qabs (proj1_sig b n))).
apply (proj1 H9).
apply (H11 n).
apply (le_trans N2 (max N (max N1 N2)) n).
apply (le_trans N2 (max N1 N2) (max N (max N1 N2))).
apply (Nat.le_max_r N1 N2).
apply (Nat.le_max_r N (max N1 N2)).
apply H12.
rewrite H14.
simpl.
reflexivity.
intro H13.
apply (Qlt_not_eq 0 (Qabs (proj1_sig a n))).
apply (Qlt_trans 0 M1 (Qabs (proj1_sig a n))).
apply (proj1 H8).
apply (H10 n).
apply (le_trans N1 (max N (max N1 N2)) n).
apply (le_trans N1 (max N1 N2) (max N (max N1 N2))).
apply (Nat.le_max_l N1 N2).
apply (Nat.le_max_r N (max N1 N2)).
apply H12.
rewrite H13.
simpl.
reflexivity.
apply (Cv_Q_mult_0_bounded (fun n : nat => (proj1_sig b n - proj1_sig a n)) (fun n : nat => (/ proj1_sig a n * / proj1_sig b n))).
apply (CauchySequenceEquivalenceSymm a b H2).
cut (forall N : nat, (exists M : Q, forall n : nat, (n >= N)%nat -> Qabs (/ proj1_sig a n * / proj1_sig b n) <= M) -> (exists M : Q, forall n : nat, Qabs (/ proj1_sig a n * / proj1_sig b n) <= M)).
intro H5.
elim (Cv_0_Q_nature (proj1_sig a) (proj2_sig a) H3).
intros M1 H6.
elim (Cv_0_Q_nature (proj1_sig b) (proj2_sig b) H4).
intros M2 H7.
elim (proj2 H6).
intros N1 H8.
elim (proj2 H7).
intros N2 H9.
apply (H5 (max N1 N2)).
exists (1 / (M2 * M1)).
intros n H10.
cut (M2 * M1 > 0).
intro H11.
apply (Qmult_le_l (Qabs (/ proj1_sig a n * / proj1_sig b n)) (1 / (M2 * M1)) (M2 * M1)).
apply H11.
rewrite (Qmult_1_l (/ (M2 * M1))).
rewrite (Qmult_inv_r (M2 * M1)).
apply (Qle_trans (M2 * M1 * Qabs (/ proj1_sig a n * / proj1_sig b n)) (M2 * Qabs (/ proj1_sig b n)) 1).
rewrite<- (Qmult_assoc M2 M1 (Qabs (/ proj1_sig a n * / proj1_sig b n))).
apply (Qmult_le_l (M1 * Qabs (/ proj1_sig a n * / proj1_sig b n)) (Qabs (/ proj1_sig b n)) M2).
apply (proj1 H7).
rewrite (Qabs_Qmult (/ proj1_sig a n) (/ proj1_sig b n)).
rewrite (Qmult_assoc M1 (Qabs (/ proj1_sig a n)) (Qabs (/ proj1_sig b n))).
rewrite<- (Qmult_1_l (Qabs (/ proj1_sig b n))) at 2.
apply (Qmult_le_compat_r (M1 * Qabs (/ proj1_sig a n)) 1 (Qabs (/ proj1_sig b n))).
cut (1 == Qabs (proj1_sig a n) * Qabs (/ proj1_sig a n)).
intro H12.
rewrite H12.
apply (Qmult_le_compat_r M1 (Qabs (proj1_sig a n)) (Qabs (/ proj1_sig a n))).
apply (Qlt_le_weak M1 (Qabs (proj1_sig a n))).
apply (H8 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H10.
apply (Qabs_nonneg (/ proj1_sig a n)).
rewrite<- (Qabs_Qmult (proj1_sig a n) (/ proj1_sig a n)).
rewrite (Qmult_inv_r (proj1_sig a n)).
simpl.
reflexivity.
intro H12.
apply (Qlt_not_eq 0 (Qabs (proj1_sig a n))).
apply (Qlt_trans 0 M1 (Qabs (proj1_sig a n))).
apply (proj1 H6).
apply (H8 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H10.
rewrite H12.
simpl.
reflexivity.
apply (Qabs_nonneg (/ proj1_sig b n)).
cut (1 == Qabs (proj1_sig b n) * Qabs (/ proj1_sig b n)).
intro H12.
rewrite H12.
apply (Qmult_le_compat_r M2 (Qabs (proj1_sig b n)) (Qabs (/ proj1_sig b n))).
apply (Qlt_le_weak M2 (Qabs (proj1_sig b n))).
apply (H9 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H10.
apply (Qabs_nonneg (/ proj1_sig b n)).
rewrite<- (Qabs_Qmult (proj1_sig b n) (/ proj1_sig b n)).
rewrite (Qmult_inv_r (proj1_sig b n)).
simpl.
reflexivity.
intro H12.
apply (Qlt_not_eq 0 (Qabs (proj1_sig b n))).
apply (Qlt_trans 0 M2 (Qabs (proj1_sig b n))).
apply (proj1 H7).
apply (H9 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H10.
rewrite H12.
simpl.
reflexivity.
intro H12.
apply (Qlt_not_eq 0 (M2 * M1) H11).
rewrite H12.
reflexivity.
rewrite<- (Qmult_0_l M1).
apply (Qmult_lt_compat_r 0 M2 M1).
apply (proj1 H6).
apply (proj1 H7).
intro N.
elim N.
intro H5.
elim H5.
intros M H6.
exists M.
intro n.
apply (H6 n).
apply (le_0_n n).
intros n H5 H6.
apply H5.
elim H6.
intros M H7.
exists (Qabs (M) + Qabs (/ proj1_sig a n * / proj1_sig b n)).
intros n0 H8.
elim (le_lt_or_eq n n0).
intro H9.
apply (Qle_trans (Qabs (/ proj1_sig a n0 * / proj1_sig b n0)) M (Qabs M + Qabs (/ proj1_sig a n * / proj1_sig b n))).
apply (H7 n0 H9).
apply (Qle_trans M (Qabs M) (Qabs M + Qabs (/ proj1_sig a n * / proj1_sig b n))).
apply (Qle_Qabs M).
rewrite<- (Qplus_0_r (Qabs M)) at 1.
apply (Qplus_le_r 0 (Qabs (/ proj1_sig a n * / proj1_sig b n)) (Qabs M)).
apply (Qabs_nonneg (/ proj1_sig a n * / proj1_sig b n)).
intro H9.
rewrite H9.
rewrite<- (Qplus_0_l (Qabs (/ proj1_sig a n0 * / proj1_sig b n0))) at 1.
apply (Qplus_le_l 0 (Qabs M) (Qabs (/ proj1_sig a n0 * / proj1_sig b n0))).
apply (Qabs_nonneg M).
apply H8.
intro H4.
apply H3.
apply (H1 b a).
apply H4.
apply (CauchySequenceEquivalenceSymm a b H2).
intros a b H1 H2.
cut (Cv_Q (fun n : nat => (proj1_sig b n - proj1_sig a n) + proj1_sig a n) 0).
intro H3.
intros eps H4.
elim (H3 eps H4).
intros N H5.
exists N.
intros n H6.
cut (proj1_sig b n == (proj1_sig b n - proj1_sig a n + proj1_sig a n)).
intro H7.
rewrite H7.
apply (H5 n H6).
rewrite<- (Qplus_assoc (proj1_sig b n) (- proj1_sig a n) (proj1_sig a n)).
rewrite (Qplus_comm (- proj1_sig a n) (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
rewrite (Qplus_0_r (proj1_sig b n)).
reflexivity.
apply (Cv_Q_plus_0_0 (fun n : nat => (proj1_sig b n - proj1_sig a n)) (proj1_sig a)).
apply (CauchySequenceEquivalenceSymm a b H2).
apply H1.
Qed.


Lemma CRealLtWellDefined : (forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (CauchySequenceQLt a1 a2) = (CauchySequenceQLt b1 b2)).
Proof.
cut (forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (CauchySequenceQLt a1 a2) -> (CauchySequenceQLt b1 b2)).
intros H1 a1 b1 a2 b2 H2 H3.
apply (propositional_extensionality (CauchySequenceQLt a1 a2) (CauchySequenceQLt b1 b2)).
apply conj.
apply (H1 a1 b1 a2 b2 H2 H3).
apply (H1 b1 a1 b2 a2).
apply (CauchySequenceEquivalenceSymm a1 b1 H2).
apply (CauchySequenceEquivalenceSymm a2 b2 H3).
intros a1 b1 a2 b2 H1 H2 H3.
elim H3.
intros M H4.
elim (proj2 H4).
intros N1 H5.
cut (M / (inject_Z 2) > 0).
intro H6.
cut (M / (inject_Z 2) / (inject_Z 2) > 0).
intro H7.
elim (H1 (M / (inject_Z 2) / (inject_Z 2))).
intros N2 H8.
elim (H2 (M / (inject_Z 2) / (inject_Z 2))).
intros N3 H9.
exists (M / (inject_Z 2)).
apply conj.
apply H6.
exists (max N1 (max N2 N3)).
intros n H10.
apply (Qle_trans (proj1_sig b1 n + M / inject_Z 2) (proj1_sig a2 n - M / inject_Z 2 / inject_Z 2) (proj1_sig b2 n)).
apply (Qle_trans (proj1_sig b1 n + M / inject_Z 2) (proj1_sig a1 n + M / inject_Z 2 / inject_Z 2 + M / inject_Z 2) (proj1_sig a2 n - M / inject_Z 2 / inject_Z 2)).
apply (Qplus_le_l (proj1_sig b1 n) (proj1_sig a1 n + M / inject_Z 2 / inject_Z 2) (M / inject_Z 2)).
apply (Qplus_le_r (proj1_sig b1 n) (proj1_sig a1 n + M / inject_Z 2 / inject_Z 2) (- proj1_sig a1 n)).
rewrite (Qplus_assoc (- proj1_sig a1 n) (proj1_sig a1 n) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_comm (- proj1_sig a1 n) (proj1_sig a1 n)).
rewrite (Qplus_opp_r (proj1_sig a1 n)).
rewrite (Qplus_0_l (M / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (- proj1_sig a1 n + proj1_sig b1 n) (Qabs (- proj1_sig a1 n + proj1_sig b1 n)) (M / inject_Z 2 / inject_Z 2)).
apply (Qle_Qabs (- proj1_sig a1 n + proj1_sig b1 n)).
apply (Qlt_le_weak (Qabs (- proj1_sig a1 n + proj1_sig b1 n)) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qabs_wd (- proj1_sig a1 n + proj1_sig b1 n) (0 - SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1)) n)).
apply (H8 n).
apply (le_trans N2 (max N1 (max N2 N3)) n).
apply (le_trans N2 (max N2 N3) (max N1 (max N2 N3))).
apply (Nat.le_max_l N2 N3).
apply (Nat.le_max_r N1 (max N2 N3)).
apply H10.
rewrite (Qplus_0_l (- SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1)) n)).
apply (Qplus_inj_l (- proj1_sig a1 n + proj1_sig b1 n) (- SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1)) n) (SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1)) n)).
rewrite (Qplus_opp_r (SequenceQPlus (proj1_sig a1) (SequenceQOpp (proj1_sig b1)) n)).
rewrite (Qplus_comm (proj1_sig a1 n) (- proj1_sig b1 n)).
rewrite<- (Qplus_assoc (- proj1_sig b1 n) (proj1_sig a1 n) (- proj1_sig a1 n + proj1_sig b1 n)).
rewrite (Qplus_assoc (proj1_sig a1 n) (- proj1_sig a1 n) (proj1_sig b1 n)).
rewrite (Qplus_opp_r (proj1_sig a1 n)).
rewrite (Qplus_0_l (proj1_sig b1 n)).
rewrite (Qplus_comm (- proj1_sig b1 n) (proj1_sig b1 n)).
apply (Qplus_opp_r (proj1_sig b1 n)).
apply (Qplus_le_l (proj1_sig a1 n + M / inject_Z 2 / inject_Z 2 + M / inject_Z 2) (proj1_sig a2 n - M / inject_Z 2 / inject_Z 2) (M / inject_Z 2 / inject_Z 2)).
rewrite<- (Qplus_assoc (proj1_sig a2 n) (- (M / inject_Z 2 / inject_Z 2)) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_comm (- (M / inject_Z 2 / inject_Z 2)) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_opp_r (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_0_r (proj1_sig a2 n)).
rewrite<- (Qplus_assoc (proj1_sig a1 n) (M / inject_Z 2 / inject_Z 2) (M / inject_Z 2)).
rewrite<- (Qplus_assoc (proj1_sig a1 n) (M / inject_Z 2 / inject_Z 2 + M / inject_Z 2) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_comm (M / inject_Z 2 / inject_Z 2) (M / inject_Z 2)).
rewrite<- (Qplus_assoc (M / inject_Z 2) (M / inject_Z 2 / inject_Z 2) (M / inject_Z 2 / inject_Z 2)).
rewrite (double_Q (M / inject_Z 2)).
rewrite (double_Q M).
apply (H5 n).
apply (le_trans N1 (max N1 (max N2 N3)) n).
apply (Nat.le_max_l N1 (max N2 N3)).
apply H10.
apply (Qplus_le_r (proj1_sig a2 n - M / inject_Z 2 / inject_Z 2) (proj1_sig b2 n) (- proj1_sig b2 n)).
rewrite (Qplus_comm (- proj1_sig b2 n) (proj1_sig b2 n)).
rewrite (Qplus_opp_r (proj1_sig b2 n)).
apply (Qplus_le_l (- proj1_sig b2 n + (proj1_sig a2 n - M / inject_Z 2 / inject_Z 2)) 0 (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_0_l (M / inject_Z 2 / inject_Z 2)).
rewrite<- (Qplus_assoc (- proj1_sig b2 n) (proj1_sig a2 n - M / inject_Z 2 / inject_Z 2) (M / inject_Z 2 / inject_Z 2)).
rewrite<- (Qplus_assoc (proj1_sig a2 n) (- (M / inject_Z 2 / inject_Z 2)) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_comm (- (M / inject_Z 2 / inject_Z 2)) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_opp_r (M / inject_Z 2 / inject_Z 2)).
rewrite (Qplus_0_r (proj1_sig a2 n)).
apply (Qle_trans (- proj1_sig b2 n + proj1_sig a2 n) (Qabs (- proj1_sig b2 n + proj1_sig a2 n)) (M / inject_Z 2 / inject_Z 2)).
apply (Qle_Qabs (- proj1_sig b2 n + proj1_sig a2 n)).
rewrite (Qplus_comm (- proj1_sig b2 n) (proj1_sig a2 n)).
cut (Qabs (proj1_sig a2 n + - proj1_sig b2 n) = Qabs (proj1_sig a2 n - proj1_sig b2 n)).
intro H11.
rewrite H11.
rewrite (Qabs_Qminus (proj1_sig a2 n) (proj1_sig b2 n)).
apply (Qlt_le_weak (Qabs (proj1_sig b2 n - proj1_sig a2 n)) (M / inject_Z 2 / inject_Z 2)).
rewrite (Qabs_wd (proj1_sig b2 n - proj1_sig a2 n) (0 - SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2)) n)).
apply (H9 n).
apply (le_trans N3 (max N1 (max N2 N3)) n).
apply (le_trans N3 (max N2 N3) (max N1 (max N2 N3))).
apply (Nat.le_max_r N2 N3).
apply (Nat.le_max_r N1 (max N2 N3)).
apply H10.
rewrite (Qplus_0_l (- SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2)) n)).
apply (Qplus_inj_l (proj1_sig b2 n - proj1_sig a2 n) (- SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2)) n) (SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2)) n)).
rewrite (Qplus_opp_r (SequenceQPlus (proj1_sig a2) (SequenceQOpp (proj1_sig b2)) n)).
rewrite<- (Qplus_assoc (proj1_sig a2 n) (- (proj1_sig b2 n)) (proj1_sig b2 n - proj1_sig a2 n)).
rewrite (Qplus_assoc (- proj1_sig b2 n) (proj1_sig b2 n) (- proj1_sig a2 n)).
rewrite (Qplus_comm (- proj1_sig b2 n) (proj1_sig b2 n)).
rewrite (Qplus_opp_r (proj1_sig b2 n)).
rewrite (Qplus_0_l (- proj1_sig a2 n)).
apply (Qplus_opp_r (proj1_sig a2 n)).
unfold Qminus.
reflexivity.
apply H7.
apply H7.
apply (Qlt_shift_div_l 0 (M / inject_Z 2) (inject_Z 2)).
cut (0 == inject_Z 0).
intro H7.
rewrite H7.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
unfold inject_Z.
reflexivity.
rewrite (Qmult_0_l (inject_Z 2)).
apply H6.
apply (Qlt_shift_div_l 0 M (inject_Z 2)).
cut (0 == inject_Z 0).
intro H6.
rewrite H6.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
unfold inject_Z.
reflexivity.
rewrite (Qmult_0_l (inject_Z 2)).
apply (proj1 H4).
Qed.

Lemma OCauchy : Cauchy_Q (fun (n : nat) => 0).
Proof.
intros eps H1.
exists O.
intros n m H2 H3.
rewrite (Qplus_opp_r 0).
apply H1.
Qed.

Lemma ICauchy : Cauchy_Q (fun (n : nat) => 1).
Proof.
intros eps H1.
exists O.
intros n m H2 H3.
rewrite (Qplus_opp_r 1).
apply H1.
Qed.

Definition CReal := EquivalenceClassSet (CauchySequenceEquivalenceRelation).

Definition CRealO := ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (n : nat) => 0) OCauchy).

Definition CRealI := ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (n : nat) => 1) ICauchy).

Definition CRealPlus := (ToEquivalenceFunctionBinary CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal (exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2))) CRealPlusWellDefined)).

Definition CRealOpp := (ToEquivalenceFunction CauchySequenceEquivalenceRelation CReal (exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a))) CRealOppWellDefined)).

Definition CRealMult := (ToEquivalenceFunctionBinary CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal (exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2))) CRealMultWellDefined)).

Definition CRealInv := (ToEquivalenceFunction CauchySequenceEquivalenceRelation CReal (exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQInv a))) CRealInvWellDefined)).

Definition CRealLt := (ToEquivalenceFunctionBinary CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop (exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (CauchySequenceQLt a1 a2)) CRealLtWellDefined)).

Lemma CRplus_comm : forall (r1 r2 : CReal), (CRealPlus r1 r2) = (CRealPlus r2 r1).
Proof.
intros A B.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) A a B b).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) B b A a).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H3.
exists O.
intros n H4.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQPlus a b)) (SequenceQOpp (proj1_sig (CauchySequenceQPlus b a))) n) 0).
simpl.
apply H3.
unfold CauchySequenceQPlus.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite (Qplus_comm (proj1_sig a n) (proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig b n + proj1_sig a n)).
apply (Qplus_opp_r 0).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
Qed.

Lemma CRplus_assoc : forall (r1 r2 r3 : CReal), (CRealPlus (CRealPlus r1 r2) r3) = (CRealPlus r1 (CRealPlus r2 r3)).
Proof.
intros A B C.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
elim (proj2_sig C).
intros c H3.
unfold CRealPlus at 1.
unfold CRealPlus at 2.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (CRealPlus A B) (CauchySequenceQPlus a b) C c).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) A a (CRealPlus B C) (CauchySequenceQPlus b c)).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H4.
exists O.
intros n H5.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQPlus (CauchySequenceQPlus a b) c))
     (SequenceQOpp (proj1_sig (CauchySequenceQPlus a (CauchySequenceQPlus b c)))) n) 0).
simpl.
apply H4.
unfold CauchySequenceQPlus.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite<- (Qplus_assoc (proj1_sig a n) (proj1_sig b n) (proj1_sig c n)).
rewrite (Qplus_opp_r (proj1_sig a n + (proj1_sig b n + proj1_sig c n))).
apply (Qplus_opp_r 0).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) B b C c).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQPlus b c)).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) A a B b).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQPlus a b)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
Qed.

Lemma CRplus_opp_r : forall (r : CReal), (CRealPlus r (CRealOpp r)) = CRealO.
Proof.
intro A.
elim (proj2_sig A).
intros a H1.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) A a (CRealOpp A) (CauchySequenceQOpp a)).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H2.
exists O.
intros n H3.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQPlus a (CauchySequenceQOpp a)))
     (SequenceQOpp (proj1_sig (exist Cauchy_Q (fun _ : nat => 0) OCauchy))) n) 0).
simpl.
apply H2.
unfold CauchySequenceQPlus.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite (Qplus_opp_r (proj1_sig a n)).
rewrite (Qplus_opp_r 0).
apply (Qplus_opp_r 0).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
unfold CRealOpp.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a)))) CRealOppWellDefined) A a).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQOpp a)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
Qed.

Lemma CRplus_O_l : forall (r : CReal), (CRealPlus CRealO r) = r.
Proof.
intro A.
elim (proj2_sig A).
intros a H1.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy) A a).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
cut (EquivalenceClass CauchySequenceEquivalenceRelation
  (CauchySequenceQPlus (exist Cauchy_Q (fun _ : nat => 0) OCauchy) a) = EquivalenceClass CauchySequenceEquivalenceRelation a).
intro H2.
rewrite H2.
apply H1.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H3.
exists O.
intros n H4.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQPlus (exist Cauchy_Q (fun _ : nat => 0) OCauchy) a)) (SequenceQOpp (proj1_sig a)) n) 0).
simpl.
apply H3.
unfold CauchySequenceQPlus.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite (Qplus_0_l (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
apply (Qplus_opp_r 0).
unfold CRealO.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
Qed.

Lemma CRmult_comm : forall (r1 r2 : CReal), (CRealMult r1 r2) = (CRealMult r2 r1).
Proof.
intros A B.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a B b).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) B b A a).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H3.
exists O.
intros n H4.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQMult a b)) (SequenceQOpp (proj1_sig (CauchySequenceQMult b a))) n) 0).
simpl.
apply H3.
unfold CauchySequenceQMult.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite (Qmult_comm (proj1_sig a n) (proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig b n * proj1_sig a n)).
apply (Qplus_opp_r 0).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
Qed.

Lemma CRmult_assoc : forall (r1 r2 r3 : CReal), (CRealMult (CRealMult r1 r2) r3) = (CRealMult r1 (CRealMult r2 r3)).
Proof.
intros A B C.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
elim (proj2_sig C).
intros c H3.
unfold CRealMult at 1.
unfold CRealMult at 2.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) (CRealMult A B) (CauchySequenceQMult a b) C c).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a (CRealMult B C) (CauchySequenceQMult b c)).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H4.
exists O.
intros n H5.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQMult (CauchySequenceQMult a b) c))
     (SequenceQOpp (proj1_sig (CauchySequenceQMult a (CauchySequenceQMult b c)))) n) 0).
simpl.
apply H4.
unfold CauchySequenceQMult.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite<- (Qmult_assoc (proj1_sig a n) (proj1_sig b n) (proj1_sig c n)).
rewrite (Qplus_opp_r (proj1_sig a n * (proj1_sig b n * proj1_sig c n))).
apply (Qplus_opp_r 0).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) B b C c).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQMult b c)).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a B b).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQMult a b)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
Qed.

Lemma CRinv_l : forall (r : CReal), (r <> CRealO) -> (CRealMult (CRealInv r) r) = CRealI.
Proof.
intros A H1.
elim (proj2_sig A).
intros a H2.
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) (CRealInv A) (CauchySequenceQInv a) A a).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H3.
cut (~ Cv_Q (proj1_sig a) 0).
intros H4.
cut (exists M : Q, M > 0 /\ (exists N : nat, forall n : nat, (n >= N)%nat -> (Qabs (proj1_sig a n)) > M)).
intros H5.
elim H5.
intros M H6.
elim (proj2 H6).
intros N H7.
exists N.
intros n H8.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQMult (CauchySequenceQInv a) a))
     (SequenceQOpp (proj1_sig (exist Cauchy_Q (fun _ : nat => 1) ICauchy))) n) 0).
simpl.
apply H3.
unfold CauchySequenceQMult.
unfold CauchySequenceQInv.
unfold SequenceQMul.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite (proj2 (SequenceQInvAltNature (proj1_sig a))).
rewrite (Qmult_comm (/ proj1_sig a n) (proj1_sig a n)).
rewrite (Qmult_inv_r (proj1_sig a n)).
rewrite (Qplus_opp_r 1).
apply (Qplus_opp_r 0).
intro H9.
apply (Qlt_not_eq 0 (Qabs (proj1_sig a n))).
apply (Qlt_trans 0 M (Qabs (proj1_sig a n))).
apply (proj1 H6).
apply (H7 n H8).
rewrite H9.
simpl.
reflexivity.
apply H4.
apply (Cv_0_Q_nature (proj1_sig a) (proj2_sig a) H4).
intro H4.
apply H1.
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
cut (proj1_sig CRealO = proj1_sig A).
simpl.
intro H5.
rewrite<- H5.
reflexivity.
cut (proj1_sig CRealO = EquivalenceClass CauchySequenceEquivalenceRelation a).
intro H5.
rewrite H5.
apply H2.
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps2 H5.
elim (H4 eps2).
intros N H6.
exists N.
intros n H7.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (exist Cauchy_Q (fun _ : nat => 0) OCauchy)) (SequenceQOpp (proj1_sig a)) n) (proj1_sig a n - 0)).
rewrite (Qabs_Qminus (proj1_sig a n) 0).
apply (H6 n H7).
unfold SequenceQPlus.
simpl.
rewrite (Qplus_0_l (SequenceQOpp (proj1_sig a) n)).
unfold SequenceQOpp.
unfold Qminus.
rewrite (Qopp_involutive (proj1_sig a n)).
rewrite<- (Qplus_0_l (- 0)).
rewrite (Qplus_opp_r 0).
apply (Qplus_comm 0 (proj1_sig a n)).
apply H5.
unfold CRealInv.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQInv a)))) CRealInvWellDefined) A a).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQInv a)).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl a).
Qed.

Lemma CRmult_I_l : forall (r : CReal), (CRealMult CRealI r) = r.
Proof.
intro A.
elim (proj2_sig A).
intros a H1.
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) CRealI (exist Cauchy_Q (fun (n : nat) => 1) ICauchy) A a).
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
cut (EquivalenceClass CauchySequenceEquivalenceRelation
  (CauchySequenceQMult (exist Cauchy_Q (fun _ : nat => 1) ICauchy) a) = EquivalenceClass CauchySequenceEquivalenceRelation a).
intro H2.
rewrite H2.
apply H1.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H3.
exists O.
intros n H4.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQMult (exist Cauchy_Q (fun _ : nat => 1) ICauchy) a)) (SequenceQOpp (proj1_sig a)) n) 0).
simpl.
apply H3.
unfold CauchySequenceQMult.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
rewrite (Qmult_1_l (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
apply (Qplus_opp_r 0).
unfold CRealO.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
Qed.

Lemma CReal_I_neq_O : CRealI <> CRealO.
Proof.
intro H1.
unfold CRealO in H1.
unfold CRealI in H1.
cut (EquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1) ICauchy) =
     EquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
intro H2.
cut (Rela CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun n : nat => 1) ICauchy) (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
intro H3.
apply (Qlt_irrefl 1).
elim (H3 1).
intros N H4.
cut (1 = Qabs (0 - SequenceQPlus (proj1_sig (exist Cauchy_Q (fun _ : nat => 1) ICauchy)) (SequenceQOpp (proj1_sig (exist Cauchy_Q (fun _ : nat => 0) OCauchy))) N)).
intro H5.
rewrite H5 at 1.
apply (H4 N).
apply (le_n N).
simpl.
reflexivity.
cut (0 = inject_Z 0).
intro H4.
cut (1 = inject_Z 1).
intro H5.
rewrite H4.
rewrite H5.
rewrite<- (Zlt_Qlt 0 1).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
apply H2.
cut (proj1_sig (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1) ICauchy)) =
     proj1_sig (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 0) OCauchy))).
intros H2.
apply H2.
rewrite H1.
reflexivity.
Qed.

Lemma CRmult_plus_distr_l : forall (r1 r2 r3 : CReal), (CRealMult r1 (CRealPlus r2 r3)) = (CRealPlus (CRealMult r1 r2) (CRealMult r1 r3)).
Proof.
intros A B C.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
elim (proj2_sig C).
intros c H3.
unfold CRealMult at 1.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a (CRealPlus B C) (CauchySequenceQPlus b c)).
simpl.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (CRealMult A B) (CauchySequenceQMult a b) (CRealMult A C) (CauchySequenceQMult a c)).
simpl.
apply (sig_map (fun (s : Ensemble CauchySequenceQSet) => exists (b : CauchySequenceQSet), (EquivalenceClass CauchySequenceEquivalenceRelation b) = s)).
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H4.
exists O.
intros n H5.
rewrite (Qabs_wd (0 - SequenceQPlus (proj1_sig (CauchySequenceQMult a (CauchySequenceQPlus b c))) (SequenceQOpp (proj1_sig (CauchySequenceQPlus (CauchySequenceQMult a b) (CauchySequenceQMult a c)))) n) 0).
simpl. 
apply H4.
unfold CauchySequenceQMult.
unfold CauchySequenceQPlus.
simpl.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold SequenceQMul.
rewrite (Qmult_plus_distr_r (proj1_sig a n) (proj1_sig b n) (proj1_sig c n)).
rewrite (Qplus_opp_r (proj1_sig a n * proj1_sig b n + proj1_sig a n * proj1_sig c n)).
apply (Qplus_opp_r 0).
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a B b).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQMult a b)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a C c).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQMult a c)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) B b C c).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQPlus b c)).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
Qed.

Lemma CRlt_asym : forall (r1 r2 : CReal), (CRealLt r1 r2) -> (~ (CRealLt r2 r1)).
Proof.
intros A B.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) A a B b).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) B b A a).
simpl.
intros H3 H4.
elim H3.
intros M1 H5.
elim H4.
intros M2 H6.
elim (proj2 H5).
intros N1 H7.
elim (proj2 H6).
intros N2 H8.
apply (Qle_not_lt (proj1_sig a (max N1 N2)) (proj1_sig b (max N1 N2))).
apply (Qle_trans (proj1_sig a (Init.Nat.max N1 N2)) (proj1_sig a (Init.Nat.max N1 N2) + M1) (proj1_sig b (Init.Nat.max N1 N2))).
rewrite<- (Qplus_0_r (proj1_sig a (Init.Nat.max N1 N2))) at 1.
apply (Qplus_le_r 0 M1 (proj1_sig a (Init.Nat.max N1 N2))).
apply (Qlt_le_weak 0 M1 (proj1 H5)).
apply (H7 (max N1 N2) (Nat.le_max_l N1 N2)).
apply (Qlt_le_trans (proj1_sig b (max N1 N2)) (proj1_sig b (max N1 N2) + M2) (proj1_sig a (max N1 N2))).
rewrite<- (Qplus_0_r (proj1_sig b (Init.Nat.max N1 N2))) at 1.
apply (Qplus_lt_r 0 M2 (proj1_sig b (Init.Nat.max N1 N2))).
apply (proj1 H6).
apply (H8 (max N1 N2) (Nat.le_max_r N1 N2)).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
Qed.

Lemma CRlt_trans : forall (r1 r2 r3 : CReal), (CRealLt r1 r2) -> (CRealLt r2 r3) -> (CRealLt r1 r3).
Proof.
intros A B C.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
elim (proj2_sig C).
intros c H3.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) A a B b).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) B b C c).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) A a C c).
simpl.
intros H4 H5.
elim H4.
intros M1 H6.
elim H5.
intros M2 H7.
elim (proj2 H6).
intros N1 H8.
elim (proj2 H7).
intros N2 H9.
exists (M1 + M2).
apply conj.
apply (Qlt_trans 0 M1 (M1 + M2)).
apply (proj1 H6).
rewrite<- (Qplus_0_r M1) at 1.
apply (Qplus_lt_r 0 M2 M1).
apply (proj1 H7).
exists (max N1 N2).
intros n H10.
apply (Qle_trans (proj1_sig a n + (M1 + M2)) (proj1_sig b n + M2) (proj1_sig c n)).
rewrite (Qplus_assoc (proj1_sig a n) M1 M2).
apply (Qplus_le_l (proj1_sig a n + M1) (proj1_sig b n) M2).
apply (H8 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H10.
apply (H9 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H10.
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
Qed.

Lemma CRtotal_order : forall (r1 r2 : CReal), (CRealLt r1 r2) \/ (r1 = r2) \/ (CRealLt r2 r1).
Proof.
intros A B.
elim (classic (CRealLt A B)).
intro H1.
apply or_introl.
apply H1.
intro H1.
elim (classic (CRealLt B A)).
intro H2.
apply or_intror.
apply or_intror.
apply H2.
intro H2.
apply or_intror.
apply or_introl.
elim (proj2_sig A).
intros a H3.
elim (proj2_sig B).
intros b H4.
unfold CRealLt in H1.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) A a B b) in H1.
simpl in H1.
unfold CRealLt in H2.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) B b A a) in H2.
simpl in H2.
apply sig_map.
rewrite<- H3.
rewrite<- H4.
apply EquivalenceSame.
intros eps H5.
elim (CauchySequenceQLeNature a b H1 eps H5).
intros N1 H6.
elim (CauchySequenceQLeNature b a H2 eps H5).
intros N2 H7.
exists (max N1 N2).
intros n H8.
unfold SequenceQPlus.
unfold SequenceQOpp.
apply Qabs_case.
intro H9.
rewrite (Qplus_0_l (- (proj1_sig a n + - proj1_sig b n))).
apply (Qplus_lt_r (- (proj1_sig a n + - proj1_sig b n)) eps (proj1_sig a n + - proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig a n + - proj1_sig b n)).
rewrite<- (Qplus_assoc (proj1_sig a n) (- proj1_sig b n) eps).
rewrite (Qplus_comm (- proj1_sig b n) eps).
rewrite (Qplus_assoc (proj1_sig a n) eps (- proj1_sig b n)).
rewrite<- (Qplus_opp_r (proj1_sig b n)).
apply (Qplus_lt_l (proj1_sig b n) (proj1_sig a n + eps) (- proj1_sig b n)).
apply (H6 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H8.
intro H9.
rewrite (Qplus_0_l (- (proj1_sig a n + - proj1_sig b n))).
rewrite (Qopp_involutive (proj1_sig a n + - proj1_sig b n)).
rewrite (Qplus_comm (proj1_sig a n) (- proj1_sig b n)).
apply (Qplus_lt_r (- proj1_sig b n + proj1_sig a n) eps (proj1_sig b n)).
rewrite (Qplus_assoc (proj1_sig b n) (- proj1_sig b n) (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig b n)).
rewrite (Qplus_0_l (proj1_sig a n)).
apply (H7 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H8.
rewrite<- H4.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H4.
apply (CauchySequenceEquivalenceRefl b).
Qed.

Lemma CRplus_lt_compat_l : forall (r r1 r2 : CReal), (CRealLt r1 r2) -> (CRealLt (CRealPlus r r1) (CRealPlus r r2)).
Proof.
intros A B C.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
elim (proj2_sig C).
intros c H3.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) B b C c).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (CRealPlus A B) (CauchySequenceQPlus a b) (CRealPlus A C) (CauchySequenceQPlus a c)).
simpl.
intro H4.
elim H4.
intros M H5.
elim (proj2 H5).
intros N H6.
exists M.
apply conj.
apply (proj1 H5).
exists N.
intros n H7.
rewrite<- (Qplus_assoc (proj1_sig a n) (proj1_sig b n) M).
apply (Qplus_le_r (proj1_sig b n + M) (proj1_sig c n) (proj1_sig a n)).
apply (H6 n H7).
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) A a B b).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQPlus a b)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) A a C c).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQPlus a c)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
Qed.

Lemma CRmult_lt_compat_l : forall (r r1 r2 : CReal), (CRealLt CRealO r) -> (CRealLt r1 r2) -> (CRealLt (CRealMult r r1) (CRealMult r r2)).
Proof.
intros A B C.
elim (proj2_sig A).
intros a H1.
elim (proj2_sig B).
intros b H2.
elim (proj2_sig C).
intros c H3.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy) A a).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) B b C c).
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (CRealMult A B) (CauchySequenceQMult a b) (CRealMult A C) (CauchySequenceQMult a c)).
simpl.
intros H4 H5.
elim H4.
intros M1 H6.
elim H5.
intros M2 H7.
elim (proj2 H6).
intros N1 H8.
elim (proj2 H7).
intros N2 H9.
exists (M1 * M2).
apply conj.
rewrite<- (Qmult_0_l M2).
apply (Qmult_lt_r 0 M1 M2).
apply (proj1 H7).
apply (proj1 H6).
exists (max N1 N2).
intros n H10.
apply (Qplus_le_r (proj1_sig (CauchySequenceQMult a b) n + M1 * M2) (proj1_sig (CauchySequenceQMult a c) n) (- proj1_sig (CauchySequenceQMult a b) n)).
rewrite (Qplus_assoc (- proj1_sig (CauchySequenceQMult a b) n) (proj1_sig (CauchySequenceQMult a b) n) (M1 * M2)).
rewrite (Qplus_comm (- proj1_sig (CauchySequenceQMult a b) n) (proj1_sig (CauchySequenceQMult a b) n)).
rewrite (Qplus_opp_r (proj1_sig (CauchySequenceQMult a b) n)).
rewrite (Qplus_0_l (M1 * M2)).
cut (- proj1_sig (CauchySequenceQMult a b) n + proj1_sig (CauchySequenceQMult a c) n == (proj1_sig a n) * (- proj1_sig b n + proj1_sig c n)).
intro H11.
rewrite H11.
apply (Qle_trans (M1 * M2) (M1 * (- proj1_sig b n + proj1_sig c n)) (proj1_sig a n * (- proj1_sig b n + proj1_sig c n))).
apply (Qmult_le_l M2 (- proj1_sig b n + proj1_sig c n) M1).
apply (proj1 H6).
apply (Qplus_le_r M2 (- proj1_sig b n + proj1_sig c n) (proj1_sig b n)).
rewrite (Qplus_assoc (proj1_sig b n) (- proj1_sig b n) (proj1_sig c n)).
rewrite (Qplus_opp_r (proj1_sig b n)).
rewrite (Qplus_0_l (proj1_sig c n)).
apply (H9 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H10.
apply (Qmult_le_r M1 (proj1_sig a n) (- proj1_sig b n + proj1_sig c n)).
apply (Qplus_lt_r 0 (- proj1_sig b n + proj1_sig c n) (proj1_sig b n)).
rewrite (Qplus_assoc (proj1_sig b n) (- proj1_sig b n) (proj1_sig c n)).
rewrite (Qplus_opp_r (proj1_sig b n)).
rewrite (Qplus_0_l (proj1_sig c n)).
apply (Qlt_le_trans (proj1_sig b n + 0) (proj1_sig b n + M2) (proj1_sig c n)).
apply (Qplus_lt_r 0 M2 (proj1_sig b n)).
apply (proj1 H7).
apply (H9 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H10.
rewrite<- (Qplus_0_l M1).
apply (H8 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H10.
apply (Qplus_inj_l (- proj1_sig (CauchySequenceQMult a b) n + proj1_sig (CauchySequenceQMult a c) n) (proj1_sig a n * (- proj1_sig b n + proj1_sig c n)) (proj1_sig (CauchySequenceQMult a b) n)).
rewrite (Qplus_assoc (proj1_sig (CauchySequenceQMult a b) n) (- proj1_sig (CauchySequenceQMult a b) n) (proj1_sig (CauchySequenceQMult a c) n)).
rewrite (Qplus_opp_r (proj1_sig (CauchySequenceQMult a b) n)).
rewrite (Qplus_0_l (proj1_sig (CauchySequenceQMult a c) n)).
rewrite (Qmult_plus_distr_r (proj1_sig a n) (- proj1_sig b n) (proj1_sig c n)).
rewrite (Qplus_assoc (proj1_sig (CauchySequenceQMult a b) n) (proj1_sig a n * - proj1_sig b n) (proj1_sig a n * proj1_sig c n)).
rewrite<- (Qmult_plus_distr_r (proj1_sig a n) (proj1_sig b n) (- proj1_sig b n)).
rewrite (Qplus_opp_r (proj1_sig b n)).
rewrite (Qmult_0_r (proj1_sig a n)).
rewrite (Qplus_0_l (proj1_sig a n * proj1_sig c n)).
reflexivity.
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a B b).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQMult a b)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
unfold CRealMult.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQMult a1 a2)))) CRealMultWellDefined) A a C c).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQMult a c)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
rewrite<- H2.
apply (CauchySequenceEquivalenceRefl b).
rewrite<- H3.
apply (CauchySequenceEquivalenceRefl c).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl a).
Qed.

Lemma CRealabsUnique : forall (r : CReal), exists! (rabs : CReal),
((~ CRealLt r CRealO) -> rabs = r) /\ ((CRealLt r CRealO) -> rabs = (CRealOpp r)).
Proof.
intros A.
apply (proj1 (unique_existence (fun rabs : CReal => (~ CRealLt A CRealO -> rabs = A) /\ (CRealLt A CRealO -> rabs = CRealOpp A)))).
apply conj.
elim (classic (CRealLt A CRealO)).
intro H1.
exists (CRealOpp A).
apply conj.
intro H2.
apply False_ind.
apply (H2 H1).
intro H2.
reflexivity.
intro H1.
exists A.
apply conj.
intro H2.
reflexivity.
intro H2.
apply False_ind.
apply (H1 H2).
intros a1 a2 H1 H2.
elim (classic (CRealLt A CRealO)).
intro H3.
rewrite (proj2 H1 H3).
rewrite (proj2 H2 H3).
reflexivity.
intro H3.
rewrite (proj1 H1 H3).
rewrite (proj1 H2 H3).
reflexivity.
Qed.

Definition CRealabs := fun (r : CReal) => proj1_sig (constructive_definite_description (fun rabs : CReal => (~ CRealLt r CRealO -> rabs = r) /\ (CRealLt r CRealO -> rabs = CRealOpp r)) (CRealabsUnique r)).

Lemma CRealabsNature : forall (r : CReal), (~ CRealLt r CRealO -> CRealabs r = r) /\ (CRealLt r CRealO -> CRealabs r = CRealOpp r).
Proof.
intro r.
apply (proj2_sig (constructive_definite_description (fun rabs : CReal => (~ CRealLt r CRealO -> rabs = r) /\ (CRealLt r CRealO -> rabs = CRealOpp r)) (CRealabsUnique r))).
Qed.

Lemma Cauchy_Q_abs : forall (a : SequenceQ), (Cauchy_Q a) -> (Cauchy_Q (fun (n : nat) => (Qabs (a n)))).
Proof.
intros a H1.
intros eps H2.
elim (H1 eps H2).
intros N H3.
exists N.
intros n m H4 H5.
apply Qabs_case.
intro H6.
apply (Qle_lt_trans (Qabs (a n) - Qabs (a m)) (Qabs (a n - a m)) eps).
apply (Qabs_triangle_reverse (a n) (a m)).
apply H3.
apply H4.
apply H5.
intro H6.
cut (- (Qabs (a n) - Qabs (a m)) == Qabs (a m) - Qabs (a n)).
intro H7.
rewrite H7.
apply (Qle_lt_trans (Qabs (a m) - Qabs (a n)) (Qabs (a m - a n)) eps).
apply (Qabs_triangle_reverse (a m) (a n)).
apply (H3 m n).
apply H5.
apply H4.
apply (Qplus_inj_l (- (Qabs (a n) - Qabs (a m))) (Qabs (a m) - Qabs (a n)) (Qabs (a n) - Qabs (a m))).
rewrite (Qplus_opp_r (Qabs (a n) - Qabs (a m))).
rewrite (Qplus_assoc (Qabs (a n) - Qabs (a m)) (Qabs (a m)) (- Qabs (a n))).
rewrite<- (Qplus_assoc (Qabs (a n)) (- Qabs (a m)) (Qabs (a m))).
rewrite (Qplus_comm (- Qabs (a m)) (Qabs (a m))).
rewrite (Qplus_opp_r (Qabs (a m))).
rewrite (Qplus_0_r (Qabs (a n))).
rewrite (Qplus_opp_r (Qabs (a n))).
reflexivity.
Qed.

Lemma CRealabsNature2 : forall (a : CauchySequenceQSet), (CRealabs (ToEquivalenceClass CauchySequenceEquivalenceRelation a)) = (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (n : nat) => Qabs (proj1_sig a n)) (Cauchy_Q_abs (proj1_sig a) (proj2_sig a)))).
Proof.
intro a.
elim (CRtotal_order (ToEquivalenceClass CauchySequenceEquivalenceRelation a) CRealO).
intro H1.
rewrite (proj2 (CRealabsNature (ToEquivalenceClass CauchySequenceEquivalenceRelation a)) H1).
unfold CRealOpp.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a)))) CRealOppWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation a) a).
simpl.
apply sig_map.
unfold ToEquivalenceClass.
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
unfold CRealLt in H1.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation a) a CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy)) in H1.
simpl in H1.
elim H1.
intros M H2.
elim (proj2 H2).
intros N H3.
intros eps H4.
exists N.
intros n H5.
unfold CauchySequenceQOpp.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig at 1.
unfold proj1_sig at 2.
apply (Qabs_case (proj1_sig a n)).
intro H6.
apply False_ind.
apply (Qlt_irrefl 0).
apply (Qle_lt_trans 0 (proj1_sig a n) 0).
apply H6.
apply (Qlt_le_trans (proj1_sig a n) (proj1_sig a n + M) 0).
rewrite<- (Qplus_0_r (proj1_sig a n)) at 1.
apply (Qplus_lt_r 0 M (proj1_sig a n)).
apply (proj1 H2).
apply (H3 n H5).
intro H6.
rewrite (Qplus_opp_r (- proj1_sig a n)).
rewrite (Qplus_opp_r 0).
apply H4.
apply (CauchySequenceEquivalenceRefl a).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
apply (CauchySequenceEquivalenceRefl a).
intro H1.
elim H1.
intro H2.
rewrite H2.
rewrite (proj1 (CRealabsNature CRealO)).
unfold CRealO.
apply sig_map.
unfold ToEquivalenceClass.
simpl.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
cut (Rela CauchySequenceEquivalenceRelation a (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
intro H3.
intros eps H4.
elim (H3 eps H4).
intros N H5.
exists N.
intros n H6.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig at 1.
unfold proj1_sig at 1.
rewrite (Qplus_0_l (- Qabs (proj1_sig a n))).
rewrite (Qplus_0_l (- - Qabs (proj1_sig a n))).
rewrite (Qopp_involutive (Qabs (proj1_sig a n))).
rewrite (Qabs_pos (Qabs (proj1_sig a n))).
unfold SequenceQPlus in H5.
unfold SequenceQOpp in H5.
unfold proj1_sig at 2 in H5.
rewrite<- (Qabs_opp (proj1_sig a n)).
rewrite<- (Qplus_0_l (- proj1_sig a n)).
rewrite<- (Qplus_0_r (proj1_sig a n)).
rewrite<- (Qplus_opp_r 0) at 2.
apply (H5 n H6).
apply (Qabs_nonneg (proj1_sig a n)).
apply EquivalenceSame.
cut (proj1_sig (ToEquivalenceClass CauchySequenceEquivalenceRelation a) = proj1_sig CRealO).
intro H3.
apply H3.
rewrite H2.
reflexivity.
intro H3.
apply (CRlt_asym CRealO CRealO).
apply H3.
apply H3.
intro H2.
rewrite (proj1 (CRealabsNature (ToEquivalenceClass CauchySequenceEquivalenceRelation a))).
apply sig_map.
apply EquivalenceSame.
unfold CRealLt in H2.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy) (ToEquivalenceClass CauchySequenceEquivalenceRelation a) a) in H2.
simpl in H2.
elim H2.
intros M H3.
elim (proj2 H3).
intros N H4.
exists N.
intros n H5.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig at 2.
rewrite (Qabs_pos (proj1_sig a n)).
rewrite (Qplus_opp_r (proj1_sig a n)).
rewrite (Qplus_opp_r 0).
apply H.
apply (Qle_trans 0 M (proj1_sig a n)).
apply (Qlt_le_weak 0 M).
apply (proj1 H3).
rewrite<- (Qplus_0_l M).
apply (H4 n H5).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
apply (CauchySequenceEquivalenceRefl a).
apply (CRlt_asym CRealO (ToEquivalenceClass CauchySequenceEquivalenceRelation a) H2).
Qed.

Definition Cv_CReal (an : (nat -> CReal)) (a : CReal) := forall (eps : CReal), (CRealLt CRealO eps) -> exists (N : nat), forall (n : nat), (n >= N)%nat -> (CRealLt (CRealabs (CRealPlus (an n) (CRealOpp a))) eps).

Definition Cauchy_CReal (an : (nat -> CReal)) := forall (eps : CReal), (CRealLt CRealO eps) -> exists (N : nat), forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> (CRealLt (CRealabs (CRealPlus (an n) (CRealOpp (an m)))) eps).

Lemma natInverseCauchy : forall (n : nat), Cauchy_Q (fun (m : nat) => 1 / (inject_Z (Z.of_nat n))).
Proof.
intros N eps H1.
exists O.
intros n m H2 H3.
rewrite (Qplus_opp_r (1 / inject_Z (Z.of_nat N))).
apply H1.
Qed.

Lemma ArchimedesQ : forall (eps : Q), eps > 0 -> exists (n : nat), eps > 1 / (inject_Z (Z.of_nat (S n))).
Proof.
intros eps H1.
exists (Pos.to_nat (Qden eps)).
unfold Qlt.
simpl.
apply (Zgt_lt (Qnum eps * ' Pos.of_succ_nat (Pos.to_nat (Qden eps))) (' Qden eps)).
apply (Zle_gt_trans (Qnum eps * (Zpos (Pos.of_succ_nat (Pos.to_nat (Qden eps))))) (Zpos (Pos.of_succ_nat (Pos.to_nat (Qden eps)))) (Zpos (Qden eps))).
rewrite<- (Z.mul_1_l (' Pos.of_succ_nat (Pos.to_nat (Qden eps)))) at 1.
apply (Zmult_lt_0_le_compat_r 1 (Qnum eps) (' Pos.of_succ_nat (Pos.to_nat (Qden eps)))).
apply (Pos2Z.pos_is_pos (Pos.of_succ_nat (Pos.to_nat (Qden eps)))).
apply (Zgt_le_succ 0 (Qnum eps)).
apply (Zlt_gt 0 (Qnum eps)).
rewrite<- (Z.mul_1_r (Qnum eps)).
rewrite<- (Z.mul_0_l (' Qden eps)).
apply H1.
apply (Zlt_gt (' Qden eps) (' Pos.of_succ_nat (Pos.to_nat (Qden eps)))).
apply (Pos2Z.pos_lt_pos (Qden eps) (Pos.of_succ_nat (Pos.to_nat (Qden eps)))).
rewrite (Pos2SuccNat.id_succ (Qden eps)).
apply (Pos.lt_succ_r (Qden eps) (Qden eps)).
apply (Pos.le_refl (Qden eps)).
Qed.

Lemma natInversePositive : forall (n : nat), 1 / (inject_Z (Z.of_nat (S n))) > 0.
Proof.
intros n.
rewrite (Qmult_1_l (/ inject_Z (Z.of_nat (S n)))).
apply (Qinv_lt_0_compat (inject_Z (Z.of_nat (S n)))).
cut (0 = (inject_Z 0)).
intro H1.
rewrite H1.
rewrite<- (Zlt_Qlt 0 (Z.of_nat (S n))).
apply (inj_lt 0 (S n)).
apply (le_n_S 0 n).
apply (le_0_n n).
auto.
Qed.

Lemma natMinUnique : forall (P : nat -> Prop), (exists (n : nat), (P n)) -> (exists! (n : nat), (P n) /\ (forall (m : nat), (P m) -> (n <= m)%nat)).
intros P H1.
apply (proj1 (unique_existence (fun (n : nat) => P n /\ (forall m : nat, P m -> (n <= m)%nat)))).
apply conj.
cut (forall (N : nat), (forall (n : nat), (n <= N)%nat -> (P n) -> exists x : nat, P x /\ (forall m : nat, P m -> (x <= m)%nat))).
intro H2.
elim H1.
intro n.
apply (H2 n n).
apply (le_n n).
intro N.
elim N.
intros n H2 H3.
exists O.
apply conj.
cut (O = n).
intro H4.
rewrite H4.
apply H3.
apply (le_n_0_eq n H2).
intros m H4.
apply (le_0_n m).
intros n1 H2.
intro n.
intro H3.
elim (le_lt_or_eq n (S n1)).
intros H4.
apply (H2 n).
apply (lt_n_Sm_le n n1 H4).
intros H4.
elim (classic (exists (m : nat), (m <= n1)%nat /\ (P m))).
intros H6 H7.
elim H6.
intros n2 H8.
apply (H2 n2).
apply (proj1 H8).
apply (proj2 H8).
intros H5 H6.
exists n.
apply conj.
apply H6.
intros m H7.
cut ((~ (m < n)%nat) -> (n <= m)%nat).
intro H8.
apply H8.
intro H9.
apply H5.
exists m.
apply conj.
apply (le_S_n m n1).
rewrite<- H3.
apply H9.
apply H7.
intro H8.
elim (le_or_lt n m).
intro H9.
apply H9.
intro H9.
apply False_ind.
apply (H8 H9).
apply H3.
intros n1 n2 H2 H3.
apply (le_antisym n1 n2).
apply (proj2 H2 n2).
apply (proj1 H3).
apply (proj2 H3 n1).
apply (proj1 H2).
Qed.

Lemma CauchyEpsMinUnique : (forall (a : CauchySequenceQSet) (eps : Q) (H : eps > 0),(exists! (N : nat), (forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps)) /\ (forall (M : nat), (forall (n m : nat), (n >= M)%nat -> (m >= M)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps)) -> (N <= M)%nat))).
Proof.
intros a eps H1.
apply (natMinUnique (fun (N : nat) => (forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> Qabs (proj1_sig a n - proj1_sig a m) < eps))).
apply (proj2_sig a).
apply H1.
Qed.

Definition CauchyEpsMin (a : CauchySequenceQSet) (eps : Q) (H : eps > 0) := proj1_sig (constructive_definite_description (fun (N : nat) => (forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps)) /\ (forall (M : nat), (forall (n m : nat), (n >= M)%nat -> (m >= M)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps)) -> (N <= M)%nat)) (CauchyEpsMinUnique a eps H)).

Lemma CauchyEpsMinNature2 : forall (a : CauchySequenceQSet) (eps : Q) (H : eps > 0) (n m : nat), (n >= CauchyEpsMin a eps H)%nat -> (m >= CauchyEpsMin a eps H)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps).
Proof.
intros a eps H.
apply (proj1 (proj2_sig ((constructive_definite_description (fun (N : nat) => (forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps)) /\ (forall (M : nat), (forall (n m : nat), (n >= M)%nat -> (m >= M)%nat -> (Qabs ((proj1_sig a n) - (proj1_sig a m)) < eps)) -> (N <= M)%nat)) (CauchyEpsMinUnique a eps H))))).
Qed.

Lemma Cauchy_Cv_CReal : forall (an : nat -> CReal), (Cauchy_CReal an) -> exists (a : CReal), (Cv_CReal an a).
Proof.
intros A H1.
elim (functional_choice (fun (n : nat) (an : CauchySequenceQSet) => EquivalenceClass CauchySequenceEquivalenceRelation an = proj1_sig (A n))).
intros p1A H2.
cut (let ra := (fun (n : nat) => (proj1_sig (p1A n) (CauchyEpsMin (p1A n) (1 / (inject_Z (Z.of_nat (S n)))) (natInversePositive n)))) in exists a : CReal, Cv_CReal A a).
intro H3.
apply H3.
intro ra.
cut (Cauchy_Q ra).
intro H3.
exists (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q ra H3)).
intros EPS H4.
cut (CRealLt CRealO EPS).
intro H5.
elim (proj2_sig EPS).
intros eps H6.
unfold CRealLt in H5.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy) EPS eps) in H5.
simpl in H5.
elim H5.
intros M H7.
cut (M / (inject_Z 2) / (inject_Z 2) > 0).
intro M4pos.
elim (proj2 H7).
intros N1 H8.
cut (Cauchy_Q (fun (n : nat) => M / (inject_Z 2) / (inject_Z 2))).
intro H9.
elim (H1 (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (n : nat) => M / (inject_Z 2) / (inject_Z 2)) H9))).
intros N2 H10.
elim (ArchimedesQ (M / (inject_Z 2) / (inject_Z 2))).
intros N3 H11.
exists (max N2 N3).
intros n H12.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (A n) (p1A n) (CRealOpp (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q ra H3))) (CauchySequenceQOpp (exist Cauchy_Q ra H3))).
simpl.
rewrite (CRealabsNature2 (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (exist Cauchy_Q ra H3)))).
cut (let di := (exist Cauchy_Q (fun n0 : nat => Qabs (proj1_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (exist Cauchy_Q ra H3))) n0))
        (Cauchy_Q_abs (proj1_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (exist Cauchy_Q ra H3))))
           (proj2_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (exist Cauchy_Q ra H3))))))
in CRealLt (ToEquivalenceClass CauchySequenceEquivalenceRelation di) EPS).
intro H13.
apply H13.
intro di.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation di) di EPS eps).
simpl.
exists (M / (inject_Z 2) / (inject_Z 2)).
apply conj.
cut (0 < inject_Z 2).
intro H14.
apply (Qlt_shift_div_l 0 (M / inject_Z 2) (inject_Z 2)).
apply H14.
rewrite (Qmult_0_l (inject_Z 2)).
apply (Qlt_shift_div_l 0 M (inject_Z 2)).
apply H14.
rewrite (Qmult_0_l (inject_Z 2)).
apply (proj1 H7).
cut (0 = inject_Z 0).
intro H14.
rewrite H14.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
exists (max (max N2 N3) (max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))).
intros m H14.
cut (CRealLt (CRealabs (CRealPlus (A n) (CRealOpp (A m)))) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9))).
intro H16.
unfold di.
unfold proj1_sig at 1.
unfold CRealPlus in H16.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (A n) (p1A n) (CRealOpp (A m)) (CauchySequenceQOpp (p1A m))) in H16.
simpl in H16.
rewrite (CRealabsNature2 (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m)))) in H16.
cut (CauchySequenceQLt (exist Cauchy_Q (fun n0 : nat => Qabs (proj1_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))) n0))
              (Cauchy_Q_abs (proj1_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))))
                 (proj2_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m)))))) 
(exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)).
intro H17.
unfold CauchySequenceQOpp.
unfold CauchySequenceQPlus.
unfold SequenceQOpp.
unfold SequenceQPlus.
unfold proj1_sig at 1.
unfold proj1_sig at 2.
elim H17.
intros M2 H18.
elim (proj2 H18).
intros N4 H19.
apply (Qle_trans (Qabs (proj1_sig (p1A n) m + - proj1_sig (exist Cauchy_Q ra H3) m) + M / inject_Z 2 / inject_Z 2) M (proj1_sig eps m)).
rewrite<- (Qabs_opp (proj1_sig (p1A n) m + - proj1_sig (exist Cauchy_Q ra H3) m)).
cut ((- (proj1_sig (p1A n) m + - proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) == 
(proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) - proj1_sig (p1A m) (max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) +
(proj1_sig (p1A m) (max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) - proj1_sig (p1A n) (max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) +
(proj1_sig (p1A n) (max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) - proj1_sig (p1A n) m)).
intro H20.
unfold ra.
rewrite H20.
rewrite<- (double_Q M) at 2.
rewrite<- (double_Q (M / inject_Z 2)) at 2.
rewrite<- (double_Q (M / inject_Z 2)) at 4.
rewrite (Qplus_assoc (M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2) (M / inject_Z 2 / inject_Z 2) (M / inject_Z 2 / inject_Z 2)).
apply (Qplus_le_l (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
proj1_sig (p1A m) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
(proj1_sig (p1A m) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
 proj1_sig (p1A n) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) +
(proj1_sig (p1A n) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) - proj1_sig (p1A n) m)))
(M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2)
(M / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) +
   (proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n) m)))
(Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) +
Qabs (proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n) m))
(M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2)).
apply (Qabs_triangle (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))
(proj1_sig (p1A n)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
   proj1_sig (p1A n) m)).
apply (Qle_trans (Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) +
Qabs
  (proj1_sig (p1A n)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
   proj1_sig (p1A n) m))
(Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) + M / inject_Z 2 / inject_Z 2
) (M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2)).
apply (Qplus_le_r (Qabs
  (proj1_sig (p1A n)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
   proj1_sig (p1A n) m))
(M / inject_Z 2 / inject_Z 2)
(Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))))).
apply (Qlt_le_weak (Qabs (proj1_sig (p1A n) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) - proj1_sig (p1A n) m)) (M / inject_Z 2 / inject_Z 2)).
apply (CauchyEpsMinNature2 (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos).
apply (le_trans (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos) m (max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))).
apply (le_trans (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))) m).
apply (le_trans (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)))).
apply (Nat.le_max_r N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)).
apply (Nat.le_max_r (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))).
apply H14.
apply (Nat.le_max_l m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
apply (le_trans (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)))).
apply (le_trans (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)))).
apply (Nat.le_max_r N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)).
apply (Nat.le_max_r (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))).
apply H14.
apply (Qplus_le_l (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
proj1_sig (p1A m) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
(proj1_sig (p1A m) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
 proj1_sig (p1A n) (Init.Nat.max m (max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))))
(M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2)
(M / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) +
   (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))))
(Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) +
Qabs (proj1_sig (p1A m)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
    proj1_sig (p1A n)
      (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))
(M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2)).
apply (Qabs_triangle (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))
(proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
   proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
apply (Qle_trans (Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) +
Qabs
  (proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
   proj1_sig (p1A n)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))
(Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) + M / inject_Z 2 / inject_Z 2)
(M / inject_Z 2 / inject_Z 2 + M / inject_Z 2 / inject_Z 2)).

apply (Qplus_le_r (Qabs
  (proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
   proj1_sig (p1A n)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) (M / inject_Z 2 / inject_Z 2) (Qabs
  (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))).
unfold CauchySequenceQPlus in H19.
unfold CauchySequenceQOpp in H19.
unfold SequenceQPlus in H19.
unfold SequenceQOpp in H19.
unfold proj1_sig at 1 in H19.
unfold proj1_sig at 1 in H19.
unfold proj1_sig at 2 in H19.
unfold proj1_sig at 3 in H19.
apply (Qle_trans (Qabs (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))
(Qabs (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) + M2)
(M / inject_Z 2 / inject_Z 2)).
rewrite<- (Qplus_0_r (Qabs (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))) at 1.
apply (Qplus_le_r 0 M2 (Qabs (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) -
proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))).
apply (Qlt_le_weak 0 M2 (proj1 H18)).
rewrite (Qabs_Qminus (proj1_sig (p1A m)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))
(proj1_sig (p1A n)
     (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
apply (H19 (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))).
apply (le_trans N4 (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))).
apply (Nat.le_max_l N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))).
apply (Nat.le_max_r m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
apply (Qplus_le_l (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) (M / inject_Z 2 / inject_Z 2) (M / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) (1 / inject_Z (Z.of_nat (S N3))) (M / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))))
(1 / inject_Z (Z.of_nat (S m))) (1 / inject_Z (Z.of_nat (S N3)))).
apply (Qlt_le_weak (Qabs (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
   proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))) (1 / inject_Z (Z.of_nat (S m)))).
apply (CauchyEpsMinNature2 (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)).
apply le_n.
apply (le_trans (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))).
apply (Nat.le_max_r N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))).
apply (Nat.le_max_r m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
apply (Qmult_le_r (1 / inject_Z (Z.of_nat (S m))) (1 / inject_Z (Z.of_nat (S N3))) (inject_Z (Z.of_nat (S m)))).
apply (natInversePositive m).
rewrite<- (Qmult_assoc 1 (/ inject_Z (Z.of_nat (S m))) (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_comm (/ inject_Z (Z.of_nat (S m))) (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_inv_r (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_1_r 1).
rewrite (Qmult_1_l (/ inject_Z (Z.of_nat (S N3)))).
apply (Qmult_le_l 1 (/ inject_Z (Z.of_nat (S N3)) * inject_Z (Z.of_nat (S m))) (inject_Z (Z.of_nat (S N3)))).
apply (natInversePositive N3).
rewrite (Qmult_1_r (inject_Z (Z.of_nat (S N3)))).
rewrite (Qmult_assoc (inject_Z (Z.of_nat (S N3))) (/ inject_Z (Z.of_nat (S N3))) (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_inv_r (inject_Z (Z.of_nat (S N3)))).
rewrite (Qmult_1_l (inject_Z (Z.of_nat (S m)))).
rewrite<- Zle_Qle.
apply (inj_le (S N3) (S m)).
apply (le_n_S N3 m).
apply (le_trans N3 (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))) m).
apply (le_trans N3 (Init.Nat.max N2 N3) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)))).
apply (Nat.le_max_r N2 N3).
apply (Nat.le_max_l (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))).
apply H14.
intro H21.
apply (Qlt_irrefl (inject_Z (Z.of_nat (S N3)))).
rewrite H21 at 1.
apply (natInversePositive N3).
intro H21.
apply (Qlt_irrefl (inject_Z (Z.of_nat (S m)))).
rewrite H21 at 1.
apply (natInversePositive m).
apply (Qlt_le_weak (1 / inject_Z (Z.of_nat (S N3))) (M / inject_Z 2 / inject_Z 2) H11).
rewrite (Qplus_assoc (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) -
proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (- proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite<- (Qplus_assoc (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (- proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite (Qplus_comm (- proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite (Qplus_opp_r (proj1_sig (p1A m) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite (Qplus_0_r (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
rewrite (Qplus_assoc (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) + - proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (- proj1_sig (p1A n) m)).
rewrite<- (Qplus_assoc (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (- proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite (Qplus_comm (- proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))))) (proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite (Qplus_opp_r (proj1_sig (p1A n) (Init.Nat.max m (Init.Nat.max N4 (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))))).
rewrite (Qplus_0_r (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
apply (Qplus_inj_l (- (proj1_sig (p1A n) m + - proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))) (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)) + - proj1_sig (p1A n) m) (proj1_sig (p1A n) m + - proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
rewrite (Qplus_opp_r (proj1_sig (p1A n) m + - proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
rewrite (Qplus_assoc (proj1_sig (p1A n) m + - proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (- proj1_sig (p1A n) m)).
rewrite<- (Qplus_assoc (proj1_sig (p1A n) m) (- proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
rewrite (Qplus_comm (- proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))) (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
rewrite (Qplus_opp_r (proj1_sig (p1A m) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)))).
rewrite (Qplus_0_r (proj1_sig (p1A n) m)).
rewrite (Qplus_opp_r (proj1_sig (p1A n) m)).
reflexivity.
simpl in H8.
rewrite<- (Qplus_0_l M).
apply (H8 m).
apply (le_trans N1 (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))) m).
apply (le_trans N1 (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)))).
apply (Nat.le_max_l N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos)).
apply (Nat.le_max_r (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))).
apply H14.
cut (let di2 := (exist Cauchy_Q (fun n0 : nat => Qabs (proj1_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))) n0))
     (Cauchy_Q_abs (proj1_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))))
        (proj2_sig (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))))))
in CauchySequenceQLt di2 (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)).
intro H18.
apply H18.
intro di2.
cut (CRealLt (ToEquivalenceClass CauchySequenceEquivalenceRelation di2) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9))).
intro H19.
unfold CRealLt in H19.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation di2) di2 (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)) (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)) in H19.
apply H19.
apply (CauchySequenceEquivalenceRefl di2).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)).
apply H16.
rewrite<- (H2 n).
apply (CauchySequenceEquivalenceRefl (p1A n)).
unfold CRealOpp.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a)))) CRealOppWellDefined) (A m) (p1A m)).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQOpp (p1A m))).
rewrite<- (H2 m).
apply (CauchySequenceEquivalenceRefl (p1A m)).
apply (H10 n m).
apply (le_trans N2 (max N2 N3) n).
apply (Nat.le_max_l N2 N3).
apply H12.
apply (le_trans N2 (max N2 N3) m).
apply (Nat.le_max_l N2 N3).
apply (le_trans (Init.Nat.max N2 N3) (Init.Nat.max (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))) m).
apply (Nat.le_max_l (Init.Nat.max N2 N3) (Init.Nat.max N1 (CauchyEpsMin (p1A n) (M / inject_Z 2 / inject_Z 2) M4pos))).
apply H14.
apply (CauchySequenceEquivalenceRefl di).
rewrite<- H6.
apply (CauchySequenceEquivalenceRefl eps).
rewrite<- (H2 n).
apply (CauchySequenceEquivalenceRefl (p1A n)).
unfold CRealOpp at 1.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a)))) CRealOppWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q ra H3)) (exist Cauchy_Q ra H3)).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQOpp (exist Cauchy_Q ra H3))).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q ra H3)).
apply M4pos.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) CRealO (exist Cauchy_Q (fun _ : nat => 0) OCauchy) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)) (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)).
simpl in H1.
unfold proj1_sig.
exists (M / inject_Z 2 / inject_Z 2).
apply conj.
apply M4pos.
exists O.
intros n H10.
simpl.
rewrite (Qplus_0_l (M / inject_Z 2 / inject_Z 2)).
apply (Qle_refl (M / inject_Z 2 / inject_Z 2)).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => M / inject_Z 2 / inject_Z 2) H9)).
intros ep H9.
exists O.
intros n m H10 H11.
rewrite (Qplus_opp_r (M / inject_Z 2 / inject_Z 2)).
simpl.
apply H9.
cut (0 < inject_Z 2).
intro H14.
apply (Qlt_shift_div_l 0 (M / inject_Z 2) (inject_Z 2)).
apply H14.
rewrite (Qmult_0_l (inject_Z 2)).
apply (Qlt_shift_div_l 0 M (inject_Z 2)).
apply H14.
rewrite (Qmult_0_l (inject_Z 2)).
apply (proj1 H7).
cut (0 = inject_Z 0).
intro H14.
rewrite H14.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
rewrite<- H6.
apply (CauchySequenceEquivalenceRefl eps).
apply H4.
intros eps H3.
cut (0 < eps / inject_Z 2 / inject_Z 2).
intro H4.
cut (Cauchy_Q (fun (n : nat) => eps / (inject_Z 2) / (inject_Z 2))).
intro H5.
elim (H1 (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (n : nat) => eps / (inject_Z 2) / (inject_Z 2)) H5))).
intros N1 H6.
elim (ArchimedesQ (eps / (inject_Z 2) / (inject_Z 2))).
intros N2 H7.
exists (max N1 (S N2)).
intros n m H8 H9.
cut (CRealLt (CRealabs (CRealPlus (A n) (CRealOpp (A m)))) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5))).
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (A n) (p1A n) (CRealOpp (A m)) (CauchySequenceQOpp (p1A m))).
unfold proj1_sig at 1.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (CRealabs
     (ToEquivalenceClass CauchySequenceEquivalenceRelation
        (CauchySequenceQPlus (p1A n)
           (CauchySequenceQOpp (p1A m))))) 
      (exist Cauchy_Q
        (fun n0 : nat =>
         Qabs
           (proj1_sig
              (CauchySequenceQPlus (p1A n)
                 (CauchySequenceQOpp (p1A m))) n0))
        (Cauchy_Q_abs
           (proj1_sig
              (CauchySequenceQPlus (p1A n)
                 (CauchySequenceQOpp (p1A m))))
           (proj2_sig
              (CauchySequenceQPlus (p1A n)
                 (CauchySequenceQOpp (p1A m))))))
(ToEquivalenceClass CauchySequenceEquivalenceRelation
     (exist Cauchy_Q
        (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5))
(exist Cauchy_Q
        (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5)).
unfold proj1_sig at 1.
intro H10.
elim H10.
intros M H11.
elim (proj2 H11).
intros N3 H12.
cut (let N4 := (max N3 (max (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
        (natInversePositive n)) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
        (natInversePositive m)))) in Qabs (ra n - ra m) < eps).
intro H13.
apply H13.
intro N4.
cut ((ra n - ra m) == (ra n - proj1_sig (p1A n) N4) + (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4) + (proj1_sig (p1A m) N4 - ra m)).
intro H13.
rewrite H13.
rewrite<- (double_Q eps).
rewrite<- (double_Q (eps / inject_Z 2)) at 1.
apply (Qle_lt_trans (Qabs (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4) +
   (proj1_sig (p1A m) N4 - ra m))) (Qabs (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) + Qabs (proj1_sig (p1A m) N4 - ra m)) (eps / inject_Z 2 / inject_Z 2 +
eps / inject_Z 2 / inject_Z 2 + eps / inject_Z 2)).
apply (Qabs_triangle (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) (proj1_sig (p1A m) N4 - ra m)).
apply (Qlt_le_trans (Qabs
  (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) +
Qabs (proj1_sig (p1A m) N4 - ra m)) (Qabs
  (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) + (eps / inject_Z 2)) (eps / inject_Z 2 / inject_Z 2 +
eps / inject_Z 2 / inject_Z 2 + eps / inject_Z 2)).
apply (Qplus_lt_r (Qabs (proj1_sig (p1A m) N4 - ra m)) (eps / inject_Z 2) (Qabs (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)))).
unfold ra.
apply (Qlt_trans (Qabs (proj1_sig (p1A m) N4 -
   proj1_sig (p1A m)
     (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
        (natInversePositive m)))) (1 / inject_Z (Z.of_nat (S m))) (eps / inject_Z 2)).
apply (CauchyEpsMinNature2 (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m)).
apply (le_trans (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
   (natInversePositive m)) (max
           (CauchyEpsMin (p1A n)
              (1 / inject_Z (Z.of_nat (S n)))
              (natInversePositive n))
           (CauchyEpsMin (p1A m)
              (1 / inject_Z (Z.of_nat (S m)))
              (natInversePositive m))) N4).
apply (Nat.le_max_r (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
      (natInversePositive n)) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
      (natInversePositive m))).
apply (Nat.le_max_r N3 (max
           (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
              (natInversePositive n))
           (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
              (natInversePositive m)))).
apply (le_n (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m))) (natInversePositive m))).
apply (Qlt_trans (1 / inject_Z (Z.of_nat (S m))) (eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2)).
apply (Qle_lt_trans (1 / inject_Z (Z.of_nat (S m))) (1 / inject_Z (Z.of_nat (S N2))) (eps / inject_Z 2 / inject_Z 2)).
apply (Qmult_le_r (1 / inject_Z (Z.of_nat (S m))) (1 / inject_Z (Z.of_nat (S N2))) (inject_Z (Z.of_nat (S m)))).
apply (natInversePositive m).
rewrite<- (Qmult_assoc 1 (/ inject_Z (Z.of_nat (S m))) (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_comm (/ inject_Z (Z.of_nat (S m))) (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_inv_r (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_1_r 1).
rewrite (Qmult_1_l (/ inject_Z (Z.of_nat (S N2)))).
apply (Qmult_le_l 1 (/ inject_Z (Z.of_nat (S N2)) * inject_Z (Z.of_nat (S m))) (inject_Z (Z.of_nat (S N2)))).
apply (natInversePositive N2).
rewrite (Qmult_1_r (inject_Z (Z.of_nat (S N2)))).
rewrite (Qmult_assoc (inject_Z (Z.of_nat (S N2))) (/ inject_Z (Z.of_nat (S N2))) (inject_Z (Z.of_nat (S m)))).
rewrite (Qmult_inv_r (inject_Z (Z.of_nat (S N2)))).
rewrite (Qmult_1_l (inject_Z (Z.of_nat (S m)))).
rewrite<- Zle_Qle.
apply (inj_le (S N2) (S m)).
apply (le_S (S N2) m).
apply (le_trans (S N2) (max N1 (S N2)) m).
apply (Nat.le_max_r N1 (S N2)).
apply H9.
intro H14.
apply (Qlt_irrefl (inject_Z (Z.of_nat (S N2)))).
rewrite H14 at 1.
apply (natInversePositive N3).
intro H14.
apply (Qlt_irrefl (inject_Z (Z.of_nat (S m)))).
rewrite H14 at 1.
apply (natInversePositive m).
apply H7.
rewrite<- (Qplus_0_r (eps / inject_Z 2 / inject_Z 2)).
rewrite<- (double_Q (eps / inject_Z 2)) at 2.
apply (Qplus_lt_r 0 (eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2 / inject_Z 2)).
apply H4.
apply (Qplus_le_l (Qabs (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4))) (eps / inject_Z 2 / inject_Z 2 + eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2)).
apply (Qle_trans (Qabs (ra n - proj1_sig (p1A n) N4 +
   (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4))) (Qabs (ra n - proj1_sig (p1A n) N4) + Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) (eps / inject_Z 2 / inject_Z 2 + eps / inject_Z 2 / inject_Z 2)).
apply (Qabs_triangle (ra n - proj1_sig (p1A n) N4) (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)).
apply (Qle_trans (Qabs (ra n - proj1_sig (p1A n) N4) +
Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) (Qabs (ra n - proj1_sig (p1A n) N4) + eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2 / inject_Z 2 + eps / inject_Z 2 / inject_Z 2)).
apply (Qplus_le_r (Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) (eps / inject_Z 2 / inject_Z 2) (Qabs (ra n - proj1_sig (p1A n) N4))).
unfold proj1_sig in H12 at 1.
unfold CauchySequenceQPlus in H12.
unfold CauchySequenceQOpp in H12.
unfold proj1_sig in H12 at 1.
unfold proj1_sig in H12 at 2.
unfold proj1_sig in H12 at 3.
unfold SequenceQPlus in H12.
unfold SequenceQOpp in H12.
apply (Qle_trans (Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4)) (Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4) + M) (eps / inject_Z 2 / inject_Z 2)).
rewrite<- (Qplus_0_r (Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4))) at 1.
apply (Qplus_le_r 0 M (Qabs (proj1_sig (p1A n) N4 - proj1_sig (p1A m) N4))).
apply (Qlt_le_weak 0 M).
apply (proj1 H11).
apply (H12 N4).
apply (Nat.le_max_l N3 (Init.Nat.max
           (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
              (natInversePositive n))
           (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
              (natInversePositive m)))).
apply (Qplus_le_l (Qabs (ra n - proj1_sig (p1A n) N4)) (eps / inject_Z 2 / inject_Z 2) (eps / inject_Z 2 / inject_Z 2)).
apply (Qle_trans (Qabs (ra n - proj1_sig (p1A n) N4)) (1 / inject_Z (Z.of_nat (S n))) (eps / inject_Z 2 / inject_Z 2)).
apply (Qlt_le_weak (Qabs (ra n - proj1_sig (p1A n) N4)) (1 / inject_Z (Z.of_nat (S n)))).
unfold ra.
apply (CauchyEpsMinNature2 (p1A n) (1 / inject_Z (Z.of_nat (S n))) (natInversePositive n)).
apply (le_n (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
   (natInversePositive n))).
apply (le_trans (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
   (natInversePositive n)) (max
           (CauchyEpsMin (p1A n)
              (1 / inject_Z (Z.of_nat (S n)))
              (natInversePositive n))
           (CauchyEpsMin (p1A m)
              (1 / inject_Z (Z.of_nat (S m)))
              (natInversePositive m))) N4).
apply (Nat.le_max_l (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
      (natInversePositive n)) (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
      (natInversePositive m))).
apply (Nat.le_max_r N3 (max
           (CauchyEpsMin (p1A n) (1 / inject_Z (Z.of_nat (S n)))
              (natInversePositive n))
           (CauchyEpsMin (p1A m) (1 / inject_Z (Z.of_nat (S m)))
              (natInversePositive m)))).
apply (Qle_trans (1 / inject_Z (Z.of_nat (S n))) (1 / inject_Z (Z.of_nat (S N2))) (eps / inject_Z 2 / inject_Z 2)).
apply (Qmult_le_r (1 / inject_Z (Z.of_nat (S n))) (1 / inject_Z (Z.of_nat (S N2))) (inject_Z (Z.of_nat (S n)))).
apply (natInversePositive n).
rewrite<- (Qmult_assoc 1 (/ inject_Z (Z.of_nat (S n))) (inject_Z (Z.of_nat (S n)))).
rewrite (Qmult_comm (/ inject_Z (Z.of_nat (S n))) (inject_Z (Z.of_nat (S n)))).
rewrite (Qmult_inv_r (inject_Z (Z.of_nat (S n)))).
rewrite (Qmult_1_r 1).
rewrite (Qmult_1_l (/ inject_Z (Z.of_nat (S N2)))).
apply (Qmult_le_l 1 (/ inject_Z (Z.of_nat (S N2)) * inject_Z (Z.of_nat (S n))) (inject_Z (Z.of_nat (S N2)))).
apply (natInversePositive N2).
rewrite (Qmult_1_r (inject_Z (Z.of_nat (S N2)))).
rewrite (Qmult_assoc (inject_Z (Z.of_nat (S N2))) (/ inject_Z (Z.of_nat (S N2))) (inject_Z (Z.of_nat (S n)))).
rewrite (Qmult_inv_r (inject_Z (Z.of_nat (S N2)))).
rewrite (Qmult_1_l (inject_Z (Z.of_nat (S n)))).
rewrite<- Zle_Qle.
apply (inj_le (S N2) (S n)).
apply (le_S (S N2) n).
apply (le_trans (S N2) (max N1 (S N2)) n).
apply (Nat.le_max_r N1 (S N2)).
apply H8.
intro H14.
apply (Qlt_irrefl (inject_Z (Z.of_nat (S N2)))).
rewrite H14 at 1.
apply (natInversePositive N3).
intro H14.
apply (Qlt_irrefl (inject_Z (Z.of_nat (S n)))).
rewrite H14 at 1.
apply (natInversePositive n).
apply (Qlt_le_weak (1 / inject_Z (Z.of_nat (S N2))) (eps / inject_Z 2 / inject_Z 2)).
apply H7.
rewrite (Qplus_assoc (ra n - proj1_sig (p1A n) N4) (proj1_sig (p1A n) N4) (- proj1_sig (p1A m) N4)).
rewrite<- (Qplus_assoc (ra n) (- proj1_sig (p1A n) N4) (proj1_sig (p1A n) N4)).
rewrite (Qplus_comm (- proj1_sig (p1A n) N4) (proj1_sig (p1A n) N4)).
rewrite (Qplus_opp_r (proj1_sig (p1A n) N4)).
rewrite (Qplus_0_r (ra n)).
rewrite (Qplus_assoc (ra n + - proj1_sig (p1A m) N4) (proj1_sig (p1A m) N4) (- ra m)).
rewrite<- (Qplus_assoc (ra n) (- proj1_sig (p1A m) N4) (proj1_sig (p1A m) N4)).
rewrite (Qplus_comm (- proj1_sig (p1A m) N4) (proj1_sig (p1A m) N4)).
rewrite (Qplus_opp_r (proj1_sig (p1A m) N4)).
rewrite (Qplus_0_r (ra n)).
reflexivity.
rewrite (CRealabsNature2 (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m)))).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q
     (fun n0 : nat =>
      Qabs
        (proj1_sig
           (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))) n0))
     (Cauchy_Q_abs
        (proj1_sig
           (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))))
        (proj2_sig
           (CauchySequenceQPlus (p1A n) (CauchySequenceQOpp (p1A m))))))).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5)).
rewrite<- (H2 n).
apply (CauchySequenceEquivalenceRefl (p1A n)).
unfold CRealOpp.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a)))) CRealOppWellDefined) (A m) (p1A m)).
simpl.
apply (CauchySequenceEquivalenceRefl (CauchySequenceQOpp (p1A m))).
rewrite<- (H2 m).
apply (CauchySequenceEquivalenceRefl (p1A m)).
apply (H6 n m).
apply (le_trans N1 (max N1 (S N2)) n).
apply (Nat.le_max_l N1 (S N2)).
apply H8.
apply (le_trans N1 (max N1 (S N2)) m).
apply (Nat.le_max_l N1 (S N2)).
apply H9.
apply H4.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) CRealO (exist Cauchy_Q (fun _ : nat => 0) OCauchy) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5)) (exist Cauchy_Q (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5)).
simpl.
exists (eps / inject_Z 2 / inject_Z 2).
apply conj.
apply H4.
exists O.
intros n H6.
simpl.
rewrite (Qplus_0_l (eps / inject_Z 2 / inject_Z 2)).
apply (Qle_refl (eps / inject_Z 2 / inject_Z 2)).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => eps / inject_Z 2 / inject_Z 2) H5)).
intros ep H5.
exists O.
intros n m H6 H7.
rewrite (Qplus_opp_r (eps / inject_Z 2 / inject_Z 2)).
apply H5.
cut (0 < inject_Z 2).
intro H4.
apply (Qlt_shift_div_l 0 (eps / inject_Z 2) (inject_Z 2)).
apply H4.
rewrite (Qmult_0_l (inject_Z 2)).
apply (Qlt_shift_div_l 0 eps (inject_Z 2)).
apply H4.
rewrite (Qmult_0_l (inject_Z 2)).
apply H3.
cut (0 = inject_Z 0).
intro H4.
rewrite H4.
rewrite<- (Zlt_Qlt 0 2).
apply (inj_lt 0 2).
apply (le_S 1 1).
apply (le_n 1).
auto.
intro n.
elim (proj2_sig (A n)).
intros x H2.
exists x.
apply H2.
Qed.

Lemma Archimedes_sub : Cv_CReal (fun (n : nat) => (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (m : nat) => 1 / (inject_Z (Z.of_nat n))) (natInverseCauchy n)))) CRealO.
Proof.
intros EPS.
elim (proj2_sig EPS).
intros eps H1.
unfold CRealLt at 1.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy) EPS eps).
simpl.
intros H2.
elim H2.
intros M H3.
elim (proj2 H3).
intros N H4.
exists ((Pos.to_nat (Qden M)) + (Pos.to_nat (Qden M)))%nat.
intros n H5.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) (CRealabs (CRealPlus (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n)))
        (CRealOpp CRealO))) (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n)) EPS eps).
simpl.
exists (Qmake 1 ((Qden M) + (Qden M))%positive).
apply conj.
unfold Qlt.
simpl.
apply (inj_lt 0 1).
apply (le_n 1).
exists N.
intros n0 H6.
simpl.
apply (Qle_trans (1 / inject_Z (Z.of_nat n) + (1 # Qden M + Qden M)) ((1 # Qden M + Qden M) + (1 # Qden M + Qden M)) (proj1_sig eps n0)).
apply (Qplus_le_l (1 / inject_Z (Z.of_nat n)) (1 # Qden M + Qden M) (1 # Qden M + Qden M)).
unfold inject_Z.
unfold Qdiv.
unfold Qinv.
unfold Qnum.
cut (exists (nm : nat), n = (S nm)).
intro H7.
elim H7.
intros nm H8.
rewrite H8.
simpl.
rewrite (Qmult_1_l (1 # Pos.of_succ_nat nm)).
unfold Qle.
simpl.
apply (Pos2Z.pos_le_pos (Qden M + Qden M) (Pos.of_succ_nat nm)).
apply (Pos2Nat.inj_le (Qden M + Qden M)%positive (Pos.of_succ_nat nm)).
rewrite (SuccNat2Pos.id_succ nm).
rewrite <- H8.
rewrite (Pos2Nat.inj_add (Qden M) (Qden M)).
apply H5.
cut (n <> O).
intro H7.
cut (forall (n : nat), (n <> O) -> exists nm, n = (S nm)).
intro H8.
apply (H8 n H7).
intros n1.
elim n1.
intro H8.
apply False_ind.
apply H8.
reflexivity.
intros n2 H8 H9.
exists n2.
reflexivity.
intro H7.
apply (lt_not_le 0 (Pos.to_nat (Qden M) + Pos.to_nat (Qden M))).
rewrite<- (Pos2Nat.inj_add (Qden M) (Qden M)).
apply (Pos2Nat.is_pos (Qden M + Qden M)).
rewrite<- H7.
apply H5.
cut ((1 # Qden M + Qden M) + (1 # Qden M + Qden M) == (1 # Qden M)).
intro H7.
rewrite H7.
apply (Qle_trans (1 # Qden M) M (proj1_sig eps n0)).
unfold Qle.
simpl.
rewrite<- (Z.mul_1_l (' Qden M)) at 1.
apply (Zmult_gt_0_le_compat_r 1 (Qnum M) (' Qden M)).
apply (Zlt_gt 0 (' Qden M)).
apply (Pos2Z.pos_is_pos (Qden M)).
apply (Zgt_le_succ 0 (Qnum M)).
apply (Zlt_gt 0 (Qnum M)).
rewrite<- (Z.mul_1_r (Qnum M)).
rewrite<- (Z.mul_0_l (' Qden M)).
apply (proj1 H3).
rewrite<- (Qplus_0_l M).
apply (H4 n0).
apply H6.
unfold Qplus.
unfold Qeq.
simpl.
rewrite (Pos2Z.inj_mul (Qden M + Qden M + (Qden M + Qden M)) (Qden M)).
rewrite (Pos2Z.inj_mul (Qden M + Qden M) (Qden M + Qden M)).
rewrite (Pos2Z.inj_add (Qden M + Qden M) (Qden M + Qden M)).
rewrite (Pos2Z.inj_add (Qden M) (Qden M)).
rewrite (Z.mul_add_distr_l (' Qden M + ' Qden M) (' Qden M) (' Qden M)).
rewrite (Z.mul_add_distr_r (' Qden M + ' Qden M) (' Qden M + ' Qden M) (' Qden M)).
reflexivity.
cut (In (T CauchySequenceEquivalenceRelation) (proj1_sig (CRealPlus (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n)))
           (CRealOpp CRealO))) (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n))).
intro H6.
rewrite (proj1 (CRealabsNature (CRealPlus (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n))) (CRealOpp CRealO)))).
apply H6.
unfold CRealLt.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation Prop ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> Prop => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) => (CauchySequenceQLt a1 a2))) CRealLtWellDefined) 
(CRealPlus (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n))) (CRealOpp CRealO)) (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n)) CRealO (exist Cauchy_Q (fun (n : nat) => 0) OCauchy)).
simpl.
intro H7.
elim H7.
intros MM H8.
elim (proj2 H8).
intros NN H9.
apply (Qlt_irrefl 0).
apply (Qlt_le_trans 0 (1 / inject_Z (Z.of_nat n) + MM) 0).
apply (Qlt_trans 0 (1 / inject_Z (Z.of_nat n)) (1 / inject_Z (Z.of_nat n) + MM)).
apply (Qlt_shift_div_l 0 1 (inject_Z (Z.of_nat n))).
cut (0 = inject_Z 0).
intro H10.
rewrite H10.
rewrite<- (Zlt_Qlt).
apply (inj_lt 0 n).
apply (le_trans 1 (Pos.to_nat (Qden M) + Pos.to_nat (Qden M)) n).
rewrite<- (Pos2Nat.inj_add (Qden M) (Qden M)).
apply (Pos2Nat.is_pos (Qden M + Qden M)).
apply H5.
auto.
rewrite (Qmult_0_l (inject_Z (Z.of_nat 1))).
cut (0 = inject_Z 0).
intro H10.
cut (1 = inject_Z 1).
intro H11.
rewrite H10.
rewrite H11.
rewrite<- (Zlt_Qlt).
apply (inj_lt 0 1).
apply (le_n 1).
auto.
auto.
rewrite<- (Qplus_0_r (1 / inject_Z (Z.of_nat n))) at 1.
apply (Qplus_lt_r 0 MM (1 / inject_Z (Z.of_nat n))).
apply (proj1 H8).
apply (H9 NN).
apply (le_n NN).
apply H6.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
simpl.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n))) (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n)) (CRealOpp CRealO) (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
simpl.
intros ep H6.
exists O.
intros n2 H7.
unfold CauchySequenceQPlus.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig.
rewrite (Qplus_0_r (1 / inject_Z (Z.of_nat n))).
rewrite (Qplus_opp_r (1 / inject_Z (Z.of_nat n))).
rewrite (Qplus_opp_r 0).
apply H6.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 1 / inject_Z (Z.of_nat n)) (natInverseCauchy n))).
unfold CRealOpp.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQOpp a)))) CRealOppWellDefined) CRealO (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
simpl.
intros ep H6.
exists O.
intros n2 H7.
unfold CauchySequenceQOpp.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig.
rewrite<- (Qplus_0_l (- 0)) at 1.
rewrite (Qplus_opp_r 0).
rewrite (Qplus_opp_r 0).
rewrite (Qplus_opp_r 0).
apply H6.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl eps).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 0) OCauchy)).
rewrite<- H1.
apply (CauchySequenceEquivalenceRefl eps).
Qed.

Fixpoint INR (n:nat) : CReal :=
match n with
| O => CRealO
| S n => (CRealPlus (INR n) CRealI)
end.

Fixpoint POW (r:CReal) (n:nat) : CReal :=
match n with
| O => CRealI
| S n => (CRealMult (POW r n) r)
end.

Lemma Archimedes : Cv_CReal (fun (n : nat) => (CRealInv (INR n))) CRealO.
Proof.
cut (forall (n : nat), (n > O)%nat -> (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun (m : nat) => 1 / (inject_Z (Z.of_nat n))) (natInverseCauchy n))) = CRealInv (INR n)).
intro H1.
intros eps H2.
elim (Archimedes_sub eps H2).
intros N H3.
exists (S N).
intros n H4.
rewrite<- (H1 n).
apply (H3 n).
apply (le_S_n N n).
apply (le_S (S N) n).
apply H4.
apply (le_trans (S O) (S N) n).
apply (le_n_S O N).
apply (le_0_n N).
apply H4.
cut (forall (n : nat), Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n))).
intro H1.
cut (forall (n : nat), ToEquivalenceClass CauchySequenceEquivalenceRelation
  (exist Cauchy_Q
     (fun _ : nat => inject_Z (Z.of_nat n))
     (H1 n)) = (INR n)).
intro H2.
intros n H3.
rewrite<- (H2 n).
unfold CRealInv.
rewrite (ToEquivalenceFunctionNature CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CReal => forall (a b : CauchySequenceQSet), (CauchySequenceEquivalence a b) -> (g a) = (g b)) (fun (a : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQInv a)))) CRealInvWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n)) (H1 n))) (exist Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n)) (H1 n))).
simpl.
apply sig_map.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H4.
exists O.
intros n0 H5.
unfold CauchySequenceQInv.
unfold proj1_sig.
unfold SequenceQPlus.
unfold SequenceQOpp.
cut (~ Cv_Q (fun _ : nat => inject_Z (Z.of_nat n)) 0).
intro H6.
rewrite (proj2 (SequenceQInvAltNature (fun _ : nat => inject_Z (Z.of_nat n))) H6 n0).
rewrite (Qmult_1_l (/ inject_Z (Z.of_nat n))).
rewrite (Qplus_opp_r (/ inject_Z (Z.of_nat n))).
rewrite (Qplus_opp_r 0).
apply H4.
intro H6.
elim (H6 1).
intros n1 H7.
apply (Qlt_not_le (Qabs (0 - inject_Z (Z.of_nat n))) 1).
apply (H7 n1).
apply (le_n n1).
rewrite (Qplus_0_l (- inject_Z (Z.of_nat n))).
rewrite (Qabs_opp (inject_Z (Z.of_nat n))).
apply (Qle_trans 1 (inject_Z (Z.of_nat n)) (Qabs (inject_Z (Z.of_nat n)))).
cut (1 = inject_Z (Z.of_nat (S O))).
intro H8.
rewrite H8.
rewrite<- Zle_Qle.
apply (inj_le 1 n).
apply H3.
auto.
apply (Qle_Qabs (inject_Z (Z.of_nat n))).
unfold Qlt.
simpl.
apply (inj_lt 0 1).
apply (le_n 1).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n)) (H1 n))).
intros n.
elim n.
simpl.
unfold CRealO.
apply sig_map.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H2.
exists O.
intros n0 H3.
unfold proj1_sig.
unfold SequenceQPlus.
unfold SequenceQOpp.
simpl.
apply H2.
intros n0 H3.
simpl.
rewrite<- H3.
unfold CRealPlus.
rewrite (ToEquivalenceFunctionBinaryNature CauchySequenceEquivalenceRelation CauchySequenceEquivalenceRelation CReal ((exist (fun g : CauchySequenceQSet -> CauchySequenceQSet -> CReal => forall (a1 b1 : CauchySequenceQSet) (a2 b2 : CauchySequenceQSet), (CauchySequenceEquivalence a1 b1) -> (CauchySequenceEquivalence a2 b2) -> (g a1 a2) = (g b1 b2)) (fun (a1 a2 : CauchySequenceQSet) =>  (ToEquivalenceClass CauchySequenceEquivalenceRelation (CauchySequenceQPlus a1 a2)))) CRealPlusWellDefined) (ToEquivalenceClass CauchySequenceEquivalenceRelation (exist Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n0)) (H1 n0))) (exist Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n0)) (H1 n0)) CRealI (exist Cauchy_Q (fun (n : nat) => 1) ICauchy)).
simpl.
apply sig_map.
apply (EquivalenceSame CauchySequenceEquivalenceRelation).
intros eps H4.
exists O.
intros n1 H5.
unfold CauchySequenceQPlus.
unfold SequenceQPlus.
unfold SequenceQOpp.
unfold proj1_sig.
cut ((inject_Z (' Pos.of_succ_nat n0) + - (inject_Z (Z.of_nat n0) + 1)) == 0).
intro H6.
rewrite H6.
rewrite (Qplus_opp_r 0).
apply H4.
cut (1 = inject_Z (Z.of_nat (S O))).
intro H6.
rewrite H6.
rewrite<- (inject_Z_plus (Z.of_nat n0) (Z.of_nat 1)).
cut (inject_Z (' Pos.of_succ_nat n0) == inject_Z (Z.of_nat n0 + Z.of_nat 1)).
intro H7.
rewrite H7.
apply (Qplus_opp_r (inject_Z (Z.of_nat n0 + Z.of_nat 1))).
rewrite<- (Nat2Z.inj_add n0 1).
auto.
cut ((n0 + 1)%nat = S n0).
intro H7.
rewrite H7.
simpl.
reflexivity.
rewrite<- (plus_Snm_nSm n0 O).
auto.
auto.
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => inject_Z (Z.of_nat n0)) (H1 n0))).
apply (CauchySequenceEquivalenceRefl (exist Cauchy_Q (fun _ : nat => 1) ICauchy)).
intros n eps H1.
exists O.
intros m k H2 H3.
rewrite (Qplus_opp_r (inject_Z (Z.of_nat n))).
simpl.
apply H1.
Qed.

Lemma CRopp_O : (CRealOpp CRealO) = CRealO.
Proof.
rewrite<- (CRplus_O_l (CRealOpp CRealO)).
apply (CRplus_opp_r CRealO).
Qed.

Lemma CRopp_involutive : forall (r : CReal), (CRealOpp (CRealOpp r)) = r.
Proof.
intros r.
rewrite<- (CRplus_O_l r) at 2.
rewrite<- (CRplus_opp_r (CRealOpp r)).
rewrite (CRplus_comm (CRealOpp r) (CRealOpp (CRealOpp r))).
rewrite (CRplus_assoc (CRealOpp (CRealOpp r)) (CRealOpp r) r).
rewrite (CRplus_comm (CRealOpp r) r).
rewrite (CRplus_opp_r r).
rewrite (CRplus_comm (CRealOpp (CRealOpp r)) CRealO).
rewrite (CRplus_O_l (CRealOpp (CRealOpp r))).
reflexivity.
Qed.

Lemma CRopp_lt_contravar : forall (r1 r2 : CReal), (CRealLt r2 r1) -> (CRealLt (CRealOpp r1) (CRealOpp r2)).
Proof.
intros r1 r2 H1.
rewrite<- (CRplus_O_l (CRealOpp r1)).
rewrite<- (CRplus_O_l (CRealOpp r2)).
rewrite<- (CRplus_opp_r (CRealOpp r1)).
rewrite (CRplus_assoc (CRealOpp r1) (CRealOpp (CRealOpp r1)) (CRealOpp r1)).
rewrite (CRplus_assoc (CRealOpp r1) (CRealOpp (CRealOpp r1)) (CRealOpp r2)).
apply (CRplus_lt_compat_l (CRealOpp r1) (CRealPlus (CRealOpp (CRealOpp r1)) (CRealOpp r1)) (CRealPlus (CRealOpp (CRealOpp r1)) (CRealOpp r2))).
rewrite (CRplus_comm (CRealOpp (CRealOpp r1)) (CRealOpp r1)).
rewrite (CRplus_opp_r (CRealOpp r1)).
rewrite (CRplus_comm (CRealOpp (CRealOpp r1)) (CRealOpp r2)).
rewrite (CRopp_involutive r1).
rewrite<- (CRplus_opp_r r2).
rewrite (CRplus_comm r2 (CRealOpp r2)).
apply (CRplus_lt_compat_l (CRealOpp r2) r2 r1).
apply H1.
Qed.

Lemma CRabs_def1 : forall (x a : CReal),(CRealLt x a) -> (CRealLt (CRealOpp a) x) -> (CRealLt (CRealabs x) a).
Proof.
intros x a H1 H2.
elim (classic (CRealLt x CRealO)).
intro H3.
rewrite (proj2 (CRealabsNature x) H3).
rewrite<- (CRopp_involutive a).
apply (CRopp_lt_contravar x (CRealOpp a)).
apply H2.
intro H3.
rewrite (proj1 (CRealabsNature x) H3).
apply H1.
Qed.

Lemma CRabs_def2 : forall (x a : CReal),(CRealLt (CRealabs x) a) -> (CRealLt x a) /\ (CRealLt (CRealOpp a) x).
Proof.
intros x a H1.
apply conj.
elim (classic (CRealLt x CRealO)).
intro H2.
rewrite (proj2 (CRealabsNature x) H2) in H1.
apply (CRlt_trans x CRealO a).
apply H2.
apply (CRlt_trans CRealO (CRealOpp x) a).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealO x).
apply H2.
apply H1.
intro H2.
rewrite (proj1 (CRealabsNature x) H2) in H1.
apply H1.
elim (classic (CRealLt x CRealO)).
intro H2.
rewrite (proj2 (CRealabsNature x) H2) in H1.
rewrite<- (CRopp_involutive x).
apply (CRopp_lt_contravar a (CRealOpp x)).
apply H1.
intro H2.
rewrite (proj1 (CRealabsNature x) H2) in H1.
elim (CRtotal_order x CRealO).
intro H3.
apply False_ind.
apply (H2 H3).
intro H3.
elim H3.
intro H4.
rewrite H4.
rewrite H4 in H1.
rewrite<- (CRopp_involutive CRealO).
apply (CRopp_lt_contravar a (CRealOpp CRealO)).
rewrite CRopp_O.
apply H1.
intro H4.
apply (CRlt_trans (CRealOpp a) CRealO x).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar a CRealO).
apply (CRlt_trans CRealO x a).
apply H4.
apply H1.
apply H4.
Qed.

Lemma CRplus_O_r_uniq : forall (r r1 : CReal), (CRealPlus r r1) = r -> r1 = CRealO.
Proof.
intros r r1 H1.
rewrite<- (CRplus_O_l r1).
rewrite<- (CRplus_opp_r r) at 1.
rewrite (CRplus_comm r (CRealOpp r)).
rewrite (CRplus_assoc (CRealOpp r) r r1).
rewrite H1.
rewrite (CRplus_comm (CRealOpp r) r).
apply (CRplus_opp_r r).
Qed.

Lemma CRmult_O_r : forall (r : CReal), (CRealMult r CRealO) = CRealO.
Proof.
intros r.
apply (CRplus_O_r_uniq (CRealMult r CRealO) (CRealMult r CRealO)).
rewrite<- (CRmult_plus_distr_l r CRealO CRealO).
rewrite (CRplus_O_l CRealO).
reflexivity.
Qed.

Lemma CRopp_mult_distr_l : forall (r1 r2 : CReal), (CRealOpp (CRealMult r1 r2)) = (CRealMult (CRealOpp r1) r2).
Proof.
intros r1 r2.
rewrite<- (CRplus_O_l (CRealMult (CRealOpp r1) r2)).
rewrite<- (CRplus_opp_r (CRealMult r1 r2)).
rewrite (CRplus_comm (CRealMult r1 r2) (CRealOpp (CRealMult r1 r2))).
rewrite (CRplus_assoc (CRealOpp (CRealMult r1 r2)) (CRealMult r1 r2) (CRealMult (CRealOpp r1) r2)).
rewrite (CRmult_comm r1 r2).
rewrite (CRmult_comm (CRealOpp r1) r2).
rewrite<- (CRmult_plus_distr_l r2 r1 (CRealOpp r1)).
rewrite (CRplus_opp_r r1).
rewrite (CRmult_O_r r2).
rewrite (CRplus_comm (CRealOpp (CRealMult r2 r1)) CRealO).
rewrite (CRplus_O_l (CRealOpp (CRealMult r2 r1))).
reflexivity.
Qed.


Lemma CRlt_O_I : CRealLt CRealO CRealI.
Proof.
elim (CRtotal_order CRealO CRealI).
intro H1.
apply H1.
intro H1.
elim H1.
intro H2.
apply False_ind.
apply CReal_I_neq_O.
rewrite H2.
reflexivity.
intro H2.
cut (forall (r : CReal), (CRealLt CRealO r) -> (CRealLt CRealO (CRealMult r r))).
intro H3.
rewrite<- (CRopp_involutive CRealI).
rewrite<- (CRmult_I_l CRealI).
rewrite (CRopp_mult_distr_l CRealI CRealI).
rewrite (CRmult_comm (CRealOpp CRealI) CRealI).
rewrite (CRopp_mult_distr_l CRealI (CRealOpp CRealI)).
apply (H3 (CRealOpp CRealI)).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealO CRealI).
apply H2.
intros r H3.
rewrite<- (CRmult_O_r r).
apply (CRmult_lt_compat_l r CRealO r).
apply H3.
apply H3.
Qed.

Lemma CRinv_O_lt_compat : forall (r : CReal), (CRealLt CRealO r) -> (CRealLt CRealO (CRealInv r)).
Proof.
intros r H1.
elim (CRtotal_order CRealO (CRealInv r)).
intro H2.
apply H2.
intro H2.
elim H2.
intro H3.
apply False_ind.
cut (CRealLt CRealO CRealO).
intro H4.
apply (CRlt_asym CRealO CRealO).
apply H4.
apply H4.
rewrite<- (CRmult_O_r r) at 2.
rewrite H3 at 2.
rewrite (CRmult_comm r (CRealInv r)).
rewrite (CRinv_l r).
apply CRlt_O_I.
intro H4.
rewrite H4 in H1.
apply (CRlt_asym CRealO CRealO).
apply H1.
apply H1.
intro H3.
apply False_ind.
apply (CRlt_asym CRealO CRealI).
apply CRlt_O_I.
rewrite<- (CRinv_l r).
rewrite (CRmult_comm (CRealInv r) r).
rewrite<- (CRmult_O_r r).
apply (CRmult_lt_compat_l r (CRealInv r) CRealO).
apply H1.
apply H3.
intro H4.
rewrite H4 in H1.
apply (CRlt_asym CRealO CRealO).
apply H1.
apply H1.
Qed.

Lemma CRinv_lt_contravar : forall (r1 r2 : CReal), (CRealLt CRealO r1) -> (CRealLt r1 r2) -> (CRealLt (CRealInv r2) (CRealInv r1)).
Proof.
intros r1 r2 H1 H2.
rewrite<- (CRmult_I_l (CRealInv r2)).
rewrite (CRmult_comm CRealI (CRealInv r2)).
rewrite<- (CRmult_I_l (CRealInv r1)).
rewrite (CRmult_comm CRealI (CRealInv r1)).
rewrite<- (CRinv_l r1) at 1.
rewrite<- (CRinv_l r2).
rewrite<- (CRmult_assoc (CRealInv r2) (CRealInv r1) r1).
rewrite<- (CRmult_assoc (CRealInv r1) (CRealInv r2) r2).
rewrite (CRmult_comm (CRealInv r2) (CRealInv r1)).
apply (CRmult_lt_compat_l (CRealMult (CRealInv r1) (CRealInv r2)) r1 r2).
rewrite<- (CRmult_O_r (CRealInv r1)).
apply (CRmult_lt_compat_l (CRealInv r1) CRealO (CRealInv r2)).
apply (CRinv_O_lt_compat r1 H1).
apply (CRinv_O_lt_compat r2).
apply (CRlt_trans CRealO r1 r2).
apply H1.
apply H2.
apply H2.
intro H3.
cut (CRealLt CRealO r2).
intro H4.
rewrite H3 in H4.
apply (CRlt_asym CRealO CRealO).
apply H4.
apply H4.
apply (CRlt_trans CRealO r1 r2).
apply H1.
apply H2.
intro H3.
rewrite H3 in H1.
apply (CRlt_asym CRealO CRealO).
apply H1.
apply H1.
Qed.

Lemma CRplus_opp_r_uniq : forall (r1 r2 : CReal), (CRealPlus r1 r2) = CRealO -> r2 = CRealOpp r1.
Proof.
intros r1 r2 H1.
cut (CRealPlus (CRealOpp r1) (CRealPlus r1 r2) = CRealPlus (CRealOpp r1) CRealO).
intro H2.
rewrite<- (CRplus_O_l r2).
rewrite<- (CRplus_opp_r r1).
rewrite (CRplus_comm r1 (CRealOpp r1)).
rewrite (CRplus_assoc (CRealOpp r1) r1 r2).
rewrite H2.
rewrite (CRplus_comm (CRealOpp r1) CRealO).
apply (CRplus_O_l (CRealOpp r1)).
rewrite H1.
reflexivity.
Qed.

Lemma INR_Lt_POW2 : forall (n : nat), (CRealLt (INR n) (POW (CRealPlus CRealI CRealI) n)).
cut (forall n : nat, CRealLt CRealI (POW (CRealPlus CRealI CRealI) n) \/ CRealI = (POW (CRealPlus CRealI CRealI) n)).
intro H1.
intro n.
elim n.
simpl.
apply CRlt_O_I.
intros n0 H2.
simpl.
elim (H1 n0).
intro H3.
apply (CRlt_trans (CRealPlus (INR n0) CRealI) (CRealPlus (POW (CRealPlus CRealI CRealI) n0) CRealI) (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))).
rewrite (CRplus_comm (INR n0) CRealI).
rewrite (CRplus_comm (POW (CRealPlus CRealI CRealI) n0) CRealI).
apply (CRplus_lt_compat_l CRealI (INR n0) (POW (CRealPlus CRealI CRealI) n0)).
apply H2.
rewrite (CRmult_plus_distr_l (POW (CRealPlus CRealI CRealI) n0) CRealI CRealI).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) CRealI).
rewrite (CRmult_I_l (POW (CRealPlus CRealI CRealI) n0)).
apply (CRplus_lt_compat_l (POW (CRealPlus CRealI CRealI) n0) CRealI (POW (CRealPlus CRealI CRealI) n0)).
apply H3.
intro H3.
rewrite H3 at 1.
rewrite (CRplus_comm (INR n0) (POW (CRealPlus CRealI CRealI) n0)).
rewrite (CRmult_plus_distr_l (POW (CRealPlus CRealI CRealI) n0) CRealI CRealI).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) CRealI).
rewrite (CRmult_I_l (POW (CRealPlus CRealI CRealI) n0)).
apply (CRplus_lt_compat_l (POW (CRealPlus CRealI CRealI) n0) (INR n0) (POW (CRealPlus CRealI CRealI) n0)).
apply H2.
intro n.
elim n.
right.
simpl.
reflexivity.
intros n0 H1.
simpl.
left.
rewrite (CRmult_plus_distr_l (POW (CRealPlus CRealI CRealI) n0) CRealI CRealI).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) CRealI).
rewrite (CRmult_I_l (POW (CRealPlus CRealI CRealI) n0)).
elim H1.
intro H2.
apply (CRlt_trans CRealI (POW (CRealPlus CRealI CRealI) n0) (CRealPlus (POW (CRealPlus CRealI CRealI) n0) (POW (CRealPlus CRealI CRealI) n0))).
apply H2.
rewrite<- (CRplus_O_l (POW (CRealPlus CRealI CRealI) n0)) at 1.
rewrite (CRplus_comm CRealO (POW (CRealPlus CRealI CRealI) n0)).
apply (CRplus_lt_compat_l (POW (CRealPlus CRealI CRealI) n0) CRealO (POW (CRealPlus CRealI CRealI) n0)).
apply (CRlt_trans CRealO CRealI (POW (CRealPlus CRealI CRealI) n0)).
apply CRlt_O_I.
apply H2.
intro H2.
rewrite H2 at 1.
rewrite<- (CRplus_O_l (POW (CRealPlus CRealI CRealI) n0)) at 1.
rewrite (CRplus_comm CRealO (POW (CRealPlus CRealI CRealI) n0)).
apply (CRplus_lt_compat_l (POW (CRealPlus CRealI CRealI) n0) CRealO (POW (CRealPlus CRealI CRealI) n0)).
rewrite<- H2.
apply CRlt_O_I.
Qed.

Lemma SqueezeTheorem : forall (a b c : nat -> CReal) (x : CReal), (Cv_CReal a x) -> (Cv_CReal c x) -> (exists (N : nat), forall (n : nat), (n >= N)%nat -> (CRealLt (a n) (b n)) /\ (CRealLt (b n) (c n))) -> (Cv_CReal b x).
Proof.
intros a b c x H1 H2 H3.
intros eps H4.
elim (H1 eps H4).
intros N1 H5.
elim (H2 eps H4).
intros N2 H6.
elim H3.
intros N3 H7.
exists (max (max N1 N2) N3).
intros n H8.
apply (CRabs_def1 (CRealPlus (b n) (CRealOpp x)) eps).
apply (CRlt_trans (CRealPlus (b n) (CRealOpp x)) (CRealPlus (c n) (CRealOpp x)) eps).
rewrite (CRplus_comm (b n) (CRealOpp x)).
rewrite (CRplus_comm (c n) (CRealOpp x)).
apply (CRplus_lt_compat_l (CRealOpp x) (b n) (c n)).
apply (H7 n).
apply (le_trans N3 (max (max N1 N2) N3) n).
apply (Nat.le_max_r (max N1 N2) N3).
apply H8.
apply (CRabs_def2 (CRealPlus (c n) (CRealOpp x)) eps).
apply (H6 n).
apply (le_trans N2 (max (max N1 N2) N3) n).
apply (le_trans N2 (max N1 N2) (max (max N1 N2) N3)).
apply (Nat.le_max_r N1 N2).
apply (Nat.le_max_l (max N1 N2) N3).
apply H8.
apply (CRlt_trans (CRealOpp eps) (CRealPlus (a n) (CRealOpp x)) (CRealPlus (b n) (CRealOpp x))).
apply (CRabs_def2 (CRealPlus (a n) (CRealOpp x)) eps).
apply (H5 n).
apply (le_trans N1 (max (max N1 N2) N3) n).
apply (le_trans N1 (max N1 N2) (max (max N1 N2) N3)).
apply (Nat.le_max_l N1 N2).
apply (Nat.le_max_l (max N1 N2) N3).
apply H8.
rewrite (CRplus_comm (a n) (CRealOpp x)).
rewrite (CRplus_comm (b n) (CRealOpp x)).
apply (CRplus_lt_compat_l (CRealOpp x) (a n) (b n)).
apply (H7 n).
apply (le_trans N3 (max (max N1 N2) N3) n).
apply (Nat.le_max_r (max N1 N2) N3).
apply H8.
Qed.

Lemma Archimedes2 : Cv_CReal (fun (n : nat) => (CRealInv (POW (CRealPlus CRealI CRealI) n))) CRealO.
Proof.
apply (SqueezeTheorem (fun n : nat => CRealO) (fun n : nat => CRealInv (POW (CRealPlus CRealI CRealI) n)) (fun (n : nat) => (CRealInv (INR n))) CRealO).
intros eps H1.
exists O.
intros n H2.
rewrite (CRplus_opp_r CRealO).
rewrite (proj1 (CRealabsNature CRealO)).
apply H1.
intro H3.
apply (CRlt_asym CRealO CRealO).
apply H3.
apply H3.
apply Archimedes.
exists (S O).
intro n.
elim n.
intro H1.
apply False_ind.
apply (le_not_lt (S O) O).
apply H1.
apply (le_n (S O)).
intros n0 H1 H2.
cut (forall (n1 : nat),CRealLt CRealO (INR (S n1))).
intro H3.
apply conj.
apply (CRinv_O_lt_compat (POW (CRealPlus CRealI CRealI) (S n0))).
apply (CRlt_trans CRealO (INR (S n0)) (POW (CRealPlus CRealI CRealI) (S n0))).
apply (H3 n0).
apply (INR_Lt_POW2 (S n0)).
apply (CRinv_lt_contravar (INR (S n0)) (POW (CRealPlus CRealI CRealI) (S n0))).
apply (H3 n0).
apply (INR_Lt_POW2 (S n0)).
intro n1.
elim n1.
simpl.
rewrite (CRplus_O_l CRealI).
apply CRlt_O_I.
intros n2 H3.
apply (CRlt_trans CRealO (INR (S n2)) (INR (S (S n2)))).
apply H3.
rewrite<- (CRplus_O_l (INR (S n2))).
rewrite (CRplus_comm CRealO (INR (S n2))).
apply (CRplus_lt_compat_l (INR (S n2)) CRealO CRealI).
apply CRlt_O_I.
Qed.

Lemma CRealcompleteness : forall (E : CReal -> Prop), (exists (m : CReal), forall (x : CReal), E x -> (CRealLt x m) \/ x = m) -> (exists x : CReal, E x) -> { m : CReal | (forall (x : CReal), E x -> (CRealLt x m) \/ x = m) /\ (forall (b : CReal), (forall x : CReal, E x -> (CRealLt x b) \/ x = b) -> ((CRealLt m b) \/ m = b))}.
Proof.
intros E H1 H2.
apply constructive_definite_description.
cut (forall (z : (CReal * CReal)), {y : (CReal * CReal) | 
((forall x : CReal, E x -> CRealLt x (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) \/ x = (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)))) -> y = (fst z,(CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)))))
 /\ ((~ forall x : CReal, E x -> CRealLt x (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) \/ x = (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)))) -> y = ((CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))),snd z))}).
intro H3.
elim H1.
intros b0 H4.
elim H2.
intros a0 H5.
cut (let abn := (fix f (n : nat) : (CReal * CReal) := 
match n with 
  | O => (CRealPlus a0 (CRealOpp CRealI), b0)
  | S n0 => (proj1_sig (H3 (f n0)))
end) in exists ! x : CReal,
  (forall x0 : CReal, E x0 -> CRealLt x0 x \/ x0 = x) /\
  (forall b : CReal,
   (forall x0 : CReal, E x0 -> CRealLt x0 b \/ x0 = b) ->
   CRealLt x b \/ x = b)).
intro H6.
apply H6.
intro abn.
cut (let an := fun (n : nat) => (fst (abn n)) in exists ! x : CReal,
  (forall x0 : CReal, E x0 -> CRealLt x0 x \/ x0 = x) /\
  (forall b : CReal,
   (forall x0 : CReal, E x0 -> CRealLt x0 b \/ x0 = b) ->
   CRealLt x b \/ x = b)).
intro H6.
apply H6.
intro an.
cut (let bn := fun (n : nat) => (snd (abn n)) in exists ! x : CReal,
  (forall x0 : CReal, E x0 -> CRealLt x0 x \/ x0 = x) /\
  (forall b : CReal,
   (forall x0 : CReal, E x0 -> CRealLt x0 b \/ x0 = b) ->
   CRealLt x b \/ x = b)).
intro H6.
apply H6.
intro bn.
cut (exists (a : CReal), (Cv_CReal an a) /\ (Cv_CReal bn a)).
intro H6.
apply (unique_existence (fun (x : CReal) => (forall x0 : CReal, E x0 -> CRealLt x0 x \/ x0 = x) /\
  (forall b : CReal,
   (forall x0 : CReal, E x0 -> CRealLt x0 b \/ x0 = b) ->
   CRealLt x b \/ x = b))).
apply conj.
elim H6.
intros a H7.
exists a.
apply conj.
intros x H8.
elim (CRtotal_order x a).
intro H9.
left.
apply H9.
intro H9.
elim H9.
intro H10.
right.
apply H10.
intro H10.
apply False_ind.
cut (forall (n : nat),forall x : CReal, E x -> CRealLt x (bn n) \/ x = (bn n)).
intro H11.
elim (proj2 H7 (CRealPlus x (CRealOpp a))).
intros N H12.
cut (CRealLt (bn N) x).
elim (H11 N x H8).
apply (CRlt_asym x (bn N)).
intro H13.
rewrite H13.
intro H14.
apply (CRlt_asym (bn N) (bn N) H14 H14).
rewrite<- (CRplus_O_l (bn N)).
rewrite<- (CRplus_O_l x).
rewrite<- (CRplus_opp_r a).
rewrite (CRplus_assoc a (CRealOpp a) (bn N)).
rewrite (CRplus_assoc a (CRealOpp a) x).
apply (CRplus_lt_compat_l a (CRealPlus (CRealOpp a) (bn N)) (CRealPlus (CRealOpp a) x)).
rewrite (CRplus_comm (CRealOpp a) (bn N)).
rewrite (CRplus_comm (CRealOpp a) x).
apply (CRabs_def2 (CRealPlus (bn N) (CRealOpp a)) (CRealPlus x (CRealOpp a))).
apply (H12 N).
apply (le_n N).
rewrite<- (CRplus_opp_r a).
rewrite (CRplus_comm a (CRealOpp a)).
rewrite (CRplus_comm x (CRealOpp a)).
apply (CRplus_lt_compat_l (CRealOpp a) a x).
apply H10.
intro n.
elim n.
apply H4.
intros n0 H11.
elim (classic (forall x : CReal,
       E x ->
       CRealLt x
         (CRealMult (CRealPlus (an n0) (bn n0))
            (CRealInv (CRealPlus CRealI CRealI))) \/
       x =
       CRealMult (CRealPlus (an n0) (bn n0))
         (CRealInv (CRealPlus CRealI CRealI)))).
intro H12.
unfold bn.
simpl.
rewrite (proj1 (proj2_sig (H3 (abn n0)))).
apply H12.
apply H12.
intro H12.
unfold bn.
simpl.
rewrite (proj2 (proj2_sig (H3 (abn n0)))).
unfold snd at 1.
unfold snd at 2.
apply H11.
apply H12.
intros x H8.
elim (CRtotal_order a x).
intro H9.
left.
apply H9.
intro H9.
elim H9.
intro H10.
right.
apply H10.
intro H10.
apply False_ind.
cut (forall (n : nat),~forall x : CReal, E x -> CRealLt x (an n) \/ x = (an n)).
intro H11.
elim (proj1 H7 (CRealPlus a (CRealOpp x))).
intros N H12.
apply (H11 N).
intros y H13.
left.
cut (CRealLt x (an N)).
intro H14.
elim (H8 y H13).
intro H15.
apply (CRlt_trans y x (an N)).
apply H15.
apply H14.
intro H15.
rewrite H15.
apply H14.
rewrite<- (CRplus_O_l x).
rewrite<- (CRplus_O_l (an N)).
rewrite<- (CRplus_opp_r a).
rewrite (CRplus_assoc a (CRealOpp a) x).
rewrite (CRplus_assoc a (CRealOpp a) (an N)).
apply (CRplus_lt_compat_l a (CRealPlus (CRealOpp a) x) (CRealPlus (CRealOpp a) (an N))).
rewrite (CRplus_comm (CRealOpp a) (an N)).
cut ((CRealPlus (CRealOpp a) x) = (CRealOpp (CRealPlus a (CRealOpp x)))).
intro H14.
rewrite H14.
apply (CRabs_def2 (CRealPlus (an N) (CRealOpp a)) (CRealPlus a (CRealOpp x))).
apply (H12 N).
apply (le_n N).
apply (CRplus_opp_r_uniq (CRealPlus a (CRealOpp x)) (CRealPlus (CRealOpp a) x)).
rewrite<- (CRplus_assoc (CRealPlus a (CRealOpp x)) (CRealOpp a) x).
rewrite (CRplus_assoc a (CRealOpp x) (CRealOpp a)).
rewrite (CRplus_comm (CRealOpp x) (CRealOpp a)).
rewrite<- (CRplus_assoc a (CRealOpp a) (CRealOpp x)).
rewrite (CRplus_opp_r a).
rewrite (CRplus_O_l (CRealOpp x)).
rewrite (CRplus_comm (CRealOpp x) x).
apply (CRplus_opp_r x).
rewrite<- (CRplus_opp_r x).
rewrite (CRplus_comm x (CRealOpp x)).
rewrite (CRplus_comm a (CRealOpp x)).
apply (CRplus_lt_compat_l (CRealOpp x) x a).
apply H10.
intro n.
elim n.
intro H11.
elim (CRtotal_order a0 (an O)).
apply (CRlt_asym (an O) a0).
unfold an.
unfold abn.
unfold fst.
rewrite<- (CRplus_O_l a0).
rewrite (CRplus_comm CRealO a0).
rewrite (CRplus_assoc a0 CRealO (CRealOpp CRealI)).
apply (CRplus_lt_compat_l a0 (CRealPlus CRealO (CRealOpp CRealI)) CRealO).
rewrite (CRplus_O_l (CRealOpp  CRealI)).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealI CRealO).
apply CRlt_O_I.
intro H12.
elim H12.
intro H13.
apply CReal_I_neq_O.
cut (CRealO = CRealI).
intro H14.
rewrite H14.
reflexivity.
cut (CRealOpp CRealO = CRealOpp CRealI).
intro H14.
rewrite<- (CRopp_involutive CRealO).
rewrite<- (CRopp_involutive CRealI).
rewrite H14.
reflexivity.
rewrite CRopp_O.
rewrite<- (CRplus_O_l (CRealOpp CRealI)).
rewrite<- (CRplus_opp_r a0).
rewrite (CRplus_comm a0 (CRealOpp a0)).
rewrite H13 at 2.
rewrite (CRplus_assoc (CRealOpp a0) a0 (CRealOpp CRealI)).
reflexivity.
intro H13.
elim (H11 a0 H5).
apply (CRlt_asym (an O) a0).
apply H13.
intro H14.
rewrite H14 in H13.
apply (CRlt_asym (an O) (an O)).
apply H13.
apply H13.
intros n0 H11.
elim (classic (forall x : CReal,
       E x ->
       CRealLt x
         (CRealMult (CRealPlus (an n0) (bn n0))
            (CRealInv (CRealPlus CRealI CRealI))) \/
       x =
       CRealMult (CRealPlus (an n0) (bn n0))
         (CRealInv (CRealPlus CRealI CRealI)))).
intro H12.
unfold an.
simpl.
rewrite (proj1 (proj2_sig (H3 (abn n0)))).
unfold fst at 1.
unfold fst at 2.
apply H11.
apply H12.
intro H12.
unfold an.
simpl.
rewrite (proj2 (proj2_sig (H3 (abn n0)))).
apply H12.
apply H12.
intros x y H7 H8.
cut (CRealLt x y \/ x = y).
intro H9.
cut (CRealLt y x \/ y = x).
intro H10.
elim H9.
intro H11.
apply False_ind.
elim H10.
intro H12.
apply (CRlt_asym x y H11 H12).
intro H12.
rewrite H12 in H11.
apply (CRlt_asym x x H11 H11).
intro H11.
apply H11.
apply (proj2 H8 x).
apply (proj1 H7).
apply (proj2 H7 y).
apply (proj1 H8).
cut (forall (n : nat),CRealPlus (bn n) (CRealOpp (an n)) = CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (POW (CRealPlus CRealI CRealI) n))).
intro H6.
cut (Cv_CReal (fun (n : nat) => CRealPlus (bn n) (CRealOpp (an n))) CRealO).
intro H8.
cut (forall (n : nat), CRealLt (an n) (bn n)).
intro H9.
cut (forall (n m : nat), (n <= m)%nat -> (CRealLt (bn m) (bn n) \/ (bn m) = (bn n)) /\ (CRealLt (an n) (an m) \/ (an n) = (an m))).
intro H7.
elim (Cauchy_Cv_CReal an).
intros a H10.
exists a.
apply conj.
apply H10.
intros eps H11.
cut (CRealLt CRealO (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
intro H12.
cut (eps = CRealPlus (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
intro H13.
elim (H10 (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) H12).
intros N1 H14.
elim (H8 (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) H12).
intros N2 H15.
exists (max N1 N2).
intros n H16.
apply (CRabs_def1 (CRealPlus (bn n) (CRealOpp a)) eps).
apply (CRlt_trans (CRealPlus (bn n) (CRealOpp a)) (CRealPlus (CRealPlus (bn n) (CRealOpp (an n))) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) eps).
rewrite<- (CRplus_O_l (CRealOpp a)) at 1.
rewrite<- (CRplus_opp_r (an n)).
rewrite (CRplus_comm (an n) (CRealOpp (an n))).
rewrite (CRplus_assoc (CRealOpp (an n)) (an n) (CRealOpp a)).
rewrite<- (CRplus_assoc (bn n) (CRealOpp (an n)) (CRealPlus (an n) (CRealOpp a))).
apply (CRplus_lt_compat_l (CRealPlus (bn n) (CRealOpp (an n))) (CRealPlus (an n) (CRealOpp a)) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
apply (CRabs_def2 (CRealPlus (an n) (CRealOpp a)) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
apply (H14 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H16.
rewrite (CRplus_comm (CRealPlus (bn n) (CRealOpp (an n))) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
rewrite H13 at 2.
apply (CRplus_lt_compat_l (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) (CRealPlus (bn n) (CRealOpp (an n))) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
rewrite<- (CRplus_O_l (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite (CRplus_comm CRealO (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite<- CRopp_O.
apply (CRabs_def2 (CRealPlus (CRealPlus (bn n) (CRealOpp (an n))) (CRealOpp CRealO)) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
apply (H15 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H16.
cut ((CRealOpp eps) = CRealPlus (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))))).
intro H17.
apply (CRlt_trans (CRealOpp eps) (CRealPlus (CRealPlus (bn n) (CRealOpp (an n))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))))) (CRealPlus (bn n) (CRealOpp a))).
rewrite H17.
rewrite (CRplus_comm (CRealPlus (bn n) (CRealOpp (an n))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))))).
apply (CRplus_lt_compat_l (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite<- (CRplus_O_l (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite (CRplus_comm CRealO (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite<- CRopp_O.
apply (CRabs_def2 (CRealPlus (CRealPlus (bn n) (CRealOpp (an n))) (CRealOpp CRealO)) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
apply (H15 n).
apply (le_trans N2 (max N1 N2) n).
apply (Nat.le_max_r N1 N2).
apply H16.
rewrite<- (CRplus_O_l (CRealOpp a)) at 1.
rewrite<- (CRplus_opp_r (an n)).
rewrite (CRplus_comm (an n) (CRealOpp (an n))).
rewrite (CRplus_assoc (CRealOpp (an n)) (an n) (CRealOpp a)).
rewrite<- (CRplus_assoc (bn n) (CRealOpp (an n)) (CRealPlus (an n) (CRealOpp a))).
apply (CRplus_lt_compat_l (CRealPlus (bn n) (CRealOpp (an n))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealPlus (an n) (CRealOpp a))).
apply (CRabs_def2 (CRealPlus (an n) (CRealOpp a)) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
apply (H14 n).
apply (le_trans N1 (max N1 N2) n).
apply (Nat.le_max_l N1 N2).
apply H16.
cut (CRealPlus (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) = CRealOpp eps).
intro H17.
rewrite H17.
reflexivity.
apply (CRplus_opp_r_uniq eps (CRealPlus (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))))).
rewrite H13 at 1.
rewrite<- (CRplus_assoc (CRealPlus (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))))).
rewrite (CRplus_assoc (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) (CRealOpp (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))))).
rewrite (CRplus_opp_r (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
rewrite (CRplus_comm (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) CRealO).
rewrite (CRplus_O_l (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
apply (CRplus_opp_r (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
rewrite<- (CRmult_I_l (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
rewrite (CRmult_comm CRealI (CRealMult eps (CRealInv (CRealPlus CRealI CRealI)))).
rewrite<- (CRmult_plus_distr_l (CRealMult eps (CRealInv (CRealPlus CRealI CRealI))) CRealI CRealI).
rewrite (CRmult_assoc eps (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI)).
rewrite (CRinv_l (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm eps CRealI).
rewrite (CRmult_I_l eps).
reflexivity.
intro H13.
cut (CRealLt CRealO (CRealPlus CRealI CRealI)).
intro H14.
apply (CRlt_asym CRealO (CRealPlus CRealI CRealI)).
apply H14.
rewrite H13.
rewrite<- H13 at 2.
apply H14.
apply (CRlt_trans CRealO CRealI (CRealPlus CRealI CRealI)).
apply CRlt_O_I.
rewrite<- (CRplus_O_l CRealI) at 1.
rewrite (CRplus_comm CRealO CRealI).
apply (CRplus_lt_compat_l CRealI CRealO CRealI).
apply CRlt_O_I.
rewrite<- (CRmult_O_r eps).
apply (CRmult_lt_compat_l eps CRealO (CRealInv (CRealPlus CRealI CRealI))).
apply H11.
apply (CRinv_O_lt_compat (CRealPlus CRealI CRealI)).
apply (CRlt_trans CRealO CRealI (CRealPlus CRealI CRealI)).
apply CRlt_O_I.
rewrite<- (CRplus_O_l CRealI) at 1.
rewrite (CRplus_comm CRealO CRealI).
apply (CRplus_lt_compat_l CRealI CRealO CRealI).
apply CRlt_O_I.
intros eps H10.
elim (H8 eps H10).
intros N H11.
exists N.
cut (forall n m : nat, (n >= m)%nat -> (n >= N)%nat -> (m >= N)%nat -> CRealLt (CRealabs (CRealPlus (an n) (CRealOpp (an m)))) eps).
intros H12 n m H13 H14.
elim (le_or_lt n m).
intro H15.
cut ((CRealabs (CRealPlus (an n) (CRealOpp (an m))) = (CRealabs (CRealPlus (an m) (CRealOpp (an n)))))).
intro H16.
rewrite H16.
apply (H12 m n).
apply H15.
apply H14.
apply H13.
cut ((CRealOpp (CRealPlus (an n) (CRealOpp (an m)))) = (CRealPlus (an m) (CRealOpp (an n)))).
intro H17.
elim (CRtotal_order (CRealPlus (an n) (CRealOpp (an m))) CRealO).
intro H16.
rewrite (proj2 (CRealabsNature (CRealPlus (an n) (CRealOpp (an m)))) H16).
rewrite (proj1 (CRealabsNature (CRealPlus (an m) (CRealOpp (an n))))).
apply H17.
apply (CRlt_asym CRealO (CRealPlus (an m) (CRealOpp (an n)))).
rewrite<- H17.
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealO (CRealPlus (an n) (CRealOpp (an m)))).
apply H16.
intro H16.
elim H16.
intro H18.
rewrite<- H17.
rewrite H18.
rewrite CRopp_O.
reflexivity.
intro H18.
rewrite (proj1 (CRealabsNature (CRealPlus (an n) (CRealOpp (an m))))).
rewrite (proj2 (CRealabsNature (CRealPlus (an m) (CRealOpp (an n))))).
rewrite<- (CRopp_involutive (CRealPlus (an n) (CRealOpp (an m)))).
rewrite H17.
reflexivity.
rewrite<- H17.
rewrite<- CRopp_O.
apply (CRopp_lt_contravar (CRealPlus (an n) (CRealOpp (an m))) CRealO).
apply H18.
apply (CRlt_asym CRealO (CRealPlus (an n) (CRealOpp (an m))) H18).
cut (CRealPlus (an m) (CRealOpp (an n)) = CRealOpp (CRealPlus (an n) (CRealOpp (an m)))).
intro H16.
rewrite H16.
reflexivity.
apply (CRplus_opp_r_uniq (CRealPlus (an n) (CRealOpp (an m))) (CRealPlus (an m) (CRealOpp (an n)))).
rewrite<- (CRplus_assoc (CRealPlus (an n) (CRealOpp (an m))) (an m) (CRealOpp (an n))).
rewrite (CRplus_assoc (an n) (CRealOpp (an m)) (an m)).
rewrite (CRplus_comm (CRealOpp (an m)) (an m)).
rewrite (CRplus_opp_r (an m)).
rewrite (CRplus_comm (an n) CRealO).
rewrite (CRplus_O_l (an n)).
apply (CRplus_opp_r (an n)).
intro H15.
apply (H12 n m).
apply (le_S_n m n).
apply (le_S (S m)n).
apply H15.
apply H13.
apply H14.
intros n m H12 H13 H14.
rewrite (proj1 (CRealabsNature (CRealPlus (an n) (CRealOpp (an m))))).
apply (CRlt_trans (CRealPlus (an n) (CRealOpp (an m))) (CRealPlus (bn n) (CRealOpp (an m))) eps).
rewrite (CRplus_comm (an n) (CRealOpp (an m))).
rewrite (CRplus_comm (bn n) (CRealOpp (an m))).
apply (CRplus_lt_compat_l (CRealOpp (an m)) (an n) (bn n)).
apply (H9 n).
elim (proj1 (H7 m n H12)).
intro H15.
apply (CRlt_trans (CRealPlus (bn n) (CRealOpp (an m))) (CRealPlus (bn m) (CRealOpp (an m))) eps).
rewrite (CRplus_comm (bn n) (CRealOpp (an m))).
rewrite (CRplus_comm (bn m) (CRealOpp (an m))).
apply (CRplus_lt_compat_l (CRealOpp (an m)) (bn n) (bn m)).
apply H15.
rewrite<- (CRplus_O_l (CRealPlus (bn m) (CRealOpp (an m)))).
rewrite (CRplus_comm CRealO (CRealPlus (bn m) (CRealOpp (an m)))).
apply (CRabs_def2 (CRealPlus (CRealPlus (bn m) (CRealOpp (an m))) CRealO) eps).
rewrite<- CRopp_O.
apply (H11 m H14).
intro H15.
rewrite H15.
rewrite<- (CRplus_O_l (CRealPlus (bn m) (CRealOpp (an m)))).
rewrite (CRplus_comm CRealO (CRealPlus (bn m) (CRealOpp (an m)))).
apply (CRabs_def2 (CRealPlus (CRealPlus (bn m) (CRealOpp (an m))) CRealO) eps).
rewrite<- CRopp_O.
apply (H11 m H14).
elim (proj2 (H7 m n H12)).
intro H15.
apply (CRlt_asym CRealO (CRealPlus (an n) (CRealOpp (an m)))).
rewrite<- (CRplus_opp_r (an n)).
apply (CRplus_lt_compat_l (an n) (CRealOpp (an n)) (CRealOpp (an m))).
apply (CRopp_lt_contravar (an n) (an m)).
apply H15.
intro H16.
rewrite H16.
rewrite (CRplus_opp_r (an n)).
intro H17.
apply (CRlt_asym CRealO CRealO H17 H17).
cut (forall (n : nat), (CRealLt (bn (S n)) (bn n) \/ bn (S n) = bn n) /\ (CRealLt (an n) (an (S n)) \/ an n = an (S n))).
intro H10.
intros n m H11.
elim H11.
apply conj.
right.
reflexivity.
right.
reflexivity.
intros m0 H12 H13.
apply conj.
elim (proj1 H13).
intro H14.
elim (proj1 (H10 m0)).
intro H15.
left.
apply (CRlt_trans (bn (S m0)) (bn m0) (bn n)).
apply H15.
apply H14.
intro H15.
rewrite H15.
left.
apply H14.
intro H14.
rewrite<- H14.
apply (H10 m0).
elim (proj2 H13).
intro H14.
elim (proj2 (H10 m0)).
intro H15.
left.
apply (CRlt_trans (an n) (an m0) (an (S m0))).
apply H14.
apply H15.
intro H15.
rewrite<- H15.
left.
apply H14.
intro H14.
rewrite H14.
apply (H10 m0).
cut (CRealLt CRealO (CRealPlus CRealI CRealI)).
intro H11.
intro n.
unfold an.
unfold bn.
simpl.
elim (classic (forall x : CReal,
       E x ->
       CRealLt x (CRealMult (CRealPlus (an n) (bn n)) (CRealInv (CRealPlus CRealI CRealI))) \/
       x = CRealMult (CRealPlus (an n) (bn n)) (CRealInv (CRealPlus CRealI CRealI)))).
intro H10.
rewrite (proj1 (proj2_sig (H3 (abn n))) H10).
simpl.
apply conj.
left.
rewrite<- (CRmult_I_l (snd (abn n))) at 2.
rewrite (CRmult_comm CRealI (snd (abn n))).
rewrite<- (CRinv_l (CRealPlus CRealI CRealI)) at 3.
rewrite<- (CRmult_assoc (snd (abn n)) (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm (snd (abn n)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_assoc (CRealInv (CRealPlus CRealI CRealI)) (snd (abn n)) (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm (CRealPlus (fst (abn n)) (snd (abn n))) (CRealInv (CRealPlus CRealI CRealI))).
apply (CRmult_lt_compat_l (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus (fst (abn n)) (snd (abn n))) (CRealMult (snd (abn n)) (CRealPlus CRealI CRealI))).
apply (CRinv_O_lt_compat (CRealPlus CRealI CRealI)).
apply H11.
rewrite (CRmult_plus_distr_l (snd (abn n)) CRealI CRealI).
rewrite (CRmult_comm (snd (abn n)) CRealI).
rewrite (CRmult_I_l (snd (abn n))).
rewrite (CRplus_comm (fst (abn n)) (snd (abn n))).
apply (CRplus_lt_compat_l (snd (abn n)) (fst (abn n)) (snd (abn n))).
apply (H9 n).
intro H12.
rewrite H12 in H11.
apply (CRlt_asym CRealO CRealO H11 H11).
right.
reflexivity.
intro H10.
rewrite (proj2 (proj2_sig (H3 (abn n))) H10).
simpl.
apply conj.
right.
reflexivity.
left.
rewrite<- (CRmult_I_l (fst (abn n))) at 1.
rewrite (CRmult_comm CRealI (fst (abn n))).
rewrite<- (CRinv_l (CRealPlus CRealI CRealI)) at 1.
rewrite (CRmult_comm (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI)).
rewrite<- (CRmult_assoc (fst (abn n)) (CRealPlus CRealI CRealI) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (CRealMult (fst (abn n)) (CRealPlus CRealI CRealI)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (CRealPlus (fst (abn n)) (snd (abn n))) (CRealInv (CRealPlus CRealI CRealI))).
apply (CRmult_lt_compat_l (CRealInv (CRealPlus CRealI CRealI)) (CRealMult (fst (abn n)) (CRealPlus CRealI CRealI)) (CRealPlus (fst (abn n)) (snd (abn n)))).
apply (CRinv_O_lt_compat (CRealPlus CRealI CRealI)).
apply H11.
rewrite (CRmult_plus_distr_l (fst (abn n)) CRealI CRealI).
rewrite (CRmult_comm (fst (abn n)) CRealI).
rewrite (CRmult_I_l (fst (abn n))).
apply (CRplus_lt_compat_l (fst (abn n)) (fst (abn n)) (snd (abn n))).
apply H9.
intro H12.
rewrite H12 in H11.
apply (CRlt_asym CRealO CRealO H11 H11).
apply (CRlt_trans CRealO CRealI (CRealPlus CRealI CRealI)).
apply CRlt_O_I.
rewrite<- (CRplus_O_l CRealI) at 1.
rewrite (CRplus_comm CRealO CRealI).
apply (CRplus_lt_compat_l CRealI CRealO CRealI).
apply CRlt_O_I.
cut (forall (n : nat),CRealLt CRealO (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (POW (CRealPlus CRealI CRealI) n)))).
intro H9.
intro n.
rewrite<- (CRplus_O_l (bn n)).
rewrite<- (CRplus_opp_r (an n)).
rewrite (CRplus_assoc (an n) (CRealOpp (an n)) (bn n)).
rewrite<- (CRplus_O_l (an n)) at 1.
rewrite (CRplus_comm CRealO (an n)).
apply (CRplus_lt_compat_l (an n) CRealO (CRealPlus (CRealOpp (an n)) (bn n))).
rewrite (CRplus_comm (CRealOpp (an n)) (bn n)).
rewrite (H6 n).
apply (H9 n).
intro n.
rewrite<- (CRmult_O_r (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
apply (CRmult_lt_compat_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) CRealO (CRealInv (POW (CRealPlus CRealI CRealI) n))).
rewrite<- (CRplus_opp_r b0).
apply (CRplus_lt_compat_l b0 (CRealOpp b0) (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))).
apply (CRopp_lt_contravar b0 (CRealPlus a0 (CRealOpp CRealI))).
elim (H4 a0 H5).
intro H9.
apply (CRlt_trans (CRealPlus a0 (CRealOpp CRealI)) a0 b0).
rewrite<- (CRplus_O_l a0) at 2.
rewrite (CRplus_comm CRealO a0).
apply (CRplus_lt_compat_l a0 (CRealOpp CRealI) CRealO).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealI CRealO).
apply CRlt_O_I.
apply H9.
intro H9.
rewrite H9.
rewrite<- (CRplus_O_l b0) at 2.
rewrite (CRplus_comm CRealO b0).
apply (CRplus_lt_compat_l b0 (CRealOpp CRealI) CRealO).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealI CRealO).
apply CRlt_O_I.
apply (CRinv_O_lt_compat (POW (CRealPlus CRealI CRealI) n)).
elim n.
simpl.
apply CRlt_O_I.
intros n0 H9.
simpl.
rewrite (CRmult_plus_distr_l (POW (CRealPlus CRealI CRealI) n0) CRealI CRealI).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) CRealI).
rewrite (CRmult_I_l (POW (CRealPlus CRealI CRealI) n0)).
apply (CRlt_trans CRealO (POW (CRealPlus CRealI CRealI) n0) (CRealPlus (POW (CRealPlus CRealI CRealI) n0) (POW (CRealPlus CRealI CRealI) n0))).
apply H9.
rewrite<- (CRplus_O_l (POW (CRealPlus CRealI CRealI) n0)) at 1.
rewrite (CRplus_comm CRealO (POW (CRealPlus CRealI CRealI) n0)).
apply (CRplus_lt_compat_l (POW (CRealPlus CRealI CRealI) n0) CRealO (POW (CRealPlus CRealI CRealI) n0)).
apply H9.
cut (CRealLt CRealO (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
intro H7.
intros eps H8.
elim (Archimedes2 (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)).
intros N H9.
exists N.
intros n H10.
rewrite (CRplus_comm (CRealPlus (bn n) (CRealOpp (an n))) (CRealOpp CRealO)).
apply (CRabs_def1 (CRealPlus (CRealOpp CRealO) (CRealPlus (bn n) (CRealOpp (an n)))) eps).
rewrite CRopp_O.
rewrite (CRplus_O_l (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite (H6 n).
rewrite<- (CRmult_I_l eps).
rewrite<- (CRinv_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) at 4.
rewrite (CRmult_comm (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
rewrite (CRmult_assoc (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps).
apply (CRmult_lt_compat_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (POW (CRealPlus CRealI CRealI) n)) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)).
apply H7.
apply (CRabs_def2 (CRealInv (POW (CRealPlus CRealI CRealI) n)) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)).
rewrite<- (CRplus_O_l (CRealInv (POW (CRealPlus CRealI CRealI) n))).
rewrite (CRplus_comm CRealO (CRealInv (POW (CRealPlus CRealI CRealI) n))).
rewrite<- CRopp_O.
apply (H9 n).
apply H10.
intro H11.
rewrite H11 in H7.
apply (CRlt_asym CRealO CRealO H7 H7).
rewrite CRopp_O.
rewrite (CRplus_O_l (CRealPlus (bn n) (CRealOpp (an n)))).
rewrite (H6 n).
rewrite<- (CRmult_I_l eps).
rewrite<- (CRinv_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) at 1.
rewrite (CRmult_comm (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
rewrite (CRmult_assoc (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps).
cut ((CRealOpp (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps))) = (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealOpp (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)))).
intro H11.
rewrite H11.
apply (CRmult_lt_compat_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealOpp (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)) (CRealInv (POW (CRealPlus CRealI CRealI) n))).
apply H7.
apply (CRabs_def2 (CRealInv (POW (CRealPlus CRealI CRealI) n)) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)).
rewrite<- (CRplus_O_l (CRealInv (POW (CRealPlus CRealI CRealI) n))).
rewrite (CRplus_comm CRealO (CRealInv (POW (CRealPlus CRealI CRealI) n))).
rewrite<- CRopp_O.
apply (H9 n).
apply H10.
cut (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealOpp (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)) = CRealOpp (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps))).
intro H11.
rewrite H11.
reflexivity.
apply (CRplus_opp_r_uniq (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)) (CRealMult (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealOpp (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)))).
rewrite<- (CRmult_plus_distr_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps) (CRealOpp (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps))).
rewrite (CRplus_opp_r (CRealMult (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) eps)).
apply (CRmult_O_r (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
intro H11.
rewrite H11 in H7.
apply (CRlt_asym CRealO CRealO H7 H7).
rewrite<- (CRmult_O_r (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))))).
apply (CRmult_lt_compat_l (CRealInv (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))) CRealO eps).
apply (CRinv_O_lt_compat (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
apply H7.
apply H8.
rewrite<- (CRplus_opp_r b0).
apply (CRplus_lt_compat_l b0 (CRealOpp b0) (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))).
apply (CRopp_lt_contravar b0 (CRealPlus a0 (CRealOpp CRealI))).
elim (H4 a0 H5).
intro H9.
apply (CRlt_trans (CRealPlus a0 (CRealOpp CRealI)) a0 b0).
rewrite<- (CRplus_O_l a0) at 2.
rewrite (CRplus_comm CRealO a0).
apply (CRplus_lt_compat_l a0 (CRealOpp CRealI) CRealO).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealI CRealO).
apply CRlt_O_I.
apply H9.
intro H9.
rewrite H9.
rewrite<- (CRplus_O_l b0) at 2.
rewrite (CRplus_comm CRealO b0).
apply (CRplus_lt_compat_l b0 (CRealOpp CRealI) CRealO).
rewrite<- CRopp_O.
apply (CRopp_lt_contravar CRealI CRealO).
apply CRlt_O_I.
intro n.
elim n.
unfold an.
unfold bn.
simpl.
rewrite<- (CRmult_I_l (CRealInv CRealI)).
rewrite (CRmult_comm CRealI (CRealInv CRealI)).
rewrite (CRinv_l CRealI).
rewrite (CRmult_comm (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) CRealI).
rewrite (CRmult_I_l (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI))))).
reflexivity.
intro H6.
apply (CRlt_asym CRealO CRealO).
rewrite<- H6 at 2.
apply CRlt_O_I.
rewrite<- H6 at 2.
apply CRlt_O_I.
intros n0 H6.
unfold an.
unfold bn.
simpl.
cut (CRealO <> (CRealPlus CRealI CRealI)).
intro H7.
cut (POW (CRealPlus CRealI CRealI) n0 <> CRealO).
intro H8.
elim (classic (forall x : CReal,
       E x ->
       CRealLt x (CRealMult (CRealPlus (an n0) (bn n0)) (CRealInv (CRealPlus CRealI CRealI))) \/
       x = CRealMult (CRealPlus (an n0) (bn n0)) (CRealInv (CRealPlus CRealI CRealI)))).
intro H9.
rewrite (proj1 (proj2_sig (H3 (abn n0))) H9).
unfold snd at 1.
unfold fst at 2.
cut (CRealPlus (CRealMult (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI))) (CRealOpp (fst (abn n0))) = (CRealMult (CRealPlus (snd (abn n0)) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)))).
intro H10.
rewrite H10.
unfold an in H6.
unfold bn in H6.
rewrite H6.
cut ((CRealInv (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))) = CRealMult (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI))).
intro H11.
rewrite H11.
apply (CRmult_assoc (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite<- (CRmult_I_l (CRealMult (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI)))).
rewrite<- (CRinv_l (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))) at 5.
rewrite (CRmult_assoc (CRealInv (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))) (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI)) (CRealMult (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI)))).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI)).
rewrite<- (CRmult_assoc (CRealMult (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_assoc (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0) (CRealInv (POW (CRealPlus CRealI CRealI) n0))).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) (CRealInv (POW (CRealPlus CRealI CRealI) n0))).
rewrite (CRinv_l (POW (CRealPlus CRealI CRealI) n0)).
rewrite (CRmult_comm (CRealPlus CRealI CRealI) CRealI).
rewrite (CRmult_I_l (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm (CRealPlus CRealI CRealI) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRinv_l (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm (CRealInv (CRealMult (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0))) CRealI).
rewrite (CRmult_I_l (CRealInv (CRealMult (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0)))).
reflexivity.
intro H11.
apply H7.
rewrite H11.
reflexivity.
apply H8.
intro H11.
apply H7.
rewrite<- (CRmult_I_l (CRealPlus CRealI CRealI)).
rewrite<- (CRinv_l (POW (CRealPlus CRealI CRealI) n0)) at 1.
rewrite (CRmult_assoc (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI)).
rewrite H11.
rewrite (CRmult_O_r (CRealInv (POW (CRealPlus CRealI CRealI) n0))).
reflexivity.
apply H8.
rewrite<- (CRmult_I_l (fst (abn n0))) at 2.
rewrite (CRmult_comm CRealI (fst (abn n0))).
rewrite<- (CRinv_l (CRealPlus CRealI CRealI)) at 3.
cut ((CRealOpp (CRealMult (fst (abn n0)) (CRealMult (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI)))) = (CRealMult (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)))).
intro H10.
rewrite H10.
rewrite (CRmult_comm (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite<- (CRmult_plus_distr_l (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite (CRplus_comm (fst (abn n0)) (snd (abn n0))).
rewrite (CRplus_assoc (snd (abn n0)) (fst (abn n0)) (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite<- (CRplus_assoc (fst (abn n0)) (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))).
rewrite (CRplus_opp_r (fst (abn n0))).
rewrite (CRplus_O_l (CRealOpp (fst (abn n0)))).
apply (CRmult_comm (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus (snd (abn n0)) (CRealOpp (fst (abn n0))))).
cut (CRealMult (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)) = CRealOpp (CRealMult (fst (abn n0)) (CRealMult (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI)))).
intro H10.
rewrite H10.
reflexivity.
apply (CRplus_opp_r_uniq (CRealMult (fst (abn n0)) (CRealMult (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI))) (CRealMult (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)))).
rewrite (CRmult_comm (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI)).
rewrite<- (CRmult_assoc (fst (abn n0)) (CRealPlus CRealI CRealI) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (CRealMult (fst (abn n0)) (CRealPlus CRealI CRealI)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite<- (CRmult_plus_distr_l (CRealInv (CRealPlus CRealI CRealI)) (CRealMult (fst (abn n0)) (CRealPlus CRealI CRealI)) (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite (CRmult_plus_distr_l (fst (abn n0)) CRealI CRealI).
rewrite (CRmult_comm (fst (abn n0)) CRealI).
rewrite (CRmult_I_l (fst (abn n0))).
rewrite (CRplus_assoc (fst (abn n0)) (fst (abn n0)) (CRealPlus (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite<- (CRplus_assoc (fst (abn n0)) (CRealOpp (fst (abn n0))) (CRealOpp (fst (abn n0)))).
rewrite (CRplus_opp_r (fst (abn n0))).
rewrite (CRplus_O_l (CRealOpp (fst (abn n0)))).
rewrite (CRplus_opp_r (fst (abn n0))).
apply (CRmult_O_r (CRealInv (CRealPlus CRealI CRealI))).
intro H10.
apply H7.
rewrite H10.
reflexivity.
intro H9.
rewrite (proj2 (proj2_sig (H3 (abn n0))) H9).
unfold snd at 1.
unfold fst at 1.
cut (CRealPlus (snd (abn n0)) (CRealOpp (CRealMult (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI)))) = (CRealMult (CRealPlus (snd (abn n0)) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)))).
intro H10.
rewrite H10.
unfold an in H6.
unfold bn in H6.
rewrite H6.
cut ((CRealInv (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))) = CRealMult (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI))).
intro H11.
rewrite H11.
apply (CRmult_assoc (CRealPlus b0 (CRealOpp (CRealPlus a0 (CRealOpp CRealI)))) (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite<- (CRmult_I_l (CRealMult (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI)))).
rewrite<- (CRinv_l (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))) at 5.
rewrite (CRmult_assoc (CRealInv (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI))) (CRealMult (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI)) (CRealMult (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI)))).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI)).
rewrite<- (CRmult_assoc (CRealMult (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_assoc (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0) (CRealInv (POW (CRealPlus CRealI CRealI) n0))).
rewrite (CRmult_comm (POW (CRealPlus CRealI CRealI) n0) (CRealInv (POW (CRealPlus CRealI CRealI) n0))).
rewrite (CRinv_l (POW (CRealPlus CRealI CRealI) n0)).
rewrite (CRmult_comm (CRealPlus CRealI CRealI) CRealI).
rewrite (CRmult_I_l (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm (CRealPlus CRealI CRealI) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRinv_l (CRealPlus CRealI CRealI)).
rewrite (CRmult_comm (CRealInv (CRealMult (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0))) CRealI).
rewrite (CRmult_I_l (CRealInv (CRealMult (CRealPlus CRealI CRealI) (POW (CRealPlus CRealI CRealI) n0)))).
reflexivity.
intro H11.
apply H7.
rewrite H11.
reflexivity.
apply H8.
intro H11.
apply H7.
rewrite<- (CRmult_I_l (CRealPlus CRealI CRealI)).
rewrite<- (CRinv_l (POW (CRealPlus CRealI CRealI) n0)) at 1.
rewrite (CRmult_assoc (CRealInv (POW (CRealPlus CRealI CRealI) n0)) (POW (CRealPlus CRealI CRealI) n0) (CRealPlus CRealI CRealI)).
rewrite H11.
rewrite (CRmult_O_r (CRealInv (POW (CRealPlus CRealI CRealI) n0))).
reflexivity.
apply H8.
rewrite<- (CRmult_I_l (snd (abn n0))) at 1.
rewrite (CRmult_comm CRealI (snd (abn n0))).
rewrite<- (CRinv_l (CRealPlus CRealI CRealI)) at 1.
cut ((CRealOpp (CRealMult (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI)))) = (CRealMult (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)))).
intro H10.
rewrite H10.
rewrite (CRmult_comm (CRealPlus (snd (abn n0)) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (snd (abn n0)) (CRealMult (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI))).
rewrite (CRmult_assoc (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus CRealI CRealI) (snd (abn n0))).
rewrite (CRmult_comm (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite<- (CRmult_plus_distr_l (CRealInv (CRealPlus CRealI CRealI)) (CRealMult (CRealPlus CRealI CRealI) (snd (abn n0))) (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite (CRmult_comm (CRealPlus CRealI CRealI) (snd (abn n0))).
rewrite (CRmult_plus_distr_l (snd (abn n0)) CRealI CRealI).
rewrite (CRmult_comm (snd (abn n0)) CRealI).
rewrite (CRmult_I_l (snd (abn n0))).
rewrite (CRplus_assoc (snd (abn n0)) (snd (abn n0)) (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite<- (CRplus_assoc (snd (abn n0)) (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))).
rewrite (CRplus_opp_r (snd (abn n0))).
rewrite (CRplus_O_l (CRealOpp (fst (abn n0)))).
reflexivity.
cut (CRealMult (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)) = CRealOpp (CRealMult (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI)))).
intro H10.
rewrite H10.
reflexivity.
apply (CRplus_opp_r_uniq (CRealMult (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI))) (CRealMult (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI)))).
rewrite (CRmult_comm (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite (CRmult_comm (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))) (CRealInv (CRealPlus CRealI CRealI))).
rewrite<- (CRmult_plus_distr_l (CRealInv (CRealPlus CRealI CRealI)) (CRealPlus (fst (abn n0)) (snd (abn n0))) (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite (CRplus_assoc (fst (abn n0)) (snd (abn n0)) (CRealPlus (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0))))).
rewrite<- (CRplus_assoc (snd (abn n0)) (CRealOpp (snd (abn n0))) (CRealOpp (fst (abn n0)))).
rewrite (CRplus_opp_r (snd (abn n0))).
rewrite (CRplus_O_l (CRealOpp (fst (abn n0)))).
rewrite (CRplus_opp_r (fst (abn n0))).
apply (CRmult_O_r (CRealInv (CRealPlus CRealI CRealI))).
intro H10.
apply H7.
rewrite H10.
reflexivity.
elim n0.
simpl.
apply CReal_I_neq_O.
intros n1 H8.
simpl.
intro H9.
apply H7.
rewrite<- (CRmult_I_l (CRealPlus CRealI CRealI)).
rewrite<- (CRinv_l (POW (CRealPlus CRealI CRealI) n1)) at 1.
rewrite (CRmult_assoc (CRealInv (POW (CRealPlus CRealI CRealI) n1)) (POW (CRealPlus CRealI CRealI) n1) (CRealPlus CRealI CRealI)).
rewrite H9.
rewrite (CRmult_O_r (CRealInv (POW (CRealPlus CRealI CRealI) n1))).
reflexivity.
apply H8.
cut (CRealLt CRealO (CRealPlus CRealI CRealI)).
intro H7.
intro H8.
apply (CRlt_asym CRealO CRealO).
rewrite H8 at 2.
apply H7.
rewrite H8 at 2.
apply H7.
apply (CRlt_trans CRealO CRealI (CRealPlus CRealI CRealI)).
apply CRlt_O_I.
rewrite<- (CRplus_O_l CRealI) at 1.
rewrite (CRplus_comm CRealO CRealI).
apply (CRplus_lt_compat_l CRealI CRealO CRealI CRlt_O_I).
intro z.
apply constructive_definite_description.
apply (unique_existence (fun (x : CReal * CReal) => ((forall x0 : CReal,
    E x0 ->
    CRealLt x0 (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) \/
    x0 = CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) ->
   x = (fst z, CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)))) /\
  (~
   (forall x0 : CReal,
    E x0 ->
    CRealLt x0 (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) \/
    x0 = CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) ->
   x = (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)), snd z)))).
apply conj.
elim (classic (forall x0 : CReal, E x0 -> CRealLt x0 (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) \/ x0 = CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)))).
intro H3.
exists (fst z, CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))).
apply conj.
intro H4.
reflexivity.
intro H4.
apply False_ind.
apply (H4 H3).
intro H3.
exists (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)), snd z).
apply conj.
intro H4.
apply False_ind.
apply (H3 H4).
intro H4.
reflexivity.
intros x y H3 H4.
elim (classic (forall x0 : CReal, E x0 -> CRealLt x0 (CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI))) \/ x0 = CRealMult (CRealPlus (fst z) (snd z)) (CRealInv (CRealPlus CRealI CRealI)))).
intro H5.
(rewrite (proj1 H3)).
(rewrite (proj1 H4)).
reflexivity.
apply H5.
apply H5.
intro H5.
(rewrite (proj2 H3)).
(rewrite (proj2 H4)).
reflexivity.
apply H5.
apply H5.
Qed.

Record Real : Type := mkReal
{
R   : Type;
O : R;
I : R;
plus : R -> R -> R;
opp : R -> R;
mul : R -> R -> R;
inv : R -> R;
lt : R -> R -> Prop;
Rplus_comm : forall (r1 r2 : R), (plus r1 r2) = (plus r2 r1);
Rplus_assoc : forall (r1 r2 r3 : R), (plus (plus r1 r2) r3) = (plus r1 (plus r2 r3));
Rplus_opp_r : forall (r : R), (plus r (opp r)) = O;
Rplus_0_l : forall (r : R), (plus O r) = r;
Rmult_comm : forall (r1 r2 : R), (mul r1 r2) = (mul r2 r1);
Rmult_assoc : forall (r1 r2 r3 : R), (mul (mul r1 r2) r3) = (mul r1 (mul r2 r3));
Rinv_l : forall (r : R), r <> O -> (mul (inv r) r) = I;
Rmult_1_l : forall (r : R), (mul I r) = r;
R1_neq_R0 : I <> O;
Rmult_plus_distr_l : forall (r1 r2 r3 : R), (mul r1 (plus r2 r3)) = (plus (mul r1 r2) (mul r1 r3));
Rlt_asym : forall (r1 r2 : R), (lt r1 r2) -> (~ (lt r2 r1));
Rlt_trans : forall (r1 r2 r3 : R), (lt r1 r2) -> (lt r2 r3) -> (lt r1 r3);
Rtotal_order : forall (r1 r2 : R), (lt r1 r2) \/ (r1 = r2) \/ (lt r2 r1);
Rplus_lt_compat_l : forall (r r1 r2 : R), (lt r1 r2) -> (lt (plus r r1) (plus r r2));
Rmult_lt_compat_l : forall (r r1 r2 : R), (lt O r) -> (lt r1 r2) -> (lt (mul r r1) (mul r r2));
completeness : forall (E : R -> Prop), (exists (m : R), forall (x : R), E x -> (lt x m) \/ x = m) -> (exists x : R, E x) -> { m:R | (forall (x : R), E x -> (lt x m) \/ x = m) /\ (forall (b : R), (forall x : R, E x -> (lt x b) \/ x = b) -> ((lt m b) \/ m = b))}
}.

Definition CauchyReal := mkReal CReal CRealO CRealI CRealPlus CRealOpp CRealMult CRealInv CRealLt CRplus_comm CRplus_assoc CRplus_opp_r CRplus_O_l CRmult_comm CRmult_assoc CRinv_l CRmult_I_l CReal_I_neq_O CRmult_plus_distr_l CRlt_asym CRlt_trans CRtotal_order CRplus_lt_compat_l CRmult_lt_compat_l CRealcompleteness.


