# Real number in Coq
I Composed real number defined as following in Coq.
```
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
```
# Axiom I use
I import these libraly. I don't use axioms for anything other than what is included in these.
- Require Import Coq.Sets.Ensembles.
- Require Import Coq.Logic.Classical.
- Require Import Coq.Logic.Description.
- Require Import Coq.Logic.FunctionalExtensionality.
- Require Import Coq.Logic.IndefiniteDescription.
- Require Export QArith_base.
- Require Import Coq.QArith.Qabs.
- Require Import Coq.Logic.PropExtensionality.
# Reference
- 杉浦 光夫, 解析入門, 東京大学出版会, 1980
- 齋藤 正彦, 数学の基礎, 東京大学出版会, 2002
