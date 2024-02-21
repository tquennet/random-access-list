Require Import Lists.List.
Import ListNotations.

Reserved Notation "++ n" (at level 35).
Reserved Notation "-- n" (at level 35).

Declare Scope bin_nat_scope.

Inductive Bit := Zero | One.
Definition BinNat := list Bit.

Notation "0" := Zero.
Notation "1" := One.

Fixpoint BinNat_to_nat n : nat :=
	match n with
	| [] => O
	| 0 :: t => 2 * (BinNat_to_nat t)
	| 1 :: t => S (2 * BinNat_to_nat t)
	end.

Fixpoint inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 :: ++t
	end where "++ n" := (inc n).

Fixpoint dec n :=
	match n with
	| [] => []
	| 0 :: t => 1 :: --t
	| 1 :: t => 0 :: t
	end where "-- n" := (dec n).

Fixpoint add n m :=
	match n, m with
	| [], _ => m
	| _, [] => n
	| 0 :: tn, b :: tm => b :: (tn + tm)
	| b :: tn, 0 :: tm => b :: (tn + tm)
	| 1 :: tn, 1 :: tm => 0 :: ++(tn + tm)
	end where "n + m" := (add n m).
