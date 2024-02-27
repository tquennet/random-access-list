Require Import Lists.List.
Import ListNotations.

Declare Scope bin_nat_scope.

Variant Bit := Zero | One.
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
	| 1 :: t => 0 ::inc t
	end.

Fixpoint dec n :=
	match n with
	| [] => []
	| 0 :: t => 1 :: dec t
	| 1 :: t => 0 :: t
	end.

Fixpoint add n m :=
	match n, m with
	| [], _ => m
	| _, [] => n
	| 0 :: tn, b :: tm => b :: (tn + tm)
	| b :: tn, 0 :: tm => b :: (tn + tm)
	| 1 :: tn, 1 :: tm => 0 :: inc (tn + tm)
	end where "n + m" := (add n m).
