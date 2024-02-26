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

Local Definition bit_not b :=
	match b with
	| 0 => 1
	| 1 => 0
	end.

Local Definition carry_of a b c :=
	match a, b, c with
	| 1, 1, _ | 1, _, 1 | _, 1, 1 => 1
	| _, _, _ => 0
	end.

Local Definition sum_bit_of a b c :=
	match a, b with
	| 1, 1 | 0, 0 => c
	| 1, 0 | 0, 1 => bit_not c
	end.

Fixpoint add_carry n m carry :=
	match n, m with
	| [], r | r, [] =>
		match carry with
		| 0 => r
		| 1 => inc r
		end
	| a :: tn, b :: tm => sum_bit_of a b carry
		:: (add_carry tn tm (carry_of a b carry))
	end.
