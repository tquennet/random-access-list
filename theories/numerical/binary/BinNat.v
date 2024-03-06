Require Import Lists.List.
Require Import Init.Nat.
Import ListNotations.

Declare Scope bin_nat_scope.
Open Scope bin_nat_scope.

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

Inductive valid_BinNat : nat -> BinNat -> Prop :=
	| valid_BinNat_Nil : valid_BinNat 0 []
	| valid_BinNat_Top : forall {n : nat}, valid_BinNat n [1]
	| valid_BinNat_Cons : forall {n : nat} (l : BinNat) (b : Bit),
		valid_BinNat (S n) l -> valid_BinNat n (b :: l).

Lemma valid_BinNat_S : forall (n : BinNat) (b : Bit) (d : nat),
	valid_BinNat d (b :: n) -> valid_BinNat (S d) (b :: n).
Proof.
	intros n.
	{	induction n as [|b2 tn HR]; intros b d H; inversion_clear H.
	+	apply valid_BinNat_Top.
	+	inversion_clear H0.
	+	apply valid_BinNat_Cons.
		apply HR.
		assumption.
	}
Qed.

Fixpoint inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 ::inc t
	end.

Fixpoint dec n :=
	match n with
	| [] => []
	| [1] => []
	| 0 :: t => 1 :: dec t
	| 1 :: t => 0 :: t
	end.

Lemma BinNat_inc_dec : forall (n : BinNat) {d : nat},
	valid_BinNat d n -> dec (inc n) = n.
Proof.
	intro n.
	{	induction n as [|b tn HR]; intros d H;
			try destruct b; inversion_clear H.
	+	reflexivity.
	+	destruct tn; inversion_clear H0; reflexivity.
	+	reflexivity.
	+	simpl.
		f_equal.
		apply (HR (S d)).
		assumption.
	}
Qed.

Fixpoint add n m :=
	match n, m with
	| [], _ => m
	| _, [] => n
	| 0 :: tn, b :: tm => b :: (tn + tm)
	| b :: tn, 0 :: tm => b :: (tn + tm)
	| 1 :: tn, 1 :: tm => 0 :: inc (tn + tm)
	end where "n + m" := (add n m) : bin_nat_scope.

Definition BinNat_safe_zero n :=
	match n with
	| [] => []
	| _ => 0 :: n
	end.
Definition BinNat_safe_bit b n :=
	match b with
	| 0 => BinNat_safe_zero n
	| 1 => 1 :: n
	end.

Local Definition add_bit o b :=
	match o with
	| None => None
	| Some n => Some (BinNat_safe_bit b n)
	end.

Local Fixpoint sub_aux n m :=
	match n, m with
	| [], _ => None
	| _, [] => None
	| 1 :: tn, [1] => Some (BinNat_safe_zero tn)
	| 1 :: tn, 0 :: tm => add_bit (sub_aux tn tm) 1
	| 0 :: tn, 0 :: tm => add_bit (sub_aux tn tm) 0
	| 1 :: tn, 1 :: tm => add_bit (sub_aux tn tm) 0
	| 0 :: tn, 1 :: tm => add_bit (sub_borrow tn tm) 1
	end
with sub_borrow n m :=
	match n, m with
	| [], _ => None
	| 0 :: tn, [] => add_bit (sub_borrow tn []) 1
	| 1 :: tn, [] => Some (BinNat_safe_zero tn)
	| 1 :: tn, 0 :: tm => add_bit (sub_aux tn tm) 0
	| 0 :: tn, 0 :: tm => add_bit (sub_borrow tn tm) 1
	| 1 :: tn, 1 :: tm => add_bit (sub_borrow tn tm) 1
	| 0 :: tn, 1 :: tm => add_bit (sub_borrow tn tm) 0
	end.

Definition sub n m :=
	match m with
	| [] => n
	| _ =>	match sub_aux n m with
		| None => []
		| Some n => n
		end
	end.

Notation "n - m" := (sub n m) : bin_nat_scope.
