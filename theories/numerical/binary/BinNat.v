Require Import Lists.List.
Require Import Init.Nat.
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

Inductive valid_BinNat : nat -> BinNat -> Prop :=
	| valid_BinNat_Nil : valid_BinNat 0 []
	| valid_BinNat_Top : forall {n : nat}, valid_BinNat n [1]
	| valid_BinNat_Cons : forall {n : nat} (l : BinNat) (b : Bit),
		valid_BinNat (S n) l -> valid_BinNat n (b :: l).

Lemma valid_BinNat_tail : forall (n : BinNat) (b : Bit),
	valid_BinNat 0 (b :: n) -> valid_BinNat 0 n.
Proof.
	{	assert (HR : forall  (n : BinNat) (b : Bit) {d : nat},
			n <> [] -> valid_BinNat d (b :: n) -> valid_BinNat d n).
	+	intro n.
		{	induction n as [| bit t HR]; intros b d Hnil H; [| destruct bit].
		+	contradiction.
		+	inversion_clear H.
			apply valid_BinNat_Cons.
			{	apply (HR 0).
			+	inversion_clear H0.
				inversion_clear H; discriminate.
			+	assumption.
			}
		+	destruct t; inversion_clear H.
			apply valid_BinNat_Top.
			apply valid_BinNat_Cons.
			{	apply (HR 1).
			+	discriminate.
			+	assumption.
			}
		}
	+	intros n b H.
		{	destruct n.
		+	apply valid_BinNat_Nil.
		+	{	apply (HR _ b).
			+	discriminate.
			+	assumption.
			}
		}
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

Fixpoint gt_dec n m :=
	match n, m with
	| [], _ => false
	| _, [] => true
	| 1 :: tn, 0 :: tm => gt_dec_borrow tn tm
	| _ :: tn, _ :: tm => tm <? tn
	end
with gt_dec_borrow n m :=
	match n, m with
	| _, [] => true
	| [], _ => false
	| 0 :: tn, 1 :: tm => tm <? tn
	| _ :: tn, _ :: tm => gt_dec_borrow tn tm
	end where "n <? m" := (gt_dec m n) : bin_nat_scope.

Notation "n <? m" := (gt_dec m n) : bin_nat_scope.

Fixpoint sub n m :=
	match n, m with
	| [], _ => []
	| _, [] => n
	| b :: tn, 0 :: tm => b :: (tn - tm)
	| 1 :: tn, 1 :: tm => 0 :: (tn - tm)
	| 0 :: tn, 1 :: tm => 1 :: (sub_borrow tn tm)
	end
with sub_borrow n m :=
	match n, m with
	| [], _ => []
	| _, [] => dec n
	| 1 :: tn, 0 :: tm => 0 :: (tn - tm)
	| 0 :: tn, 0 :: tm => 1 :: (sub_borrow tn tm)
	| 1 :: tn, 1 :: tm => 1 :: (sub_borrow tn tm)
	| 0 :: tn, 1 :: tm => 0 :: (sub_borrow tn tm)
	end where "n - m" := (sub n m) : bin_nat_scope.
