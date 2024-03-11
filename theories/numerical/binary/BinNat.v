Require Import Lists.List FunInd.
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

Fixpoint inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 ::inc t
	end.

Functional Scheme inc_ind := Induction for inc Sort Prop.

Lemma BinNat_inc_S : forall (n : BinNat),
	BinNat_to_nat (inc n) = S (BinNat_to_nat n).
Proof.
	intro n.
	{	induction n as [| b tn HR]; [|destruct b]; simpl.
	+	reflexivity.
	+	reflexivity.
	+	rewrite !PeanoNat.Nat.add_0_r, HR.
		rewrite plus_Sn_m, <- plus_n_Sm.
		reflexivity.
	}
Qed.

Inductive CBN : BinNat -> Prop :=
	| CBN_0 : CBN []
	| CBN_inc : forall (n : BinNat),
		CBN n -> CBN (inc n).

Local Lemma inc_non_empty : forall (n : BinNat),
	exists b tn, b :: tn = inc n.
Proof.
	intros n.
	{	destruct n as [|b tn]; [|destruct b].
	+	exists 1, []; reflexivity.
	+	exists 1, tn; reflexivity.
	+	exists 0, (inc tn); reflexivity.
	}
Qed.

Local Lemma inc_last : forall (n : BinNat),
	last n 1 = 1 -> last (inc n) 1 = 1.
Proof.
	intro n.
	{	functional induction (inc n); intro H.
		+	reflexivity.
		+ destruct t; [discriminate|].
			exact H.
		+	decompose record (inc_non_empty t).
			assert (Ht : last t 1 = 1) by (destruct t; [reflexivity | assumption]).
			apply IHl in Ht.
			rewrite <- H1 in*.
			exact Ht.
		}
Qed.

Lemma CBN_last : forall (n : BinNat),
	CBN n -> last n 1 = 1.
Proof.
	intros n H.
	{	induction H as [| n HCBN HR].
	+ reflexivity.
	+ apply inc_last.
		assumption.
	}
Qed.

Fixpoint dec n :=
	match n with
	| [] => []
	| [1] => []
	| 0 :: t => 1 :: dec t
	| 1 :: t => 0 :: t
	end.

Lemma BinNat_inc_dec : forall (n : BinNat),
	CBN n -> dec (inc n) = n.
Proof.
	intros n Hn.
	apply CBN_last in Hn.
	{	functional induction (inc n).
	+ reflexivity.
	+	destruct t; [discriminate|].
		reflexivity.
	+	simpl.
		destruct t; [reflexivity|].
		apply IHl in Hn.
		rewrite Hn.
		reflexivity.
	}
Qed.

(* modifiés dans la branche binary-discard

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

*)
