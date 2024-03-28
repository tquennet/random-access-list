Require Import Lists.List FunInd .
Require Import Init.Nat.
Import ListNotations.

Declare Scope bin_nat_scope.
Open Scope bin_nat_scope.

(********************************************************************************)
(*	Notations are defined in bin_nat_scope.										*)
(*	BN == the type of binary numbers.											*)
(*	BN_canonical == a predicate identifying canonical BinNat					*)
(*		BN_zero  == the BN representing 0										*)
(*			+: BN_canonical_0 : BN_canonical									*)
(*		BN_inc n == the successor of n											*)
(*			+: BN_canonical_inc n : BN_canonical n -> N_canonical (BN_inc n)	*)
(*																				*)
(*	**	Unary operator:															*)
(*		BN_to_nat n == n as native coq nat										*)
(*			   BN_dec n == the predecessor of n									*)
(*			BN_trim n == the canonical version of n, preserving BN_to_nat		*)
(*	**	Binary operators:														*)
(*		 sub n m, n - m == the difference between n and m						*)
(*	** Lemmes:																	*)
(*		BN_dec_canonical : forall l, BN_canonical l -> BN_canonical (BN_dec l)	*)
(*		BN_trim_canonical : forall l, BN_canonical (BN_trom l)					*)
(*		BN_inc_dec : forall l, BN_canonical n -> dec (inc n) = n				*)
(*		BN_sub_canonical : forall n m, BN_canonical (n - m)						*)
(********************************************************************************)

Variant Bit := Zero | One.
Definition BN := list Bit.
Definition DBN := BN.

Notation "0" := Zero.
Notation "1" := One.

Fixpoint BN_to_nat n : nat :=
	match n with
	| [] => O
	| 0 :: t => 2 * (BN_to_nat t)
	| 1 :: t => S (2 * BN_to_nat t)
	end.

Definition BN_zero : BN := [].

Fixpoint BN_inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 :: BN_inc t
	end.


Functional Scheme BN_inc_ind := Induction for BN_inc Sort Prop.


Inductive BN_canonical : BN -> Prop :=
	| BN_canonical_0 : BN_canonical []
	| BN_canonical_inc : forall (n : BN),
		BN_canonical n -> BN_canonical (BN_inc n).

Local Lemma CBN_1 : BN_canonical [1].
Proof.
	replace [1] with (BN_inc []) by reflexivity.
	apply BN_canonical_inc, BN_canonical_0.
Qed.

(*Lemma BN_inc_S : forall (n : BN),
	BN_to_nat (BN_inc n) = S (BN_to_nat n).
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

Lemma CBN_unicity : forall n m,
	CBN n -> CBN m ->
	BN_to_nat n = BN_to_nat m ->
	n = m.
Proof.
	intros n m Hn.
	generalize dependent m.
	{	induction Hn as [|n Hn HR]; intros m Hm Heq; destruct Hm as [|m Hm].
	+	reflexivity.
	+	rewrite BN_inc_S in Heq.
		discriminate.
	+	rewrite BN_inc_S in Heq.
		discriminate.
	+	f_equal.
		apply HR; [assumption|].
		rewrite !BN_inc_S in Heq.
		injection Heq as Heq.
		assumption.
	}
Qed.*)

Fixpoint CBN_struct b n :=
	match n with
	| [] => b
	| 0 :: tn => CBN_struct false tn
	| 1 :: tn => CBN_struct true tn
	end.

Definition CBN_st n := CBN_struct true n = true.

Local Lemma CBN_struct_false : forall n,
	CBN_struct false n = true -> CBN_st n.
Proof.
	intros n H.
	destruct n; [inversion_clear H|].
	assumption.
Qed.

Local Lemma CBN_struct_tl : forall b0 b1 n,
	CBN_st (b1 :: n) -> CBN_st (b0 :: b1 :: n).
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

Local Lemma BN_inc_non_empty : forall (n : BN),
	exists b tn, b :: tn = BN_inc n.
Proof.
	intros n.
	{	destruct n as [|b tn]; [|destruct b].
	+	exists 1, []; reflexivity.
	+	exists 1, tn; reflexivity.
	+	exists 0, (BN_inc tn); reflexivity.
	}
Qed.

Local Lemma CBN_inc_struct : forall (n : BN),
	CBN_st n ->
	CBN_st (BN_inc n).
Proof.
	intros n H.
	{	functional induction (BN_inc n).
	+	reflexivity.
	+	destruct t; [discriminate|].
		exact H.
	+	apply IHl in H.
		pose proof (Hinc := BN_inc_non_empty t).
		destruct Hinc as [b Hinc], Hinc as [tn Hinc].
		rewrite <- Hinc in *.
		apply CBN_struct_tl.
		assumption.
	}
Qed.

Local Lemma CBN_double : forall (n : BN),
	BN_canonical n -> BN_canonical (0 :: (BN_inc n)).
Proof.
	intros n H.
	{	induction H.
	+	replace (0 :: BN_inc []) with (BN_inc (BN_inc [])) by reflexivity.
		apply BN_canonical_inc, BN_canonical_inc, BN_canonical_0.
	+	apply BN_canonical_inc, BN_canonical_inc in IHBN_canonical.
		simpl in IHBN_canonical.
		assumption.
	}
Qed.

Local Lemma CBN_struct_equiv : forall (n : BN),
	BN_canonical n <-> CBN_struct true n = true.
Proof.
	intro n.
	{	split; intro H.
	+	{	induction H as [|n H].
		+	reflexivity.
		+	apply CBN_inc_struct.
			assumption.
		}
	+	{	induction n as [|bn tn].
		+	apply BN_canonical_0.
		+	destruct tn; [destruct bn; [discriminate|apply CBN_1]|].
			assert (Ht : CBN_st (b :: tn)) by (destruct bn; assumption).
			apply IHtn in Ht.
			{	destruct Ht, bn.
			+	discriminate.
			+	apply CBN_1.
			+	apply CBN_double.
				assumption.
			+	replace (1 :: BN_inc n) with (BN_inc (0 :: BN_inc n)) by reflexivity.
				apply BN_canonical_inc.
				apply CBN_double.
				assumption.
			}
		}
	}
Qed.

Fixpoint BN_trim n :=
	match n with
	| [] => []
	| 1 :: tl => 1 :: (BN_trim tl)
	| 0 :: tl => match (BN_trim tl) with
		| [] => []
		| r => 0 :: r
		end
	end.

Functional Scheme BN_trim_ind := Induction for BN_trim Sort Prop.

Lemma BN_trim_canonical : forall l, BN_canonical (BN_trim l).
Proof.
	intro l.
	apply CBN_struct_equiv.
	{	functional induction (BN_trim l).
	+	reflexivity.
	+	reflexivity.
	+	rewrite e1 in IHl0.
		apply IHl0.
	+	apply IHl0.
	}
Qed.

(*Local Lemma CBN_cons : forall b n,
	BN_canonical (b :: n) -> BN_canonical n.
Proof.
	intros b n Hn.
	apply CBN_struct_equiv; apply CBN_struct_equiv in Hn.
	{	destruct b.
	+	apply CBN_struct_false.
		assumption.
	+	assumption.
	}
Qed.*)

Fixpoint BN_dec n :=
	match n with
	| [] => []
	| [1] => []
	| 0 :: t => 1 :: (BN_dec t)
	| 1 :: t => 0 :: t
	end.

Functional Scheme BN_dec_ind := Induction for BN_dec Sort Prop.

Lemma BN_inc_dec : forall (n : BN),
	BN_canonical n -> BN_dec (BN_inc n) = n.
Proof.
	intros n Hn.
	apply CBN_struct_equiv in Hn.
	{	functional induction (BN_inc n).
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

Lemma BN_dec_canonical : forall (n : BN),
	BN_canonical n -> BN_canonical (BN_dec n).
Proof.
	intros n Hn.
	destruct Hn; [apply BN_canonical_0|].
	rewrite BN_inc_dec; assumption.
Qed.

Fixpoint BN_sub_aux n m acc :=
	match n, m with
	| [], _ => None
	| 0 :: tn, [] => BN_sub_aux tn [] (0 :: acc)
	| 1 :: tn, [] => Some (rev_append acc (0 :: tn))
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> BN_sub_aux tn tm (0 :: acc)
	| 0 :: tn, 1 :: tm => BN_sub_aux tn tm (1 :: acc)
	| 1 :: tn, 0 :: tm => BN_sub_borrow tn tm (1 :: acc)
	end
with BN_sub_borrow n m acc :=
	match n, m with
	| [], _ => None
	| _, [] => None
	| 1 :: tn , [1] => Some (rev_append acc (0 :: tn))
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> BN_sub_borrow tn tm (1 :: acc)
	| 1 :: tn, 0 :: tm => BN_sub_borrow tn tm (0 :: acc)
	| 0 :: tn, 1 :: tm => BN_sub_aux tn tm (0 :: acc)
	end.

Definition BN_sub n m :=
	match BN_sub_aux n m [] with
	| Some r => BN_trim (BN_inc r)
	| None => []
	end.

Notation "n - m" := (BN_sub n m) : bin_nat_scope.

Lemma BN_sub_canonical : forall n m, BN_canonical (n - m).
Proof.
	intros n m.
	unfold BN_sub.
	destruct (BN_sub_aux n m []); [|apply BN_canonical_0].
	apply BN_trim_canonical.
Qed.
