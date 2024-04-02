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
Definition t := list Bit.
Definition dt := t.

Notation "0" := Zero.
Notation "1" := One.

Fixpoint to_nat n : nat :=
	match n with
	| [] => O
	| 0 :: t => 2 * (to_nat t)
	| 1 :: t => S (2 * to_nat t)
	end.

Definition zero : t := [].

Fixpoint inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 :: inc t
	end.

Functional Scheme inc_ind := Induction for inc Sort Prop.

Inductive is_canonical : t -> Prop :=
	| canonical_0 : is_canonical []
	| canonical_inc : forall (n : t),
		is_canonical n -> is_canonical (inc n).

Local Lemma canonical_1 : is_canonical [1].
Proof.
	replace [1] with (inc []) by reflexivity.
	apply canonical_inc, canonical_0.
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

Fixpoint is_canonical_struct_fix b n :=
	match n with
	| [] => b
	| 0 :: tn => is_canonical_struct_fix false tn
	| 1 :: tn => is_canonical_struct_fix true tn
	end.

Definition is_canonical_struct n := is_canonical_struct_fix true n = true.

Local Lemma is_canonical_struct_false : forall n,
	is_canonical_struct_fix false n = true -> is_canonical_struct n.
Proof.
	intros n H.
	destruct n; [inversion_clear H|].
	assumption.
Qed.

Local Lemma is_canonical_struct_tl : forall b0 b1 n,
	is_canonical_struct (b1 :: n) -> is_canonical_struct (b0 :: b1 :: n).
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

Local Lemma inc_non_empty : forall (n : t),
	exists b tn, b :: tn = inc n.
Proof.
	intros n.
	{	destruct n as [|b tn]; [|destruct b].
	+	exists 1, []; reflexivity.
	+	exists 1, tn; reflexivity.
	+	exists 0, (inc tn); reflexivity.
	}
Qed.

Local Lemma is_canonical_inc_struct : forall (n : t),
	is_canonical_struct n ->
	is_canonical_struct (inc n).
Proof.
	intros n H.
	{	functional induction (inc n).
	+	reflexivity.
	+	destruct t0; [discriminate|].
		exact H.
	+	apply IHl in H.
		pose proof (Hinc := inc_non_empty t0).
		destruct Hinc as [b Hinc], Hinc as [tn Hinc].
		rewrite <- Hinc in *.
		apply is_canonical_struct_tl.
		assumption.
	}
Qed.

Local Lemma canonical_double : forall (n : t),
	is_canonical n -> is_canonical (0 :: (inc n)).
Proof.
	intros n H.
	{	induction H.
	+	replace (0 :: inc []) with (inc (inc [])) by reflexivity.
		apply canonical_inc, canonical_inc, canonical_0.
	+	apply canonical_inc, canonical_inc in IHis_canonical.
		simpl in IHis_canonical.
		assumption.
	}
Qed.

Local Lemma is_canonical_struct_equiv : forall (n : t),
	is_canonical n <-> is_canonical_struct n.
Proof.
	intro n.
	{	split; intro H.
	+	{	induction H as [|n H].
		+	reflexivity.
		+	apply is_canonical_inc_struct.
			assumption.
		}
	+	{	induction n as [|bn tn].
		+	apply canonical_0.
		+	destruct tn; [destruct bn; [discriminate|apply canonical_1]|].
			assert (Ht : is_canonical_struct (b :: tn)) by (destruct bn; assumption).
			apply IHtn in Ht.
			{	destruct Ht, bn.
			+	discriminate.
			+	apply canonical_1.
			+	apply canonical_double.
				assumption.
			+	replace (1 :: inc n) with (inc (0 :: inc n)) by reflexivity.
				apply canonical_inc.
				apply canonical_double.
				assumption.
			}
		}
	}
Qed.

Fixpoint trim n :=
	match n with
	| [] => []
	| 1 :: tl => 1 :: (trim tl)
	| 0 :: tl => match (trim tl) with
		| [] => []
		| r => 0 :: r
		end
	end.

Functional Scheme trim_ind := Induction for trim Sort Prop.

Lemma trim_canonical : forall l, is_canonical (trim l).
Proof.
	intro l.
	apply is_canonical_struct_equiv.
	{	functional induction (trim l).
	+	reflexivity.
	+	reflexivity.
	+	rewrite e1 in IHl0.
		apply IHl0.
	+	apply IHl0.
	}
Qed.

Fixpoint dec n :=
	match n with
	| [] => []
	| [1] => []
	| 0 :: t => 1 :: (dec t)
	| 1 :: t => 0 :: t
	end.

Functional Scheme dec_ind := Induction for dec Sort Prop.

Lemma inc_dec : forall (n : t),
	is_canonical n -> dec (inc n) = n.
Proof.
	intros n Hn.
	apply is_canonical_struct_equiv in Hn.
	{	functional induction (inc n).
	+ reflexivity.
	+	destruct t0; [discriminate|].
		reflexivity.
	+	simpl.
		destruct t0; [reflexivity|].
		apply IHl in Hn.
		rewrite Hn.
		reflexivity.
	}
Qed.

Lemma dec_canonical : forall (n : t),
	is_canonical n -> is_canonical (dec n).
Proof.
	intros n Hn.
	destruct Hn; [apply canonical_0|].
	rewrite inc_dec; assumption.
Qed.

Fixpoint sub_aux n m acc :=
	match n, m with
	| [], _ => None
	| 0 :: tn, [] => sub_aux tn [] (0 :: acc)
	| 1 :: tn, [] => Some (rev_append acc (0 :: tn))
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> sub_aux tn tm (0 :: acc)
	| 0 :: tn, 1 :: tm => sub_aux tn tm (1 :: acc)
	| 1 :: tn, 0 :: tm => sub_borrow tn tm (1 :: acc)
	end
with sub_borrow n m acc :=
	match n, m with
	| [], _ => None
	| _, [] => None
	| 1 :: tn , [1] => Some (rev_append acc (0 :: tn))
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> sub_borrow tn tm (1 :: acc)
	| 1 :: tn, 0 :: tm => sub_borrow tn tm (0 :: acc)
	| 0 :: tn, 1 :: tm => sub_aux tn tm (0 :: acc)
	end.

Definition sub n m :=
	match sub_aux n m [] with
	| Some r => trim (inc r)
	| None => []
	end.

Notation "n - m" := (sub n m) : bin_nat_scope.

Lemma sub_canonical : forall n m, is_canonical (n - m).
Proof.
	intros n m.
	unfold sub.
	destruct (sub_aux n m []); [|apply canonical_0].
	apply trim_canonical.
Qed.

Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.

End Notations.
