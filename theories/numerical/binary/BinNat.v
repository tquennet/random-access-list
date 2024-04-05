Require Import Lists.List FunInd .
(*Require Import Init.Nat.*)
Require Import utils.Utils.
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

Definition nat_equiv n m := to_nat n = to_nat m.

Notation "n === m" := (nat_equiv n m) (at level 70, no associativity).

Lemma to_nat_trail_0 : forall n, n ++ [0] === n.
Proof.
	intro n.
	unfold nat_equiv.
	{	induction n as [|bn tn HR]; [|destruct bn]; simpl in *.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	+	rewrite HR.
		reflexivity.
	}
Qed.

Definition zero : t := [].

Fixpoint inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 :: inc t
	end.

Functional Scheme inc_ind := Induction for inc Sort Prop.

Theorem inc_S : forall n, to_nat (inc n) = S (to_nat n).
Proof.
	intro n.
	{	functional induction (inc n); simpl.
	+	reflexivity.
	+	reflexivity.
	+	rewrite IHl.
		rewrite <- !plus_n_O, plus_Sn_m, <- plus_n_Sm.
		reflexivity.
	}
Qed.

Inductive is_canonical : t -> Prop :=
	| canonical_0 : is_canonical []
	| canonical_inc : forall (n : t),
		is_canonical n -> is_canonical (inc n).

Local Lemma canonical_1 : is_canonical [1].
Proof.
	replace [1] with (inc []) by reflexivity.
	apply canonical_inc, canonical_0.
Qed.

(*Lemma canonical_unicity : forall n m,
	is_canonical n -> is_canonical m ->
	to_nat n = to_nat m ->
	n = m.
Proof.
	intros n m Hn.
	generalize dependent m.
	{	induction Hn as [|n Hn HR]; intros m Hm Heq; destruct Hm as [|m Hm].
	+	reflexivity.
	+	rewrite inc_S in Heq.
		discriminate.
	+	rewrite inc_S in Heq.
		discriminate.
	+	f_equal.
		apply HR; [assumption|].
		rewrite !inc_S in Heq.
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

Local Lemma is_canonical_struct_cons : forall b0 b1 n,
	is_canonical_struct (b1 :: n) -> is_canonical_struct (b0 :: b1 :: n).
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

Lemma is_canonical_struct_tl : forall b n, is_canonical_struct (b :: n) -> is_canonical_struct n.
Proof.
	intros b n H.
	{	destruct n.
	+	reflexivity.
	+	destruct b; destruct b0; assumption.
	}
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
		apply is_canonical_struct_cons.
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

Lemma trim_nat : forall l, to_nat (trim l) = to_nat l.
Proof.
	intro l.
	{	functional induction (trim l); simpl.
	+	reflexivity.
	+	rewrite <- IHl0, e1.
		reflexivity.
	+	rewrite <- IHl0, e1.
		reflexivity.
	+	rewrite IHl0.
		reflexivity.
	}
Qed.

Fixpoint dec_aux n :=
	match n with
	| [] => None
	| [1] => Some []
	| 1 :: t => Some (0 :: t)
	| 0 :: t => option_map (fun r => 1 :: r) (dec_aux t)
	end.

Functional Scheme dec_aux_ind := Induction for dec_aux Sort Prop.

Definition dec n := option_default [] (dec_aux n).

(*Lemma nat_inc_dec : forall n, to_nat (dec (inc n)) = to_nat n.
Proof.
	intro n.
	unfold dec.
	{	enough (H : option_map to_nat (dec_aux (inc n)) = Some (to_nat n)).
	+	destruct (dec_aux (inc n)); [|discriminate].
		simpl.
		inversion_clear H.
		reflexivity.
	+	{	functional induction (inc n).
		+	reflexivity.
		+	destruct t0; reflexivity.
		+	simpl.
			destruct (dec_aux (inc t0)); [|discriminate].
			simpl in *.
			inversion_clear IHl.
			reflexivity.
		}
	}
Qed.*)

Lemma inc_dec : forall (n : t),
	is_canonical n -> dec (inc n) = n.
Proof.
	intros n Hn.
	unfold dec.
	enough (forall n, is_canonical n -> dec_aux (inc n) = Some n);
		[apply H in Hn; rewrite Hn; reflexivity|].
	clear n Hn.
	intros n Hn.
	apply is_canonical_struct_equiv in Hn.
	{	functional induction (inc n).
	+	reflexivity.
	+	destruct t0; [discriminate|].
		reflexivity.
	+	simpl.
		destruct t0; [reflexivity|].
		apply IHl in Hn.
		rewrite Hn.
		reflexivity.
	}
Qed.

Lemma dec_aux_None : forall n, dec_aux n = None <-> to_nat n = O.
Proof.
	intro n.
	{	split; intro H; functional induction (dec_aux n); simpl in *.
	+	reflexivity.
	+	destruct (dec_aux t0); [discriminate|].
		rewrite IHo; reflexivity.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	+	apply PeanoNat.Nat.eq_add_0 in H; destruct H as [H _].
		rewrite H in IHo.
		rewrite IHo; reflexivity.
	+	discriminate.
	+	destruct _x; [discriminate|].
		rewrite plus_Sn_m in H.
		discriminate.
	}
Qed.

Theorem dec_pred : forall n,
	to_nat (dec n) = pred (to_nat n).
Proof.
	intros n.
	unfold dec.
	{	functional induction (dec_aux n); simpl in *.
	+	reflexivity.
	+	{	apply option_default_map_inv.
		+	intro eq.
			apply dec_aux_None in eq.
			rewrite eq.
			reflexivity.
		+	intros n eq.
			rewrite eq in IHo.
			simpl in *.
			assert (to_nat t0 <> O)
				by (intro H; apply dec_aux_None in H; rewrite H in eq; discriminate).
			rewrite IHo, <- !plus_n_O, <- plus_Sn_m, <- PeanoNat.Nat.add_1_l.
			rewrite !PeanoNat.Nat.add_pred_r; [|assumption|assumption].
			rewrite PeanoNat.Nat.add_1_l.
			reflexivity.
		}
	+	reflexivity.
	+	reflexivity.
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
	| 0 :: tn, [] => sub_aux tn [] (1 :: acc)
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

Lemma sub_n_O : forall n,
		is_canonical n -> n - [] === n.
Proof.
	intros n Hn.
	unfold sub.
	destruct Hn; [reflexivity|].
	unfold nat_equiv.
	apply is_canonical_struct_equiv in Hn.
	{	enough (H : forall a, option_map to_nat (sub_aux (inc n) [] a)
						 = Some (to_nat (rev_append a n))).
	+	specialize (H []).
		destruct (sub_aux (inc n) [] []); [|discriminate].
		rewrite trim_nat, !inc_S.
		inversion H.
		reflexivity.
	+	{	induction n as [|bn tn HR]; [|destruct bn]; intro a; simpl in *.
		+	rewrite !rev_append_rev.
			rewrite to_nat_trail_0, app_nil_r.
			reflexivity.
		+	reflexivity.
		+	rewrite HR; [|assumption].
			reflexivity.
		}
	}
Qed.

Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.

End Notations.
