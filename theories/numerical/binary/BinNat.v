Require Import Lists.List FunInd .
Require Import Init.Nat.
Import ListNotations.

Declare Scope bin_nat_scope.
Open Scope bin_nat_scope.

(********************************************************************************)
(*	Notations are defined in bin_nat_scope.										*)
(*	BN == the type of binary numbers.											*)
(*			 CBN == a predicate identifying canonical BinNat					*)
(*					all operations are defined only for canonical BinNat		*)
(*		BN_zero  == the BN representing 0										*)
(*		BN_inc n == the successor of n											*)
(*	**	Unary operator:															*)
(*		BN_to_nat n == n as native coq nat										*)
(*			   BN_dec n == the predecessor of n									*)
(*	**	Binary operators:														*)
(*		 sub n m, n - m == the difference between n and m						*)
(*	** Lemmes:																	*)
(*		BN_inc_valid : forall l, VBN l -> VBN (BN_inc l)						*)
(*		BN_dec_valid : forall l, VBN l -> VBN (BN_dec l)						*)
(*		BN_inc_dec : forall l, VBN l -> VBN d n -> dec (inc n) = n				*)
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

Lemma BN_inc_S : forall (n : BN),
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

Inductive CBN : BN -> Prop :=
	| CBN_0 : CBN []
	| CBN_inc : forall (n : BN),
		CBN n -> CBN (BN_inc n).

Local Lemma CBN_1 : CBN [1].
Proof.
	replace [1] with (BN_inc []) by reflexivity.
	apply CBN_inc, CBN_0.
Qed.

(*Lemma CBN_unicity : forall n m,
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

Lemma CBN_double : forall (n : BN),
	CBN n -> CBN (0 :: (BN_inc n)).
Proof.
	intros n H.
	{	induction H.
	+	replace (0 :: BN_inc []) with (BN_inc (BN_inc [])) by reflexivity.
		apply CBN_inc, CBN_inc, CBN_0.
	+	apply CBN_inc, CBN_inc in IHCBN.
		simpl in IHCBN.
		assumption.
	}
Qed.

Local Lemma CBN_struct_equiv : forall (n : BN),
	CBN n <-> CBN_struct true n = true.
Proof.
	intro n.
	{	split; intro H.
	+	{	induction H as [|n H].
		+	reflexivity.
		+	apply CBN_inc_struct.
			assumption.
		}
	+	{	induction n as [|bn tn].
		+	apply CBN_0.
		+	destruct tn; [destruct bn; [discriminate|apply CBN_1]|].
			assert (Ht : CBN_st (b :: tn)) by (destruct bn; assumption).
			apply IHtn in Ht.
			{	destruct Ht, bn.
			+	discriminate.
			+	apply CBN_1.
			+	apply CBN_double.
				assumption.
			+	replace (1 :: BN_inc n) with (BN_inc (0 :: BN_inc n)) by reflexivity.
				apply CBN_inc.
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

Lemma trim_canonical : forall l, CBN (BN_trim l).
Proof.
Admitted.

Lemma CBN_cons : forall b n,
	CBN (b :: n) -> CBN n.
Proof.
	intros b n Hn.
	apply CBN_struct_equiv; apply CBN_struct_equiv in Hn.
	{	destruct b.
	+	apply CBN_struct_false.
		assumption.
	+	assumption.
	}
Qed.

(*Lemma CBN_last : forall (n : BN),
	CBN n <-> last n 1 = 1.
Proof.
	intros n.
	{	split; intro H.
	+	{	induction H as [| n HCBN HR].
		+ reflexivity.
		+ apply BN_inc_last.
			assumption.
		}
	+	{	induction n as [|b tn HR].
		+	apply CBN_0.
		+
		}
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
	CBN n -> BN_dec (BN_inc n) = n.
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

Lemma BN_dec_inc : forall b n,
	CBN (b :: n) -> b :: n = BN_inc (BN_dec (b :: n)).
Proof.
	intros b n Hbn.
	inversion_clear Hbn.
	rewrite BN_inc_dec; [|assumption].
	reflexivity.
Qed.

Lemma BN_dec_canonical : forall (n : BN),
	CBN n -> CBN (BN_dec n).
Proof.
	intros n Hn.
	destruct Hn; [apply CBN_0|].
	rewrite BN_inc_dec; assumption.
Qed.

Lemma CBN_0_tn : forall tn,
	CBN (0 :: tn) -> exists m, CBN m /\ BN_inc m = tn.
Proof.
	intros tn Htn.
	apply CBN_struct_equiv in Htn.
	destruct tn as [|b tn]; [discriminate|].
	exists (BN_dec (b :: tn)).
	{	split.
	+	apply BN_dec_canonical, CBN_struct_equiv.
		assumption.
	+	rewrite <- BN_dec_inc; [|apply CBN_struct_equiv; assumption].
		reflexivity.
	}
Qed.

Fixpoint BN_sub n m :=
	match n, m with
	| [], _ => []
	| _, [] => n
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> 0 :: (BN_sub tn tm)
	| 0 :: tn, 1 :: tm => 1 :: (BN_sub_borrow tn tm)
	| 1 :: tn, 0 :: tm => 1 :: (BN_sub tn tm)
	end
with BN_sub_borrow n m :=
	match n, m with
	| [], _ => []
	| _, [] => BN_dec n
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> 1 :: (BN_sub_borrow tn tm)
	| 0 :: tn, 1 :: tm => 0 :: (BN_sub_borrow tn tm)
	| 1 :: tn, 0 :: tm => 1 :: (BN_sub tn tm)
	end.

Notation "n - m" := (BN_sub n m) : bin_nat_scope.

(*Lemma BN_sub_aux_n_O : forall n,
	BN_sub_aux n [] = n.
Proof.
	intros n.
	destruct n as [|b tn]; [|destruct b];
		reflexivity.
Qed.

Lemma BN_sub_borrow_n_O : forall n,
	BN_sub_borrow n [] = BN_dec n.
Proof.
	intros n.
	{	functional induction (BN_dec n).
	+	reflexivity.
	+	destruct t; [reflexivity|].
		simpl in *.
		rewrite IHl.
		reflexivity.
	+	reflexivity.
	}
Qed.

Lemma BN_sub_aux_borrow : forall (n m : BN),
	m <? n = true -> CBN n ->
	BN_sub_aux n m = BN_inc (BN_sub_borrow n m).
Proof.
	intros n.
	{	induction n as [|bn tn HRn]; [|destruct bn]; intros m Hlt Hn; simpl.
	+	apply BN_ltb_n_O in Hlt.
		contradiction.
	+	{	destruct m as [| bm tm]; [|destruct bm].
		+	rewrite BN_sub_borrow_n_O.
			apply BN_ltb_n_m_as_inc in Hlt; [|assumption].
			apply CBN_0_tn in Hn as Hm.
			destruct Hm as [m Hm], Hm as [Hm Hmtn].
			rewrite <- Hmtn, BN_inc_dec; [|assumption].
			reflexivity.
		+	apply BN_ltb_cons in Hlt.
			apply CBN_cons in Hn.
			apply HRn in Hlt; [|assumption].
			rewrite Hlt.
			pose proof (Hinc := BN_inc_non_empty (BN_sub_borrow tn tm)).
			destruct Hinc as [b Hinc], Hinc as [tbn Hinc].
			simpl.
			rewrite <- !Hinc.
			reflexivity.
		+	destruct (BN_sub_borrow tn tm); reflexivity.
		}
	+	{	destruct m as [| bm tm]; [|destruct bm].
		+	destruct tn; reflexivity.
		+	destruct (BN_sub_aux tn tm); reflexivity.
		+	apply BN_ltb_cons in Hlt.
			apply CBN_cons in Hn.
			{	destruct tm.
			+	destruct tn; [discriminate|].
				rewrite BN_sub_borrow_n_O.
				unfold BN_inc; fold BN_inc.
				rewrite <- BN_dec_inc; [|assumption].
				reflexivity.
			+	apply HRn in Hlt; [|assumption].
				rewrite Hlt.
				pose proof (Hinc := BN_inc_non_empty (BN_sub_borrow tn (b :: tm))).
				destruct Hinc as [bn Hinc], Hinc as [tbn Hinc].
				simpl.
				rewrite <- !Hinc.
				reflexivity.
			}
		}
	}
Qed.


*)

