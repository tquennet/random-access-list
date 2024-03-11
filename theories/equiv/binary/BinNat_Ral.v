Require Import FunInd.
Require Import numerical.binary.BinNat.
Require Import structure.binary.Ral structure.tree.Clbt.
Require Import utils.Utils.

Require Import Lists.List.
Import ListNotations.
Open Scope bin_nat_scope.

(*	** Theoremes:																*)
(*		RAL_cons_inc : forall l a, size (RAL_cons a l) = BN_inc (size l)		*)
(*		RAL_tail_dec : forall l, VRAL l -> size (RAL_tail l) = BN_dec (size l)	*)
(*	 RAL_discard_sub : forall l n, VBN n -> size (RAL_discard l n) = size l - n	*)
(********************************************************************************)

Section BinNatRal.
Context {A : Type}.

Local Lemma RAL_cons_aux_inc : forall (l : @RAL A) (clbt : CLBT),
	size (Ral.RAL_cons_aux clbt l) = BN_inc (size l).
Proof.
	intro l.
	{	induction l as [| bit t HR]; try destruct bit.
	+	reflexivity.
	+	reflexivity.
	+	intro clbt.
		simpl.
		f_equal.
		apply HR.
	}
Qed.

Theorem RAL_cons_inc : forall (l : RAL) (a : A),
	size (RAL_cons a l) = BN_inc (size l).
Proof.
	intros l a.
	apply RAL_cons_aux_inc.
Qed.

Lemma RAL_size_canonical : forall (l : @RAL A),
	CRAL l -> CBN (size l).
Proof.
	intros l H.
	{	induction H.
	+ apply CBN_0.
	+	rewrite RAL_cons_inc.
		apply CBN_inc.
		assumption. 
	}
Qed.

Theorem RAL_tail_dec : forall (l : @RAL A),
	CRAL l -> size (RAL_tail l) = dec (size l).
Proof.
	intros l Hl.
	{	destruct Hl.
	+	reflexivity.
	+	rewrite RAL_cons_tail, RAL_cons_inc; [|assumption].
		apply RAL_size_canonical in Hl.
		rewrite BinNat_inc_dec; [|assumption].
		reflexivity.
	}
Qed.

Lemma RAL_discard_split_sub : forall (o : option (Ral.RAL_discard_zipper * @RAL A))
	(b : Bit) (n : option BinNat),
	option_map (fun '(_, l) => size l) o = n ->
	option_map (fun '(_, l) => size l) (Ral.RAL_discard_split o b)
		= BinNat.BN_add_bit n b.
Proof.
	intros o b n H.
	{	destruct o as [p|]; [destruct p as [zip l], zip as [c zip], b|]; simpl.
	+	rewrite <- H.		
		destruct l as [|bit tl]; [|destruct bit]; reflexivity.
	+	rewrite <- H.		
		destruct l as [|bit tl]; [|destruct bit]; reflexivity.
	+	rewrite <- H.
		reflexivity.
	}
Qed.

Lemma RAL_BinNat_safe_zero : forall (l : @RAL A),
	size (Ral.RAL_safe_zero l) = BinNat.BN_safe_zero (size l).
Proof.
	intro l.
	destruct l as [|bit tl]; [| destruct bit]; reflexivity.
Qed.

Lemma RAL_discard_aux_sub_nil : forall (l : @RAL A) (dral : Ral.DRAL),
	(option_map (fun '(_, l) => size l) (Ral.RAL_discard_aux l [] dral) =
		BinNat.BN_sub_aux (size l) []
	/\ option_map (fun '(_, l) => size l) (Ral.RAL_discard_borrow l [] dral) =
		BinNat.BN_sub_borrow (size l) []).
Proof.
	intros l.
	{	induction l as [|bit tl HR]; [|destruct bit]; intro dral; simpl; split.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	apply RAL_discard_split_sub.
		apply HR.
	+	reflexivity.
	+	f_equal.
		apply RAL_BinNat_safe_zero.
	}
Qed.

Lemma RAL_discard_aux_sub : forall (l : @RAL A) (n : BinNat) (dral : Ral.DRAL) {d : nat},
	valid_BinNat (S d) n ->
	(option_map (fun '(_, l) => size l) (Ral.RAL_discard_aux l n dral) =
		BinNat.BN_sub_aux (size l) n
	/\ option_map (fun '(_, l) => size l) (Ral.RAL_discard_borrow l n dral) =
		BinNat.BN_sub_borrow (size l) n).
Proof.
	intro l.
	{	induction l as [| bit tl HR]; intros n dral; split; simpl.
	+	reflexivity.
	+	reflexivity.
	+	{	destruct n as [|b tn]; [|destruct b]; destruct bit; simpl; inversion_clear H.
		+	apply RAL_discard_split_sub.
			apply (HR _ _ _ H0).
		+	apply RAL_discard_split_sub.
			apply (HR _ _ _ H0).
		+	apply RAL_discard_split_sub.
			apply RAL_discard_aux_sub_nil.
		+	apply RAL_discard_split_sub.
			apply (HR _ (RAL_Zero :: dral)), proj2 in H0.
			assumption.
		+	simpl; f_equal.
			apply RAL_BinNat_safe_zero.
		+	{	destruct tn; simpl.
			+	f_equal.
				apply RAL_BinNat_safe_zero.
			+	apply RAL_discard_split_sub.
				apply (HR _ (RAL_One c :: dral)), proj1 in H0.
				assumption.
			}
		}
	+	{	destruct n as [|b tn]; [|destruct b]; destruct bit; simpl; inversion_clear H.
		+	apply RAL_discard_split_sub.
			apply (HR _ _ _ H0).
		+	apply RAL_discard_split_sub.
			apply (HR _ _ _ H0).
		+	apply RAL_discard_split_sub.
			apply RAL_discard_aux_sub_nil.
		+	apply RAL_discard_split_sub.
			apply (HR _ (RAL_Zero :: dral)), proj2 in H0.
			assumption.
		+	apply RAL_discard_split_sub.
			apply RAL_discard_aux_sub_nil.
		+	apply RAL_discard_split_sub.
			apply (HR _ (RAL_One c :: dral)), proj2 in H0.
			assumption.
		}
	}
Qed.

Theorem RAL_discard_sub : forall (l : @RAL A) (n : BinNat),
		VBN n -> size (RAL_discard l n) = size l - n.
Proof.
	intros l n H.
	{	destruct n; simpl.
	+	reflexivity.
	+	apply BinNat.valid_BinNat_S in H.
		apply (RAL_discard_aux_sub l _ []), proj1 in H.
		{	destruct Ral.RAL_discard_aux as [p|]; [destruct p as [zip r]|]; simpl in H.
		+	rewrite <- H.
			reflexivity.
		+	rewrite <- H.
			reflexivity.
		}
	}
Qed.
*)

End BinNatRal.