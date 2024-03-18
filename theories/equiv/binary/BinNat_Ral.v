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
	CRAL l -> size (RAL_tail l) = BN_dec (size l).
Proof.
	intros l Hl.
	{	destruct Hl.
	+	reflexivity.
	+	rewrite RAL_cons_tail, RAL_cons_inc; [|assumption].
		apply RAL_size_canonical in Hl.
		rewrite BN_inc_dec; [|assumption].
		reflexivity.
	}
Qed.

Theorem RAL_discard_sub_O : forall (l : @RAL A) (n : BN)  dl tl,
		RAL_open l n [] [] = (dl, None, tl) -> dl = rev l /\ tl = [].
Proof.
Admitted.

Lemma RAL_discard_sub_aux : forall (el l : @RAL A) (en n : BN) dl t dt tl,
		RAL_open l n (rev (size el - en)) (rev el) = (dl, Some(t, dt), tl) ->
		(size (el ++ l)) - (en ++ n) = BN_inc (DCLBT_trace dt ++ 0 :: size tl).
Proof.
Admitted.

Theorem RAL_discard_sub : forall (l : @RAL A) (n : BN) dl t dt tl,
		RAL_open l n [] [] = (dl, Some(t, dt), tl) ->
		(size l) - n = BN_inc (DCLBT_trace dt ++ 0 :: size tl).
Proof.
Admitted.

End BinNatRal.
