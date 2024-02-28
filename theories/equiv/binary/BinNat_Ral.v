Require Import numerical.binary.BinNat.
Require Import structure.binary.Ral structure.tree.Clbt.

Require Import Lists.List.
Import ListNotations.
Open Scope bin_nat_scope.

Section BinNatRal.
Context {A : Type}.

Local Lemma RAL_cons_aux_inc : forall (l : @RAL A) (clbt : CLBT),
	size (Ral.RAL_cons_aux clbt l) = inc (size l).
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
	size (RAL_cons a l) = inc (size l).
Proof.
	intros l a.
	apply RAL_cons_aux_inc.
Qed.

Local Lemma RAL_tail_aux_dec : forall (l : @RAL A) {n : nat},
	valid_RAL n l -> size (snd (Ral.uncons l)) = dec (size l).
Proof.
	intro l.
	{	induction l as [|bit t HR]; intros n Hl;
		[| destruct bit]; inversion_clear Hl.
	+	reflexivity.
	+	specialize (HR (S n)).
		apply HR in H as Hs.
		apply Ral.uncons_valid_lhs in H.
		destruct H as [clbt Hc], Hc as [Hc Heq].
		simpl.
		destruct (Ral.uncons t).
		simpl in *.
		rewrite <- Heq.
		destruct clbt as [|clbtl clbtr]; inversion_clear Hc.
		simpl.
		rewrite Hs.
		reflexivity.
	+	reflexivity.
	+	simpl.
		{	destruct t.
		+	inversion_clear H0.
		+	simpl.
			destruct r; reflexivity.
		}
	}
Qed.

Theorem RAL_tail_dec : forall (l : @RAL A),
	valid_RAL 0 l -> size (RAL_tail l) = dec (size l).
Proof.
	intros l H.
	apply (RAL_tail_aux_dec _ H).
Qed.

Definition is_some {T : Type} (o : option T) :=
	match o with
	| Some _ => true
	| None => false
	end.

Lemma RAL_lookup_aux_nil : forall (l : @RAL A) (b : Bit) (pos : list Bit),
	valid_RAL (length (b :: pos)) l ->
	is_some (Ral.RAL_lookup_aux l [] (b :: pos)) = true
	/\ is_some (Ral.RAL_lookup_borrow l [] (b :: pos)) = true.
Proof.
	intro l.
	{	induction l as [| bit t HR]; intros b pos H; [|destruct bit]; split;
			inversion_clear H.
	+	apply HR.
		assumption.
	+	apply HR.
		assumption.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	}
Qed.

Lemma RAL_lookup_aux_gt : forall (l : @RAL A) (n : BinNat) (b : Bit) (pos : list Bit),
	valid_RAL (length (b :: pos)) l -> valid_BinNat (length (b :: pos)) n ->
	(is_some (Ral.RAL_lookup_aux l n (b :: pos)) = (n <? (size l)))
	/\ (is_some (Ral.RAL_lookup_borrow l n (b :: pos)) = (gt_dec_borrow (size l) n)).
Proof.
	intro l.
	{	induction l as [|bit tl HR]; intros n b pos Hl Hn.
	+	{	split.
		+	reflexivity.
		+	inversion_clear Hl.
		}
	+	simpl.
		{	split; destruct bit, n as [|bn tn]; simpl;
				inversion_clear Hl; inversion_clear Hn.
		+	apply RAL_size_non_zero in H as Hnz.
			rewrite Hnz.
			apply RAL_lookup_aux_nil.
			assumption.
		+	apply HR; assumption.
		+	reflexivity.
		+	simpl; destruct bn, tn; inversion_clear H0;
				reflexivity.
		+	apply RAL_size_non_zero in H0 as Hnz.
			rewrite Hnz.
			apply RAL_lookup_aux_nil.
			assumption.
		+	destruct bn;
				apply HR; assumption.
		+	apply RAL_size_non_zero in H as Hnz.
			rewrite Hnz.
			apply RAL_lookup_aux_nil.
			assumption.
		+	destruct bn; apply HR; assumption.
		+	reflexivity.
		+	destruct bn, tn; inversion_clear H0;
				reflexivity.
		+	destruct tl as [|b2 tl]; [| destruct b2];
				reflexivity.
		+	{	destruct bn; simpl.
			+	apply HR; assumption.
			+	{	destruct tn.
				+	apply RAL_size_non_zero_borrow in H0 as Hnz.
					rewrite Hnz.
					reflexivity.
				+	apply HR; assumption.
				}
			}
		}
	}
Qed.


Theorem RAL_lookup_gt : forall (l : @RAL A) (n : BinNat),
	valid_RAL 0 l -> valid_BinNat 0 n ->
	is_some (RAL_lookup l n) = (n <? (size l)).
Proof.
	intros l n Hl Hn.
	{	destruct l as [| bit lt].
	+	reflexivity.
	+	{	destruct n as [|b tn]; [| destruct b];
				inversion_clear Hl; simpl; inversion_clear Hn.
		+	reflexivity.
		+	apply RAL_lookup_aux_nil.
			assumption.
		+	reflexivity.
		+	destruct tn; inversion_clear H0; reflexivity.
		+	apply RAL_lookup_aux_gt; assumption.
		+	apply RAL_lookup_aux_gt; assumption.
		+	reflexivity.
		+	reflexivity.
		+	apply RAL_size_non_zero in H as Hnz.
			rewrite Hnz.
			apply RAL_lookup_aux_nil.
			assumption.
		+	apply RAL_lookup_aux_gt; assumption.
		+	apply RAL_size_non_zero in H0 as Hnz.
			rewrite Hnz.
			apply RAL_lookup_aux_nil.
			assumption.
		+	apply RAL_lookup_aux_gt; assumption.
		}
	}
Qed.

End BinNatRal.