Require Import Lists.List FunInd.
Require Import utils.Utils.
Require numerical.binary.BinNat structure.binary.Ral structure.tree.Clbt.
Import ListNotations.

Module BinNat := numerical.binary.BinNat.
Module CLBT := structure.tree.Clbt.
Module RAL := structure.binary.Ral.
Import BinNat.Notations.

Open Scope bin_nat_scope.

(*	** Theoremes:																*)
(*		RAL_cons_inc : forall l a, size (RAL_cons a l) = BN_inc (size l)		*)
(*		RAL_tail_dec : forall l, VRAL l -> size (RAL_tail l) = BN_dec (size l)	*)
(*	 RAL_discard_sub : forall l n, VBN n -> size (RAL_discard l n) = size l - n	*)
(********************************************************************************)

Section BinNatRal.
Context {A : Type}.

Definition cons_inc_strip := @RAL.cons_inc_strip A.

Theorem trim_strip : forall (l : @RAL.t A), RAL.strip (RAL.trim l) = BinNat.trim (RAL.strip l).
Proof.
	intro l.
	{	induction l, (@RAL.trim A l) using RAL.trim_ind; simpl in *.
	+	reflexivity.
	+	rewrite <- IHl0, e1.
		reflexivity.
	+	rewrite <- IHl0, e1.
		destruct y0; reflexivity.
	+	rewrite IHl0.
		reflexivity.
	}
Qed.

Theorem strip_canonical : forall (l : @RAL.t A),
	RAL.is_canonical l -> BinNat.is_canonical (RAL.strip l).
Proof.
	intros l H.
	{	induction H.
	+	apply BinNat.canonical_0.
	+	rewrite RAL.cons_inc_strip.
		apply BinNat.canonical_inc.
		assumption.
	}
Qed.

Theorem tail_dec : forall (l : @RAL.t A),
	RAL.is_canonical l -> RAL.strip (RAL.tail l) = BinNat.dec (RAL.strip l).
Proof.
	intros l Hl.
	{	destruct Hl.
	+	reflexivity.
	+	rewrite RAL.cons_tail, RAL.cons_inc_strip; [|assumption].
		apply strip_canonical in Hl.
		rewrite BinNat.inc_dec; [|assumption].
		reflexivity.
	}
Qed.

Definition open_sub_map : (@RAL.zip A) -> option BinNat.t
  := option_map (fun '(_, (_, dt), rl) => CLBT.dtrace dt ++ 0 :: RAL.strip rl).

Theorem open_sub_aux : forall l d n dn dl,
		RAL.valid d l -> length dn <= d ->
		(open_sub_map (RAL.open l n dn dl) = BinNat.sub_aux (RAL.strip l) n dn)
		/\ (open_sub_map (RAL.open_borrow l n dn dl) = BinNat.sub_borrow (RAL.strip l) n dn).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; intros d n dn dl Hl Hd;
			[|destruct bl; (destruct n as [|bn tn]; [|destruct bn])];
			split; apply le_n_S in Hd as Hsd; simpl in *.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	inversion_clear Hl.
		apply (HR (S d) [] (1 :: dn)); assumption.
	+	inversion_clear Hl.
		apply (HR (S d) tn (0 :: dn)); assumption.
	+	inversion_clear Hl.
		apply (HR (S d) tn (1 :: dn)); assumption.
	+	inversion_clear Hl.
		apply (HR (S d) tn (1 :: dn)); assumption.
	+	inversion_clear Hl.
		apply (HR (S d) tn (0 :: dn)); assumption.
	+	reflexivity.
	+	pose proof (Hopen := CLBT.open_trace dn d d (CLBT.make_zip t)).
		destruct (CLBT.open (CLBT.make_zip t) dn).
		cbn in Hopen.
		inversion_clear Hl; inversion_clear H.
		{	rewrite Hopen.
		+	rewrite !rev_append_rev, app_nil_r.
			reflexivity.
		+	split; [assumption|apply CLBT.valid_DRoot].
		+	assumption.
		}
	+	inversion_clear Hl.
		apply (HR (S d) tn (1 :: dn)); assumption.
	+	inversion_clear Hl.
		apply (HR (S d) tn (0 :: dn)); assumption.
	+	{	destruct tn; simpl in *.
		+	pose proof (Hopen := CLBT.open_trace dn d d (CLBT.make_zip t)).
			destruct (CLBT.open (CLBT.make_zip t) dn).
			cbn in Hopen.
			inversion_clear Hl; inversion_clear H.
			{	rewrite Hopen.
				+	rewrite !rev_append_rev, app_nil_r.
					reflexivity.
				+	split; [assumption|apply CLBT.valid_DRoot].
				+	assumption.
			}
		+	inversion_clear Hl.
			apply (HR (S d) (b :: tn) (0 :: dn)); assumption.
		}
	+	inversion_clear Hl.
		apply (HR (S d) tn (1 :: dn)); assumption.
	}
Qed.

Lemma DCLBT_to_RAL_strip : forall dt (l : @RAL.t A),
		RAL.strip (RAL.DCLBT_to_RAL l dt) = CLBT.dtrace dt ++ 0 :: (RAL.strip l).
Proof.
	intros dt l.
	{	induction dt as [| dt HR t| t dt HR]; simpl.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	+	rewrite HR.
		reflexivity.
	}
Qed.

Theorem drop_sub_strip : forall (l : @RAL.t A) n,
		RAL.is_valid l ->
		RAL.strip (RAL.drop l n) = BinNat.sub (RAL.strip l) n.
Proof.
	intros l n H.
	unfold BinNat.sub, RAL.drop.
	pose proof (Hopen := open_sub_aux l 0 (BinNat.trim n) [] []).
	destruct Hopen as [_ Hopen]; [assumption| apply le_n|].
	{	destruct (RAL.open_borrow l (BinNat.trim n) [] []);
			destruct (BinNat.sub_borrow (RAL.strip l) (BinNat.trim n) []);
			simpl in *.
	+	destruct p as [p rl], p as [rdl zip], zip as [t dt].
		inversion_clear Hopen.
		rewrite trim_strip, RAL.cons_aux_inc_strip, DCLBT_to_RAL_strip.
		reflexivity.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	}
Qed.

Theorem create_strip : forall n (a : A), RAL.strip (RAL.create n a) = n.
Proof.
	intros n a.
	unfold RAL.create.
	{	induction n, (CLBT.singleton a), (RAL.create_aux n (CLBT.singleton a))
			using RAL.create_aux_ind
			; simpl in *.
	+	reflexivity.
	+	rewrite IHl.
		reflexivity.
	+	rewrite IHl.
		reflexivity.
	}
Qed.

Lemma RAL_create_canonical : forall n (a : A),
		BinNat.is_canonical n ->
		RAL.is_canonical (RAL.create n a).
Proof.
	intros n a Hn.
	apply RAL.is_canonical_struct_equiv.
	apply BinNat.is_canonical_struct_equiv in Hn.
	{	split.
	+	apply RAL.create_valid.
	+	rewrite create_strip.
		assumption.
	}
Qed.

End BinNatRal.
