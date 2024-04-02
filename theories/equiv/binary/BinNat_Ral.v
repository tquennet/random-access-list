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

Theorem open_sub_Some : forall (l : @RAL.t A) d n dn dl rdl t dt rl,
		RAL.valid d l -> length dn <= d ->
		(RAL.open l n dn dl = (rdl, Some(t, dt), rl) ->
			(BinNat.sub_aux (RAL.strip l) n dn) = Some(CLBT.dtrace dt ++ 0 :: RAL.strip rl))
		/\ (RAL.open_borrow l n dn dl = (rdl, Some(t, dt), rl) ->
			(BinNat.sub_borrow (RAL.strip l) n dn) = Some(CLBT.dtrace dt ++ 0 :: RAL.strip rl)).
Proof.
	intros l.
	{	induction l as [|bl tl HR]; intros d n dn dl rdl t dt rl Hl Hdn;
			[|destruct bl; (destruct n as [|bn tn]; [|destruct bn])];
			split; intro He; simpl in *;
			apply le_n_S in Hdn as Hsdn.
	+	inversion_clear He.
	+	inversion_clear He.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	pose proof (Hc := RAL.open_borrow_O tl (0 :: dn) (RAL.Zero :: dl)).
		destruct Hc as [crl Hc], Hc as [crdl Hc].
		rewrite Hc in He.
		discriminate.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	inversion He.
		replace dt with (snd (CLBT.open (CLBT.make_zip t0) dn))
			by (apply (f_equal snd) in H1; assumption).
		inversion_clear Hl.
		inversion_clear H.
		{	rewrite (CLBT.open_trace _ d d), !rev_append_rev, app_nil_r.
		+	reflexivity.
		+	apply CLBT.make_zip_valid.
			assumption.
		+	assumption.
		}
	+	pose proof (Hc := RAL.open_borrow_O tl (0 :: dn) (RAL.One t0 :: dl)).
		destruct Hc as [crl Hc], Hc as [crdl Hc].
		rewrite Hc in He.
		discriminate.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	inversion_clear Hl.
		apply (HR (S d)) in He; assumption.
	+	destruct tn; [|inversion_clear Hl; apply (HR (S d)) in He; assumption].
		inversion He.
		replace dt with (snd (CLBT.open (CLBT.make_zip t0) dn))
			by (apply (f_equal snd) in H1; assumption).
		inversion_clear Hl.
		inversion_clear H.
		{	rewrite (CLBT.open_trace _ d d), !rev_append_rev, app_nil_r.
		+	reflexivity.
		+	apply CLBT.make_zip_valid.
			assumption.
		+	assumption.
		}
	}
Qed.

Theorem open_sub_None : forall (l : @RAL.t A) n dn dl rdl rl,
		(RAL.open l n dn dl = (rdl, None, rl) ->
			BinNat.sub_aux (RAL.strip l) n dn = None)
		/\ (RAL.open_borrow l n dn dl = (rdl, None, rl) ->
			BinNat.sub_borrow (RAL.strip l) n dn = None).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dn dl rdl rl;
			destruct n as [|bn tn]; split; intro H; simpl in *.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	apply HR in H.
		assumption.
	+	reflexivity.
	+	destruct bn; apply HR in H; assumption.
	+	destruct bn; apply HR in H; assumption.
	+	discriminate.
	+	reflexivity.
	+	destruct bn; apply HR in H; assumption.
	+	destruct bn; [apply HR in H; assumption|].
		destruct tn; [discriminate|].
		apply HR in H.
		assumption.
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

Theorem drop_sub : forall (l : @RAL.t A) n,
		RAL.is_valid l ->
		RAL.strip (RAL.drop l n) = BinNat.sub (RAL.strip l) n.
Proof.
	intros l n H.
	unfold BinNat.sub, RAL.drop.
	destruct (RAL.open l n [] []) as [p rl] eqn:He, p as [drl zip].
	{	destruct zip as [zip|].
	+	destruct zip as [t dt].
		pose proof (Ho := open_sub_Some l 0 n [] []).
		apply Ho in He; [| assumption | apply le_0_n].
		rewrite trim_strip, RAL.cons_aux_inc_strip, DCLBT_to_RAL_strip, He.
		reflexivity.
	+	pose proof (Ho := open_sub_None l n [] []).
		apply Ho in He.
		rewrite He.
		reflexivity.
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
