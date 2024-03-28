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

Definition RAL_cons_inc := @RAL_cons_inc A.

Theorem RAL_trim_size : forall (l : @RAL A), size (RAL_trim l) = BN_trim (size l).
Proof.
	intro l.
	{	functional induction (RAL_trim l); simpl in *.
	+	reflexivity.
	+	rewrite <- IHl0, e1.
		reflexivity.
	+	rewrite <- IHl0, e1.
		destruct y0; reflexivity.
	+	rewrite IHl0.
		reflexivity.
	}
Qed.

Theorem RAL_size_canonical : forall (l : @RAL A),
	CRAL l -> BN_canonical (size l).
Proof.
	intros l H.
	{	induction H.
	+	apply BN_canonical_0.
	+	rewrite RAL_cons_inc.
		apply BN_canonical_inc.
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

Theorem RAL_open_sub_Some : forall (l : @RAL A) d n dn dl rdl t dt rl,
		valid_RAL d l -> length dn <= d ->
		(RAL_open l n dn dl = (rdl, Some(t, dt), rl) ->
			(BN_sub_aux (size l) n dn) = Some(DCLBT_trace dt ++ 0 :: size rl))
		/\ (RAL_open_borrow l n dn dl = (rdl, Some(t, dt), rl) ->
			(BN_sub_borrow (size l) n dn) = Some(DCLBT_trace dt ++ 0 :: size rl)).
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
	+	pose proof (Hc := RAL_open_borrow_O tl (0 :: dn) (RAL_Zero :: dl)).
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
		replace dt with (snd (CLBT_open (CLBT_make_zip c) dn))
			by (apply (f_equal snd) in H1; assumption).
		inversion_clear Hl.
		inversion_clear H.
		{	rewrite (CLBT_open_trace _ d d), !rev_append_rev, app_nil_r.
		+	reflexivity.
		+	apply CLBT_make_zip_valid.
			assumption.
		+	assumption.
		}
	+	pose proof (Hc := RAL_open_borrow_O tl (0 :: dn) (RAL_One c :: dl)).
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
		replace dt with (snd (CLBT_open (CLBT_make_zip c) dn))
			by (apply (f_equal snd) in H1; assumption).
		inversion_clear Hl.
		inversion_clear H.
		{	rewrite (CLBT_open_trace _ d d), !rev_append_rev, app_nil_r.
		+	reflexivity.
		+	apply CLBT_make_zip_valid.
			assumption.
		+	assumption.
		}
	}
Qed.

Theorem RAL_open_sub_None : forall (l : @RAL A) n dn dl rdl rl,
		(RAL_open l n dn dl = (rdl, None, rl) -> BN_sub_aux (size l) n dn = None)
		/\ (RAL_open_borrow l n dn dl = (rdl, None, rl) -> BN_sub_borrow (size l) n dn = None).
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

Lemma RAL_DCLBT_to_RAL : forall dt (l : @RAL A),
		size (Ral.DCLBT_to_RAL l dt) = DCLBT_trace dt ++ 0 :: (size l).
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

Theorem RAL_discard_sub : forall (l : @RAL A) n,
		VRAL l ->
		size (RAL_discard l n) = BN_sub (size l) n.
Proof.
	intros l n H.
	unfold BN_sub, RAL_discard.
	destruct (RAL_open l n [] []) as [p rl] eqn:He, p as [drl zip].
	{	destruct zip as [zip|].
	+	destruct zip as [t dt].
		pose proof (Ho := RAL_open_sub_Some l 0 n [] []).
		apply Ho in He; [| assumption | apply le_0_n].
		rewrite RAL_trim_size, Ral.RAL_cons_aux_inc, RAL_DCLBT_to_RAL, He.
		reflexivity.
	+	pose proof (Ho := RAL_open_sub_None l n [] []).
		apply Ho in He.
		rewrite He.
		reflexivity.
	}
Qed.

Theorem RAL_create_size : forall n (a : A), size (RAL_create n a) = n.
Proof.
	intros n a.
	unfold RAL_create.
	{	functional induction (RAL_create_aux n (singleton a)); simpl in *.
	+	reflexivity.
	+	rewrite IHl.
		reflexivity.
	+	rewrite IHl.
		reflexivity.
	}
Qed.

Lemma RAL_create_canonical : forall n (a : A), BN_canonical n -> CRAL (RAL_create n a).
Proof.
	intros n a Hn.
	apply CRAL_struct_equiv.
	apply BinNat.CBN_struct_equiv in Hn.
	{	split.
	+	apply RAL_create_valid.
	+	rewrite RAL_create_size.
		assumption.
	}
Qed.

End BinNatRal.
