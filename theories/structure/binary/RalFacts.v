Require Import structure.binary.Ral equiv.binary.BinNat_Ral numerical.binary.BinNat.

Section Ral.

Context {A : Type}.

Section open.

Notation open_borrow := (@open_borrow A).
Notation dec_zip := (@dec_zip A).

Lemma open_aux_borrow_inc : forall l n dbn dral,
		BinNat.is_canonical_struct n ->
		open_aux l (BinNat.inc n) dbn dral = open_borrow l n dbn dral.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral Hn;
			(destruct n as [|bn tn];
		 	 	[|destruct bn; apply BinNat.is_canonical_struct_tl in Hn as Htn]);
			try reflexivity.
	+	apply HR; assumption.
	+	destruct tn as [|bn tn]; [discriminate|].
		reflexivity.
	+	apply HR; assumption.
	}
Qed.

Lemma open_aux_dt_true : forall l n dbn dral zip dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		(open_borrow l n dbn dral = Some zip ->
			open_borrow l n dd dral = dec_zip zip)
		/\ (open_aux l n dbn dral = Some zip ->
			open_aux l n dd dral = dec_zip zip).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral zip dd Hdd;
			assert (Hsdd : forall b, BinNat.dt_dec (b :: dbn) = (true, b :: dd))
				by (intro b; simpl; rewrite Hdd; destruct b; reflexivity);
			(destruct n as [|bn tn]; [|destruct bn]); split; intro H; simpl in *;
			try discriminate.
	+	specialize (Hsdd 1).
		apply (HR [] (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	specialize (Hsdd 0).
		apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
	+	specialize (Hsdd 0).
		apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	inversion_clear H.
		unfold dec_zip; simpl.
		rewrite Hdd.
		reflexivity.
	+	specialize (Hsdd 0).
		apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	{	destruct tn as [|bn tn].
		+	inversion_clear H.
			unfold dec_zip; simpl.
			rewrite Hdd.
			reflexivity.
		+	specialize (Hsdd 0).
			apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
		}
	}
Qed.


Lemma open_aux_inc : forall l n dbn dral dd zip,
		BinNat.is_canonical_struct n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		(open_borrow l n dbn dral = Some zip ->
			open_borrow l (BinNat.inc n) dd dral = dec_zip zip)
		/\ (open_aux l n dbn dral = Some zip ->
			open_borrow l n dd dral = dec_zip zip).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral dd zip Hn Hdd;
			(destruct n as [|bn tn]; [|destruct bn;
				apply BinNat.is_canonical_struct_tl in Hn as Htn]);
			split ; intro H; simpl in *;
			assert (BinNat.dt_dec (1 :: dbn) = (true, 0 :: dd))
				by (simpl; rewrite Hdd; reflexivity);
			assert (BinNat.dt_dec (0 :: dbn) = (false, 1 :: dd))
				by (simpl; rewrite Hdd; reflexivity);
			try discriminate.
	+	apply (open_aux_dt_true tl [] (1 :: dbn)); assumption.
	+	apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	apply (HR tn (0 :: dbn)); assumption.
	+	apply (HR tn (0 :: dbn)); assumption.
	+	apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	inversion_clear H.
		unfold dec_zip; simpl.
		rewrite Hdd.
		reflexivity.
	+	apply (HR tn (0 :: dbn)); assumption.
	+	apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	{	destruct tn as [|bn tn].
		+	inversion_clear H.
			unfold dec_zip; simpl.
			rewrite Hdd.
			reflexivity.
		+	apply (HR (bn :: tn) (0 :: dbn)); assumption.
		}
	}
Qed.



Lemma open_aux_None : forall l n dbn1 dbn2 dral,
		(open_borrow l n dbn1 dral = None -> open_borrow l n dbn2 dral = None)
		/\ (open_aux l n dbn1 dral = None -> open_aux l n dbn2 dral = None).
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn1 dbn2 dral ;
			(destruct n as [|bn tn]; [|destruct bn]);
			split; intro H; simpl in *; try reflexivity.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	discriminate.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	destruct tn; [discriminate|].
		apply (HR _ (0 :: dbn1)); assumption.
	}
Qed.

Lemma open_aux_inc_None : forall l n dbn1 dbn2 dral ,
		BinNat.is_canonical_struct n ->
		(open_borrow l n dbn1 dral = None -> open_borrow l (BinNat.inc n) dbn2 dral = None)
		/\ (n <> [] -> open_aux l n dbn1 dral = None -> open_borrow l n dbn2 dral = None).
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn1 dbn2 dral Hn;
			(destruct n as [|bn tn]; [|destruct bn;
				apply BinNat.is_canonical_struct_tl in Hn as Htn]);
			(split; [|intro He]; intro H); simpl in *; try reflexivity.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	contradiction.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR tn (0 :: dbn1)); assumption.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	discriminate.
	+	contradiction.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply (HR _ (0 :: dbn1)); assumption.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	destruct tn as [|bn tn]; [discriminate|].
		apply (HR (bn :: tn) (0 :: dbn1)); [assumption|discriminate|assumption].
	}
Qed.

Lemma open_inc : forall l n,
		BinNat.is_canonical n ->
		open l (BinNat.inc n) = option_join dec_zip (open l n).
Proof.
	intros l n Hn.
	apply BinNat.is_canonical_equiv in Hn.
	unfold open.
	pose proof (Hnone := proj1 (open_aux_inc_None l n [] [] [] Hn)).
	pose proof (Hsome := open_aux_inc l n [] [] []).
	{	destruct open_borrow as [zip|].
	+	specialize (Hsome zip Hn eq_refl).
		apply proj1 in Hsome.
		apply Hsome; reflexivity.
	+	rewrite Hnone; reflexivity.
	}
Qed.

End open.

Section scatter.

Lemma scatter_lookup : forall dn t tl,
		CLBT.is_valid (length dn) t ->
		fst (scatter t tl dn) = CLBT.Leaf (CLBT.lookup t (BinNat.complement dn)).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; intros t tl Ht;
			inversion_clear Ht; simpl.
	+	reflexivity.
	+	destruct bn; apply HR; assumption.
	}
Qed.

Lemma scatter_empty_zeroes : forall n t, snd (scatter t empty (repeat 0 n)) = empty.
Proof.
	intro n.
	{	induction n as [|n HR]; intro t; simpl.
	+	reflexivity.
	+	apply HR.
	}
Qed.
Lemma scatter_zeroes : forall n t l,
		l <> [] ->
		snd (scatter t l (repeat 0 n)) = (repeat Zero n) ++ l.
Proof.
	intro n.
	{	induction n as [|n HR]; intros t l He; simpl.
	+	reflexivity.
	+	rewrite app_comm_cons, repeat_cons, <- app_assoc.
		destruct l; [contradiction|].
		apply HR.
		discriminate.
	}
Qed.

Lemma scatter_cons_zero_aux : forall n k t l r,
		CLBT.is_valid n t ->
		cons_aux t l = (repeat Zero k) ++ r ->
		(uncurry cons_aux) (scatter t l (repeat 1 n)) = (repeat Zero (n + k)) ++ r.
Proof.
	intros n.
	{	induction n as [|n HR]; intros k t l r Ht; inversion_clear Ht; intro Hc; simpl in *.
	+	assumption.
	+	rewrite app_comm_cons, repeat_cons, <- app_assoc.
		apply HR; [assumption|].
		rewrite app_assoc, <- repeat_cons.
		simpl.
		rewrite <- Hc.
		reflexivity.
	}
Qed.
Lemma scatter_cons_zero : forall n t tl,
		CLBT.is_valid n t ->
		(uncurry cons_aux) (scatter t (safe_zero tl) (repeat 1 n)) = (repeat Zero n) ++ [One t] ++ tl.
Proof.
	intros n t tl Ht.
	rewrite (plus_n_O n) at 2.
	{	apply scatter_cons_zero_aux.
	+	assumption.
	+	destruct tl; reflexivity.
	}
Qed.

Lemma scatter_dec_aux : forall dn tl t dd,
		is_canonical tl ->
		CLBT.is_valid (length dn) t ->
		BinNat.dt_dec dn = (true, dd) ->
		tail ((uncurry cons_aux) (scatter t tl dn)) = (uncurry cons_aux) (scatter t tl dd).
Proof.
	intros dn.
	{	induction dn as [|bn tdn HR]; [|destruct bn];
			intros tl t dd Htl Ht Hdd; simpl in *.
	+	discriminate.
	+	destruct BinNat.dt_dec as [b tdd], b; [|discriminate].
		inversion_clear Hdd; simpl.
		inversion_clear Ht; simpl.
		apply safe_zero_canonical in Htl.
		apply HR; [assumption..|reflexivity].
	+	pose proof (Hz := BinNat.dt_dec_zero tdn).
		pose proof (Hl := BinNat.dt_dec_length tdn).
		apply BinNat.one_canonical in Htl.
		{	destruct BinNat.dt_dec as [b tdd], b.
		+	inversion_clear Hdd; simpl.
			inversion_clear Ht; simpl.
			apply HR; [assumption..|reflexivity].
		+	specialize (Hz _ eq_refl).
			specialize (Hl _ _ eq_refl).
			inversion_clear Hdd; simpl.
			inversion_clear Ht; simpl.
			rewrite (proj1 Hz), (proj2 Hz).
			rewrite (scatter_cons_zero (length tdd)); [|rewrite <- Hl; assumption].
			pose proof (Hzs := scatter_zeroes (length tdn) r (One l :: tl)).
			pose proof (Hc := scatter_canonical
								  (repeat 0 (length tdn)) r (One l :: tl) Htl).
			destruct scatter as [st sr]; simpl in *.
			unfold tail.
			rewrite uncons_cons, Hzs, Hl; [reflexivity|discriminate|assumption].
		}
	}
Qed.

End scatter.

Theorem drop_zero : forall l,
		is_well_formed l ->
		drop l [] = l.
Proof.
	intros l Hl.
	destruct Hl as [Hvl Hsl].
	unfold drop.
	pose proof (Hoz := open_zero l).
	pose proof (Hv := open_valid l []).
	pose proof (Hozn := open_zero_None _ Hsl).
	pose proof (Hz := open_zipper l []).
	destruct open as [zip|]; [|rewrite Hozn; reflexivity].
	specialize (Hoz zip eq_refl).
	specialize (Hv zip Hvl eq_refl).
	specialize (Hz zip eq_refl).
	destruct Hv as [_ _ Ht _].
	unfold is_zipper in Hz.
	destruct zip as [tl dl t dn], Hoz as [Hdl Hnb]; simpl in *.
	pose proof (Hsc := scatter_cons_zero (length dl) t tl Ht).
	rewrite Hnb.
	destruct scatter as [st sl]; simpl in *.
	rewrite <- rev_repeat, <- Hdl, <- rev_append_rev, <- Hz in Hsc.
	assumption.
Qed.

Theorem drop_inc : forall l n,
		is_well_formed l -> BinNat.is_canonical n ->
		tail (drop l n) = drop l (BinNat.inc n).
Proof.
	intros l n Hl Hn.
	destruct Hl as [Hvl Hl].
	unfold drop.
	unfold is_canonical, strip in Hl.
	pose proof (Hv := open_valid l n).
	pose proof (Hi := open_inc l n Hn).
	pose proof (Hz := open_zipper l n).
	destruct (open l n) as [zip|]; rewrite Hi; [simpl|reflexivity].
	specialize (Hz _ eq_refl); unfold is_zipper in Hz.
	destruct (Hv _ Hvl eq_refl) as [Hvtl Hvdl Ht Hlen].
	destruct zip as [tl dl t nb]; simpl in *.
	rewrite <- Hlen in Ht.
	rewrite Hz, rev_append_rev, map_app in Hl.
	apply BinNat.is_canonical_app, BinNat.is_canonical_tl in Hl.
	unfold dec_zip; simpl.
	pose proof (Hsd := scatter_dec_aux nb (safe_zero tl) t).
	pose proof (Hdz := BinNat.dt_dec_zero nb).
	pose proof (Hdlen := BinNat.dt_dec_length nb).
	{	destruct BinNat.dt_dec as [b tdd], b; simpl in *.
	+	assert (Hpsl : is_canonical (safe_zero tl))
			by (apply safe_zero_canonical; assumption).
		rewrite (Hsd _ Hpsl Ht eq_refl).
		reflexivity.
	+	specialize (Hdz _ eq_refl).
		rewrite (proj1 Hdz), (proj2 Hdz).
		pose proof (Hnone := open_borrow_zero_None tl
								 (1 :: repeat 1 (length tdd)) (One t :: dl) Hl).
		pose proof (Hsome := open_borrow_zero tl (1 :: repeat 1 (length tdd)) (One t :: dl)).
		pose proof (Hzip := open_decomp_aux tl [] (1 :: repeat 1 (length tdd)) (One t :: dl)).
		pose proof (Hv2 := open_aux_valid tl [] (1 :: repeat 1 (length tdd)) (One t :: dl)).
		{	destruct open_borrow as [zip|].
		+	destruct (Hsome _ eq_refl) as [Hdl Hnb].
			specialize (Hzip zip); apply proj2 in Hzip; specialize (Hzip eq_refl).
			specialize (Hdlen _ _ eq_refl).
			simpl in Hv2.
			rewrite <- Hdlen, repeat_length in Hv2.
			destruct (Hv2 zip) as [_ _ Hvt2 Hlen2];
				[right;reflexivity|rewrite Hlen; assumption| apply valid_DCons;
				[apply valid_BIT_One; assumption|rewrite Hlen; assumption]|].				
			destruct zip as [ztl zdl zt znb]; simpl in *.
			rewrite <- (repeat_app 1 _ (S (length tdd))) in Hnb.
			apply (f_equal (@length BinNat.Bit)) in Hnb as Hnlen.
			rewrite repeat_length in Hnlen.
			rewrite Hdl, !rev_append_rev, rev_app_distr, <- app_assoc in Hzip.
			simpl in Hzip.
			rewrite <- app_assoc in Hzip.
			apply app_inv_head in Hzip.
			inversion Hzip.
			rewrite Hnb, rev_repeat.
			assert (He : repeat Zero (length zdl - S (length dl)) ++ One zt :: ztl <> [])
				by (intro H; apply eq_sym, app_cons_not_nil in H; contradiction).
			destruct (repeat Zero (length zdl - S (length dl)) ++ One zt :: ztl) eqn:Hb;
				[contradiction|simpl; rewrite <- Hb].
			pose proof (Hzeroes := scatter_zeroes (length nb) t
				(Zero :: repeat Zero (length zdl - S (length dl)) ++ One zt :: ztl)).
			destruct (scatter t _ (repeat 0 (length nb))); simpl in *.
			assert (Htl : BinNat.is_canonical (map strip_aux tl)) by assumption.
			rewrite H0, rev_repeat, map_app in Htl.
			apply BinNat.is_canonical_app in Htl.
			inversion_clear Htl.
			simpl in Hl.
			unfold tail; rewrite Hzeroes, uncons_cons;
			  [|unfold is_canonical, strip; rewrite app_comm_cons, !map_app, app_assoc; apply BinNat.canonical_pos, BinNat.app_is_positive; assumption |discriminate].
			assert (forall {A : Type} (e : A) n, e :: repeat e n = repeat e (S n)) by reflexivity.
			rewrite app_comm_cons, app_assoc, H1, <- repeat_app,
				Nat.add_comm, Nat.add_succ_comm, Hdlen.
			apply eq_sym, scatter_cons_zero.
			rewrite <- Hnlen, Hlen2.
			assumption.
		+	rewrite Hnone; [|reflexivity].
			pose proof (Hsez := scatter_empty_zeroes (length nb) t).
			destruct (scatter t (safe_zero empty)).
			simpl in *.
			rewrite Hsez.
			unfold tail; rewrite uncons_cons; [reflexivity|apply BinNat.canonical_0].
		}
	}
Qed.

Theorem drop_as_tail : forall l n,
	 	is_well_formed l ->
		BinNat.is_canonical n ->
		drop l n = fun_pow tail (BinNat.to_nat n) l.
Proof.
	intros l n Hl Hn.
	revert l Hl.
	{	induction Hn as [|n Hn HR] using BinNat.canonical_induction; intros l Hl; simpl.
	+	apply drop_zero.
		assumption.
	+	rewrite BinNat.inc_S;simpl.
		rewrite <- fun_pow_comm.
		rewrite <- HR; [|assumption].
		apply eq_sym, drop_inc; assumption.
	}
Qed.

(*
Theorem lookup_none : forall (l : @RAL.t A) n,
		RAL.is_canonical l -> BinNat.is_canonical n ->
		(RAL.strip l) >? n = false -> RAL.lookup l n = None.
Proof.
	intros l n Hl Hn H.
	unfold RAL.lookup in *.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply RAL.is_canonical_struct_equiv in Hl.
	destruct Hl as [_ Hl].
	pose proof (Hgs := BinNat.gtb_decomp_equiv (RAL.strip l) n Hl Hn).
	pose proof (Hco := open_gtb l n).
	{	destruct RAL.open, (BinNat.gtb_decomp (RAL.strip l) n).
	+	rewrite H in Hgs.
		discriminate.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	}
Qed.
 *)
(*
Theorem update_failure : forall l n (a : A),
		is_well_formed l -> BinNat.is_canonical n ->
		(to_bin l) >? n = false -> update l n a = None.
Admitted.

Proof.
	intros l n a Hl Hn H.
	unfold RAL.update in *.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply RAL.is_canonical_struct_equiv in Hl.
	destruct Hl as [_ Hl].
	pose proof (Hgs := BinNat.gtb_decomp_equiv (RAL.strip l) n Hl Hn).
	pose proof (Hco := open_gtb l n).
	{	destruct RAL.open, (BinNat.gtb_decomp (RAL.strip l) n).
	+	rewrite H in Hgs.
		discriminate.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	}
Qed.
*)


Theorem lookup_drop : forall l n,
		is_well_formed l ->
		lookup l n = head (drop l n).
Proof.
	intros l n Hl.
	destruct Hl as [Hvl Hl].
	unfold lookup, drop.
	pose proof (Hv := open_valid l n).
	pose proof (Hz := open_zipper l n).
	destruct (open l n) as [zip|]; [|reflexivity].
	specialize (Hv zip Hvl eq_refl).
	unfold is_canonical, strip in Hl.
	rewrite (Hz _ eq_refl), rev_append_rev, map_app in Hl.
	apply BinNat.is_canonical_app, BinNat.is_canonical_tl, safe_zero_canonical in Hl.
	destruct Hv as [_ _ Ht Hlen].
	destruct zip as [tl dl t an]; simpl in *.
	rewrite <- Hlen in Ht.
	pose proof (CLBT.open_lookup t an Ht).
	destruct CLBT.open.
	pose proof (Hslcan := scatter_canonical an t (safe_zero tl) Hl).
	pose proof (Hsl := scatter_lookup an t (safe_zero tl) Ht).
	destruct scatter; simpl in *.
	rewrite Hsl.
	symmetry.
	apply head_cons.
	assumption.
Qed.

Theorem lookup_zero : forall l,
		is_well_formed l ->
		lookup l [] = head l.
Proof.
	intros l Hl.
	pose proof (BinNat.canonical_0).
	rewrite lookup_drop, drop_as_tail; [|assumption..].
	reflexivity.
Qed.

Theorem lookup_inc : forall l n,
	 	is_well_formed l ->
		BinNat.is_canonical n ->
		lookup l (BinNat.inc n) = lookup (tail l) n.
Proof.
	intros l n Hl Hn.
	apply BinNat.inc_positive in Hn as Hin.
	apply BinNat.canonical_pos in Hin.
	apply tail_well_formed in Hl as Htl.
	rewrite !lookup_drop, !drop_as_tail; [|assumption..].
	rewrite BinNat.inc_S.
	reflexivity.
Qed.

Theorem comprehension : forall l0 l1,
		is_well_formed l0 -> is_well_formed l1 ->
		(forall n, BinNat.is_canonical n -> lookup l0 n = lookup l1 n) ->
		l0 = l1.
Proof.
	intros l0 l1 Hl0.
	revert l1.
	{	induction Hl0 as [|a l0 Hl0 HR] using well_formed_induction; intros l1 Hl1 H;
			destruct Hl1 as [|b l1 Hl1] using well_formed_destruct; simpl.
	+	reflexivity.
	+	specialize (H _ BinNat.canonical_0).
		apply proj2 in Hl1 as Hsl1.
		apply (cons_well_formed b) in Hl1 as Hcl1.
		pose proof (empty_well_formed).
		rewrite !lookup_zero, head_cons in H; [|assumption..].
		discriminate.
	+	specialize (H _ BinNat.canonical_0).
		apply proj2 in Hl0 as Hsl0.
		apply (cons_well_formed a) in Hl0 as Hcl0.
		pose proof (empty_well_formed).
		rewrite !lookup_zero, head_cons in H; [|assumption..].
		discriminate.
	+	pose proof (H0 := H _ BinNat.canonical_0).
		apply proj2 in Hl0 as Hcl0.
		apply proj2 in Hl1 as hcl1.
		pose proof (cons_well_formed a _ Hl0).
		pose proof (cons_well_formed b _ Hl1).
		rewrite !lookup_zero, !head_cons in H0; [|assumption..].
		inversion_clear H0.
		f_equal.
		apply HR; [assumption|].
		intros n Hn.
		apply BinNat.inc_positive in Hn as Hin.
		apply BinNat.canonical_pos in Hin.
		specialize (H _ Hin).
		rewrite !lookup_inc in H; [|assumption..].
		rewrite !tail_cons in H; [|assumption..].
		assumption.
	}
Qed.

End Ral.
