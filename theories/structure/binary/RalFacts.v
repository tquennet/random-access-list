Require Import numerical.Num numerical.binary.BinNat structure.binary.Ral
	utils.Utils Lists.List.
Import ListNotations.
Import BinNat.Notations.

Section Ral.

Context {A : Type}.
Notation RAL := (@Ral.t A).

Lemma uncons_cons : forall (l : RAL) clbt, is_canonical l ->
		uncons (Ral.cons_tree clbt l) = Some (clbt, l).
Proof.
	intros l clbt Hc.
	inversion Hc as [? Hp H|H]; [|destruct l; [reflexivity|discriminate]].
	revert clbt.
	clear H Hc.

	{	induction l as [|tl HR bl]; [|destruct bl]; intros clbt; simpl.
	+	reflexivity.
	+	destruct tl; [inversion_clear Hp as [| |? H]; inversion_clear H|].
		reflexivity.
	+	rewrite to_bin_snoc in Hp.
		apply is_positive_tl in Hp.
		inversion Hp as [? Hptl| H]; [|destruct tl; [reflexivity|discriminate]].
		rewrite (HR Hptl); simpl.
		reflexivity.
	}
Qed.

Lemma tl_cons : forall (l : RAL) (a : A),
	is_canonical l -> Ral.tl (Ral.cons a l) = Some l.
Proof.
	intros l a H.
	unfold Ral.tl, Ral.cons.
	rewrite uncons_cons; [reflexivity|assumption].
Qed.

Lemma cons_uncons : forall l : RAL, option_lift (fun '(a, r) => Ral.cons_tree a r = l) (uncons l).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; simpl.
	+	apply I.
	+	eapply lift_bind_conseq, HR; simpl.
		intros x Hx.
		destruct x as [a r], a; [apply I|]; simpl.
		rewrite Hx.
		reflexivity.
	+	destruct tl; reflexivity.
	}
Qed.

Lemma hd_cons : forall (l : RAL) (a : A),
		is_canonical l ->
		Ral.hd (Ral.cons a l) = Some a.
Proof.
	intros l a Hl.
	unfold Ral.hd, Ral.cons.
	rewrite uncons_cons; [|assumption]; simpl.
	reflexivity.
Qed.
Theorem ral_ind : forall (P: RAL -> Prop),
    P Ob ->
    (forall a l, is_well_formed l -> P l -> P (Ral.cons a l)) ->
    forall l, is_well_formed l -> P l.
Proof.	
	intros P H0 Hc l Hl.
	destruct Hl as [Hvl Hsl].
	unfold is_canonical in Hsl.
	remember (to_bin l) as s eqn:Hs.
	revert l Hvl Hs.
	{	induction Hsl as [|s Hsl HR] using BinNat.canonical_induction; intros l Hvl Hs.
	+	destruct l as [|bl tl]; [|discriminate].
		apply H0.
	+	apply BinNat.is_positive_inc in Hsl as Hl.
		rewrite Hs in Hl.
		pose proof (Hin := uncons_positive _ _ Hvl Hl).
		destruct Hin as [a Hin], Hin as [r Hin].
		pose proof (Hcu := cons_uncons l).
		pose proof (Huv := uncons_valid l Hvl).
		pose proof (Huc := uncons_canonical l (mk_wf _ Hvl (is_pos _ Hl))).
		rewrite Hin in Hcu, Huv, Huc; simpl in Hcu, Huv, Huc.
		destruct Huv as [Ha Hr].
		rewrite <- Hcu in Hs |- *.
		rewrite cons_tree_inc in Hs.
		apply inc_inj in Hs; [|assumption..].
		inversion_clear Ha.
		pose proof (r_wf := mk_wf _ Hr Huc).
		apply Hc, HR, Hs; assumption.
	}
Qed.
(*

Lemma open_empty : forall n, open empty n = None.
Proof.
	reflexivity.
Qed.

Lemma open_borrow_zero_None : forall l dn dl,
		is_precanonical l ->
		open_borrow l [] dn dl = None ->
		l = empty.
Proof.
	intros l dn dl Hl H.
	destruct l; [reflexivity|].
	enough (He : BinNat.is_canonical_struct (strip (b :: l)) -> open_borrow (b :: l) [] dn dl <> None)
		by (apply He in H; [contradiction|assumption]).
	clear Hl H.
	revert dn dl.
	{	induction l as [|bl tl HR]; intros dn dl Hl H;
			[|destruct bl; apply BinNat.is_canonical_struct_tl in Hl]; destruct b;
			 simpl in *.
	+	discriminate.
	+	discriminate.
	+	apply HR in H; assumption.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	}
Qed.

Lemma open_zero_None : forall l,
		is_precanonical l ->
		open l [] = None ->
		l = empty.
Proof.
	intros l Hl H.
	apply open_borrow_zero_None in H; assumption.
Qed.
Lemma open_borrow_zero : forall l dn dl zip,
		open_borrow l [] dn dl = Some zip ->
		zip.(zip_dl) = (repeat Zero (length zip.(zip_dl) - length dl)) ++ dl
		/\ zip.(zip_nb) = (repeat 1 (length zip.(zip_dl) - length dl)) ++ dn.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl];
			intros dn dl zip H; simpl in *.
	+	discriminate.
	+	apply HR in H.
		destruct H as [Hdl Hnb].
		pose proof(Hlen := Nat.le_sub_l (length (zip_dl zip)) (length (zip_dl zip) - length (Zero :: dl))).
		rewrite Hdl in Hlen at 1.
		rewrite app_length, repeat_length, Nat.add_comm, Nat.add_sub in Hlen.
		rewrite (app_assoc _ [Zero] dl) in Hdl; rewrite (app_assoc _ [1] dn) in Hnb.
		rewrite <- repeat_cons in Hdl, Hnb.
		assert (forall {A : Type} (e : A) n, e :: repeat e n = repeat e (S n)) by reflexivity.
		rewrite H, <- Nat.sub_succ_l in Hdl, Hnb; [|assumption..].
		simpl in Hdl, Hnb.
		split; assumption.
	+	destruct zip as [ztl zdl zt znb].
		inversion_clear H; simpl.
		rewrite Nat.sub_diag.
		split; reflexivity.
	}
Qed.*)

Notation Zero := (@Zero (@CLBT.t A)).

Lemma open_borrow_zero : forall l n, option_lift (fun zip =>
		zip.(z_prefix _) = repeat Zero (length zip.(z_prefix _))
		/\ zip.(z_idx _) = repeat 1 (length zip.(z_idx _)))
		(open_borrow l Ob (repeat 1 n) (repeat Zero n)).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n; simpl in *.
	+	apply I.
	+	apply (HR (S n)).
	+	split; rewrite repeat_length; reflexivity.
	}
Qed.

Lemma open_zero : forall l,
		option_lift (option_lift (fun zip =>
		zip.(z_prefix _) = repeat Zero (length zip.(z_prefix _))
		/\ zip.(z_idx _) = repeat 1 (length zip.(z_idx _)))) (open l Ob).
Proof.

	intro l.
	unfold open.
	destruct l as [|tl bl]; [|destruct bl]; [apply I| |split;reflexivity]; simpl.
	eapply lift_map_conseq, (open_borrow_zero _ (S O)); trivial.
Qed.

(*
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
		BinNat.is_canonical_struct n ->
		open l (BinNat.inc n) = option_join dec_zip (open l n).
Proof.
	intros l n Hn.
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
*)

Section open.
Lemma open_aux_borrow_inc : forall (l : RAL) n dbn dl,
		BinNat.is_canonical n ->
		open_aux l (BinNat.inc n) dbn dl = open_borrow l n dbn dl.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n dbn dral Hn;
			(destruct n as [|tn bn];
		 	 	[|destruct bn; apply BinNat.is_canonical_tl in Hn as Htn]);
			try reflexivity; simpl.
	+	apply HR; assumption.
	+	inversion_clear Hn as [? Hpn|]; inversion_clear Hpn as [| |? Hn].
		inversion_clear Hn; reflexivity.
	+	destruct BinNat.inc eqn:Hd; rewrite <- Hd; apply HR; assumption.		
	}
Qed.

Lemma open_aux_dt_true : forall (l : RAL) n dbn dl dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		option_lift (fun z => option_map Some (open_aux l n dd dl) = dec_zip z) (open_aux l n dbn dl)
with open_borrow_dt_true : forall (l : RAL) n dbn dl dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		option_lift (fun z => option_map Some (open_borrow l n dd dl) = dec_zip z) (open_borrow l n dbn dl).
Proof.
	all: intro l; destruct l as [|tl bl]; [|destruct bl]; intros n dbn dral dd Hdd;
		assert (Hsdd : forall b, BinNat.dt_dec (b :: dbn) = (true, b :: dd))
			by (intro b; simpl; rewrite Hdd; destruct b; reflexivity);
		(destruct n as [|tn bn]; [|destruct bn]);
	  	try apply I; simpl.
	+	eapply lift_conseq, open_aux_dt_true, Hsdd; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	destruct tn; eapply lift_conseq, open_aux_dt_true, Hsdd;
			simpl; intros x Hx; assumption.
	+	destruct tn; [|eapply lift_conseq, open_aux_dt_true, Hsdd;trivial].
		unfold dec_zip; simpl.
		rewrite Hdd.
		reflexivity.
	+	eapply lift_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	unfold dec_zip; simpl.
		rewrite Hdd.
		reflexivity.
	+	eapply lift_conseq, open_aux_dt_true, Hsdd; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hsdd; trivial.
Qed.




Lemma open_borrow_eq_dt_true : forall (l : RAL) n dbn dl dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		option_lift (option_lift
			(fun z =>  option_map Some (open_borrow l n dd dl) = dec_zip z))
			(open_eq l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n dbn dl dd Hdd;
			assert (Hsdd : forall b, BinNat.dt_dec (b :: dbn) = (true, b :: dd))
			by (intro b; simpl; rewrite Hdd; destruct b; reflexivity);
			(destruct n as [|tn bn]; [|destruct bn]); try apply I; simpl.
	+	eapply lift_map_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	apply HR, Hsdd.
	+	eapply lift_map_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	eapply lift_map_conseq, open_aux_dt_true, Hsdd; trivial.
	+	apply HR, Hsdd.
	}
Qed.

Lemma open_aux_eq_dt_true : forall (l : RAL) n dbn dl dd,
		BinNat.is_canonical n ->
		(BinNat.dt_dec dbn) = (true, dd) ->
		option_lift (option_lift
			(fun z =>  option_map Some (open_aux l (BinNat.inc n) dd dl) = dec_zip z))
			(open_eq l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n dbn dl dd Hn Hdd;
			assert (Hsdd : forall b, BinNat.dt_dec (b :: dbn) = (true, b :: dd))
			by (intro b; simpl; rewrite Hdd; destruct b; reflexivity);
			(destruct n as [|tn bn]; [|destruct bn;
				apply BinNat.is_canonical_tl in Hn as Htn]);
			try apply I; simpl.
	+	eapply lift_map_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	apply open_borrow_eq_dt_true, Hsdd.
	+	rewrite open_aux_borrow_inc; [|assumption].
		eapply lift_map_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	inversion_clear Hn as [? Hp|]; inversion_clear Hp as [| |? Htp].
		destruct tn; [inversion_clear Htp|].
		eapply lift_map_conseq, open_aux_dt_true, Hsdd; trivial.
	+	destruct (BinNat.inc tn) eqn:Hdtn; rewrite <- Hdtn; apply HR, Hsdd; assumption.
	}
Qed.

Lemma open_borrow_eq_pos_Ob : forall (l : RAL) dn dl,
		BinNat.is_positive (to_bin l) ->
		option_map Some (open_borrow l Ob dn dl) = open_eq l Ob dn dl.
Proof.
	intros l dn dl Hl.
	destruct l as [|tl bl]; [inversion_clear Hl|destruct bl]; reflexivity.
Qed.
Lemma open_aux_eq : forall (l : RAL) n dbn dl dd,
		BinNat.is_canonical n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		(option_lift (fun z =>  open_eq l n dd dl = dec_zip z))
			(open_aux l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; intros n dbn dl dd Hn Hdd;
		[|destruct bl];
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn]);
		assert (Hd1 : BinNat.dt_dec (1 :: dbn) = (true, 0 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		assert (Hd0 : BinNat.dt_dec (0 :: dbn) = (false, 1 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		try apply I; simpl.
	+	apply HR; assumption.
	+	apply open_borrow_dt_true; assumption.
	+	destruct tn; apply open_aux_dt_true; assumption.
	+	destruct tn; [|apply HR; assumption].
		unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	}
Qed.
Lemma open_borrow_inc : forall (l : RAL) n dbn dl dd,
		is_canonical l ->
		BinNat.is_canonical n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		(option_lift (fun z =>  open_eq l (BinNat.inc n) dd dl = dec_zip z))
			(open_borrow l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; intros n dbn dl dd Hl Hn Hdd;
		[|destruct bl; apply is_canonical_tl in Hl as Htl];
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn]);
		assert (Hd1 : BinNat.dt_dec (1 :: dbn) = (true, 0 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		assert (Hd0 : BinNat.dt_dec (0 :: dbn) = (false, 1 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		try apply I; simpl.
	+	apply open_borrow_dt_true, Hd1.
	+	apply open_borrow_dt_true, Hd1.
	+	apply HR; assumption.
	+	unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	apply open_aux_eq; assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		apply open_borrow_dt_true, Hd1.
	}
Qed.


Lemma open_eq_inc : forall (l : RAL) n dbn dl dd,
		is_canonical l ->
		BinNat.is_canonical n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		option_lift (option_lift
			(fun z =>  open_eq l (BinNat.inc n) dd dl = dec_zip z))
			(open_eq l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; intros n dbn dl dd Hl Hn Hdd;
		[|destruct bl; apply is_canonical_tl in Hl];
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn]);
		assert (Hd1 : BinNat.dt_dec (1 :: dbn) = (true, 0 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		assert (Hd0 : BinNat.dt_dec (0 :: dbn) = (false, 1 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		try apply I; simpl.
	+	eapply lift_map_conseq, open_borrow_dt_true, Hd1; trivial.
	+	apply open_borrow_eq_dt_true, Hd1.
	+	eapply lift_map_conseq, open_borrow_inc, Hd0; [|assumption..]; trivial.
	+	unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	eapply lift_map_conseq, open_aux_eq, Hd0; [trivial|assumption].
	+	apply open_aux_eq_dt_true; assumption.
	}
Qed.

Lemma open_eq_dt_true : forall (l : RAL) n dbn dl dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		option_lift (option_lift (fun z => open_eq l n dd dl = dec_zip z))
			(open_eq l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n dbn dl dd Hdd;
		assert (Hsdd : forall b, BinNat.dt_dec (b :: dbn) = (true, b :: dd))
			by (intro b; simpl; rewrite Hdd; destruct b; reflexivity);
		(destruct n as [|tn bn]; [|destruct bn]);
		try apply I; simpl.
	+	eapply lift_map_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	apply HR, Hsdd.
	+	eapply lift_map_conseq, open_borrow_dt_true, Hsdd; trivial.
	+	unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	eapply lift_map_conseq, open_aux_dt_true, Hsdd; trivial.
	+	apply HR, Hsdd.
	}
Qed.

Lemma open_aux_None : forall (l : RAL) n dbn1 dbn2 dl,
		(open_borrow l n dbn1 dl = None -> open_borrow l n dbn2 dl = None)
		/\ (open_aux l n dbn1 dl = None -> open_aux l n dbn2 dl = None).
Proof.
	intros l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n dbn1 dbn2 dral ;
			(destruct n as [|tn bn]; [|destruct bn]);
			split; intro H; simpl in *; try reflexivity.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	discriminate.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	destruct tn; apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	destruct tn; [discriminate|].
		apply (HR _ (0 :: dbn1)); assumption.
	}
Qed.

Lemma open_aux_inc_None : forall (l : RAL) n dbn1 dbn2 dl,
		BinNat.is_positive n ->
		open_aux l n dbn1 dl = None -> open_borrow l n dbn2 dl = None
with open_borrow_inc_None : forall (l : RAL) n dbn1 dbn2 dl,
		BinNat.is_canonical n ->
		open_borrow l n dbn1 dl = None -> open_borrow l (BinNat.inc n) dbn2 dl = None.
Proof.
	all: intro l; destruct l as [|tl bl]; [|destruct bl]; intros n dbn1 dbn2 dl Hn H;
		(destruct n as [|tn bn]; [|destruct bn]);
		try reflexivity; simpl in *.
	+	inversion_clear Hn.
	+	inversion_clear Hn as [| |? Htn].
		eapply open_aux_inc_None, H; assumption.
	+	eapply open_aux_None, H.
	+	inversion_clear Hn.
	+	destruct tn; eapply open_aux_None, H.
	+	revert H; inversion_clear Hn as [|? Htn|]; intro H; [discriminate|].
		destruct tn; [inversion_clear Htn|].		
		eapply open_aux_inc_None, H; assumption.
	+	eapply open_aux_None, H.
	+	eapply open_aux_None, H.
	+	eapply open_borrow_inc_None, H; eapply BinNat.is_canonical_tl, Hn.
	+	discriminate.
	+	inversion_clear Hn as [? Hpn|]; inversion_clear Hpn as [| |? Htn].
		eapply open_aux_inc_None, H; assumption.
	+	apply BinNat.is_canonical_tl in Hn as Htn.
		rewrite open_aux_borrow_inc; [|assumption].
		eapply open_aux_None, H.
Qed.

Lemma open_eq_borrow_None : forall (l : RAL) n dn1 dn2 dl,
		open_eq l n dn1 dl = None -> open_borrow l n dn2 dl = None.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [t|]]; intros n dn1 dn2 dl H;
		(destruct n as [|tn bn]; [|destruct bn]);
		simpl in *;	try discriminate || reflexivity.
	+	pose proof (Hnone := proj1 (open_aux_None tl Ob (1 :: dn1) (1 :: dn2) (Zero :: dl))).
		destruct open_borrow; [discriminate|rewrite Hnone; reflexivity].
	+	eapply HR, H.
	+	pose proof (Hnone := proj1 (open_aux_None tl tn (0 :: dn1) (0 :: dn2) (Zero :: dl))).
		destruct open_borrow; [discriminate|rewrite Hnone; reflexivity].
	+	pose proof (Hnone :=
			proj2 (open_aux_None tl tn (0 :: dn1) (0 :: dn2) (One _ t :: dl))).
		destruct open_aux; [discriminate|rewrite Hnone; reflexivity].
	+	eapply HR, H.
	}
Qed.
Lemma open_aux_eq_None : forall (l : RAL) n dn1 dn2 dl,
	  is_positive n ->
	  open_aux l n dn1 dl = None -> open_eq l n dn2 dl = None.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [t|]]; intros n dn1 dn2 dl Hn H;
		(destruct n as [|tn bn]; [|destruct bn]);
		simpl in *;	try discriminate || reflexivity.
	+	inversion_clear Hn.
	+	inversion_clear Hn.
	+	inversion_clear Hn as [| |? Htn].
		eapply HR, H; assumption.
	+	eapply open_aux_None in H.
		rewrite H; reflexivity.
	+	inversion_clear Hn.
	+	destruct tn; eapply open_aux_None in H; rewrite H; reflexivity.
	+	destruct tn; [discriminate|].
		inversion_clear Hn as [| |? Htn].
		eapply HR, H; assumption.
	}
Qed.
Lemma open_borrow_eq_inc_None : forall (l : RAL) n dn1 dn2 dl,
		BinNat.is_canonical n ->
		open_borrow l n dn1 dl = None -> open_eq l (BinNat.inc n) dn2 dl = None.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [t|]]; intros n dn1 dn2 dl Hn H;
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn as Htn]);
		simpl in *;	try discriminate || reflexivity.
	+	eapply open_aux_None in H.
		rewrite H; reflexivity.
	+	eapply open_aux_None in H.
		rewrite H; reflexivity.
	+	eapply HR, H; assumption.
	+	inversion_clear Hn as [? Hp|]; inversion_clear Hp as [| |? Htp].
		eapply open_aux_eq_None, H; assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		eapply open_aux_None in H.
		rewrite H; reflexivity.
	}
Qed.
	  
Lemma open_eq_inc_None : forall (l : RAL) n dn dl,
		BinNat.is_canonical n ->
		open_eq l n dn dl = None -> open_eq l (BinNat.inc n) dn dl = None.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [t|]]; intros n dn dl Hn H;
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn as Htn]);
		simpl in *;	try discriminate || reflexivity.
	+	pose proof (Hnone := proj1 (open_aux_None tl Ob (1 :: dn) (0 :: dn) (Zero :: dl))).
		destruct open_borrow; [discriminate|rewrite Hnone; reflexivity].
	+	pose proof (Hnone := open_eq_borrow_None tl tn (1 :: dn) (0 :: dn) (Zero :: dl)).
		destruct open_eq; [discriminate|rewrite Hnone; reflexivity].
	+	assert (Hnone : open_borrow tl tn (0 :: dn) (Zero :: dl) = None)
			by (destruct open_borrow; [discriminate|reflexivity]).
		eapply open_borrow_eq_inc_None, Hnone; assumption.
	+	assert (Hnone : open_aux tl tn (0 :: dn) (One _ t :: dl) = None)
		  by (destruct open_aux; [discriminate|reflexivity]).
		inversion_clear Hn as [? Hp|]; inversion_clear Hp as [| |? Htp].
		eapply open_aux_eq_None, Hnone; assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		pose proof (Hnone := open_eq_borrow_None tl tn (1 :: dn) (0 :: dn) (One _ t :: dl)).
		destruct open_eq; [discriminate|rewrite Hnone; reflexivity].
	}
Qed.


Lemma open_eq_borrow_Some_None : forall (l : RAL) n dn1 dn2 dl,
		BinNat.is_canonical n ->
		open_eq l n dn1 dl = Some None -> open_borrow l n dn2 dl = None.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [t|]]; intros n dn1 dn2 dl Hn H;
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn as Htn]);
		simpl in *;	try discriminate || reflexivity.
	+	assert (Hnone : open_borrow tl Ob (1 :: dn1) (Zero :: dl) = None)
			by (destruct open_borrow; [discriminate|reflexivity]).
		eapply open_aux_None, Hnone.
	+	eapply HR, H; assumption.
	+	assert (Hnone : open_borrow tl tn (0 :: dn1) (Zero :: dl) = None)
			by (destruct open_borrow; [discriminate|reflexivity]).
		eapply open_aux_None, Hnone.
	+	assert (Hnone : open_aux tl tn (0 :: dn1) (One _ t :: dl) = None)
			by (destruct open_aux; [discriminate|reflexivity]).
		eapply open_aux_None, Hnone.
	+	eapply HR, H; assumption.
	}
Qed.
Lemma open_eq_Some_None_inc : forall (l : RAL) n dn dl,
		BinNat.is_canonical n ->
		open_eq l n dn dl = Some None -> open_eq l (BinNat.inc n) dn dl = None.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [t|]]; intros n dn dl Hn H;
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn as Htn]);
		simpl in *;	try discriminate || reflexivity.
	+	assert (Hnone : open_borrow tl Ob (1 :: dn) (Zero :: dl) = None)
			by (destruct open_borrow; [discriminate|reflexivity]).
		eapply open_aux_None in Hnone.
		rewrite Hnone; reflexivity.
	+	eapply open_eq_borrow_Some_None in H; [|assumption].
		rewrite H; reflexivity.
	+	assert (Hnone : open_borrow tl tn (0 :: dn) (Zero :: dl) = None)
			by (destruct open_borrow; [discriminate|reflexivity]).
		eapply open_borrow_eq_inc_None, Hnone; assumption.
	+	assert (Hnone : open_aux tl tn (0 :: dn) (One _ t :: dl) = None)
			by (destruct open_aux; [discriminate|reflexivity]).
		inversion_clear Hn as [? Hp|]; inversion_clear Hp as [| |? Htp].
		eapply open_aux_eq_None, Hnone; assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		erewrite open_eq_borrow_Some_None; [reflexivity|assumption|apply H].
	}
Qed.


Lemma open_inc : forall (l : RAL) n,
		is_canonical l ->
		BinNat.is_canonical n ->
		open l (BinNat.inc n) = option_bind (open l n) (fun o => option_bind o dec_zip).
Proof.
	intros l n Hl Hn.
	unfold open.
	pose proof (Hnone := open_eq_inc_None l n [] [] Hn).
	pose proof (Hsomenone := open_eq_Some_None_inc l n [] [] Hn).
	pose proof (Hsome := open_eq_inc l n [] [] _ Hl Hn eq_refl).
	{	destruct open_eq as [z|];  [destruct z as [z|]|]; simpl in *.
	+	assumption.
	+	apply Hsomenone; reflexivity.
	+	apply Hnone; reflexivity.
	}
Qed.


Lemma open_eq_Some_None : forall (l : RAL) n dn dl,
		open_eq l n dn dl = Some None -> to_bin l = n.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n dn dl H;
		(destruct n as [|tn bn]; [|destruct bn]); simpl in *;
		try reflexivity || discriminate.
	+	destruct open_borrow; discriminate.
	+	erewrite to_bin_snoc, HR; [reflexivity|apply H].
	+	destruct open_borrow; discriminate.
	+	destruct open_aux; discriminate.
	+	erewrite to_bin_snoc, HR; [reflexivity|apply H].
	}
Qed.

Lemma open_Some_None : forall (l : RAL) n,
	  open l n = Some None -> to_bin l = n.
Proof.
	intros l n H.
	apply open_eq_Some_None in H.
	assumption.
Qed.
End open.

Section drop.

(*
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
		Ral.cons_tree t l = (repeat Zero k) ++ r ->
		(uncurry Ral.cons_tree) (scatter t l (repeat 1 n)) = (repeat Zero (n + k)) ++ r.
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
		(uncurry cons_tree) (scatter t (safe_zero tl) (repeat 1 n)) = (repeat Zero n) ++ [One t] ++ tl.
Proof.
	intros n t tl Ht.
	rewrite (plus_n_O n) at 2.
	{	apply scatter_cons_zero_aux.
	+	assumption.
	+	destruct tl; reflexivity.
	}
Qed.
 *)

Lemma scatter_dec_false : forall dn (l l' : RAL) t t' dd,
		CLBT.is_valid_idx dn t ->
		CLBT.is_valid_idx dn t' ->
		BinNat.dt_dec dn = (false, dd) ->
		Ral.cons_tree t' l' = l ->
		option_map (fun '(_, r) => splug l r) (scatter t dn) =
		option_map (fun '(a, r) => Ral.cons a (splug l' r)) (scatter t' dd).
Proof.
	intros dn.
	{	induction dn as [|bn tn HR]; [|destruct bn]; intros l l' t t' dd Ht Ht' Hdd;
			inversion_clear Ht as [a|? tl tr Htl Htr];
			inversion_clear Ht' as [a'|? t'l t'r Ht'l Ht'r];
			intro H; simpl.
	+	inversion_clear Hdd; simpl.
		cbn [plug gplug].
		rewrite <- H.
		reflexivity.
	+	simpl in Hdd.
		destruct (BinNat.dt_dec tn) as [B r], B; [discriminate|].
		inversion_clear Hdd; simpl.
		assert (H' : Ral.cons_tree t'r (ssnoc l' (One CLBT.t t'l)) = ssnoc l Zero) by
			(destruct l' as [|tl' bl']; [|destruct bl']; rewrite <- H; simpl; reflexivity).
		specialize (HR (ssnoc l Zero) (ssnoc l' (One _ t'l)) _ _ _ Htl Ht'r eq_refl H').
		destruct scatter as [p|], scatter as [p'|]; [|discriminate..|reflexivity].
		destruct p as [? s], p' as [a' s']; simpl in *.
		apply HR.
	+	simpl in Hdd.
		destruct (BinNat.dt_dec tn) as [B r], B; discriminate.
	}
Qed.
	
Lemma scatter_dec : forall dn (l : RAL) t dd,
		CLBT.is_valid_idx dn t ->
		BinNat.dt_dec dn = (true, dd) ->
		option_map (fun '(a, r) => splug l r) (scatter t dn) =
		option_map (fun '(a, r) => Ral.cons a (splug l r)) (scatter t dd).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; [|destruct bn]; intros l t dd Ht Hdd;
			inversion_clear Ht as [a|? tl tr Htl Htr]; simpl in *.
	+	discriminate.
	+	destruct (BinNat.dt_dec tn) as [B r], B; inversion_clear Hdd;
		specialize (HR (ssnoc l Zero) _ _ Htl eq_refl);
		destruct scatter as [p|], scatter as [p'|]; [|discriminate..|reflexivity];
		destruct p as [? s], p' as [a' s']; apply HR.
	+	pose proof (Hsf := scatter_dec_false tn).
		{	destruct (BinNat.dt_dec tn) as [B r], B; inversion_clear Hdd.
		+	specialize (HR (ssnoc l (One _ tl))  _ _ Htr eq_refl).
			destruct scatter as [p|], scatter as [p'|]; [|discriminate..|reflexivity].
			destruct p as [? s], p' as [a' s']; apply HR.
		+	assert (Hct : Ral.cons_tree tl (ssnoc l Zero) = ssnoc l (One CLBT.t tl)) by
				(destruct l; reflexivity).
			specialize (Hsf _ _ _ _ _ Htr Htl eq_refl Hct).
			destruct scatter as [p|], scatter as [p'|]; [|discriminate..|reflexivity].
			destruct p as [? s], p' as [a' s']; simpl in *.
			assumption.
		}
	}
Qed.

Lemma scatter_cons_zero_aux : forall n l l' t,
	  CLBT.is_valid n t ->
	  Ral.cons_tree t l' = l ->
		Some (splug l (repeat Zero n)) =
			option_map (fun '(a, r) => Ral.cons a (splug l' r)) (scatter t (repeat 1 n)).
Proof.
	intros n.
	{	induction n as [|n HR]; intros l l' t Ht;
			inversion_clear Ht as [a|? tl tr Hl Hr];
			intro H; cbn [splug gplug]; simpl.
	+	rewrite <- H.
		reflexivity.
	+	assert (Hc : Ral.cons_tree tr (snoc l' (One _ tl)) = (snoc l Zero))
			by (simpl; rewrite H; reflexivity).
		specialize (HR (snoc l Zero) (snoc l' (One _ tl)) tr Hr Hc).
		destruct scatter as [p|]; [|discriminate].
		destruct p as [a r]; simpl in *.
		destruct l; [destruct l' as [|l' bl]; [|destruct bl]; discriminate|].
		destruct l'; assumption.
	}
Qed.

Lemma scatter_cons_zero : forall l n t,
		CLBT.is_valid n t ->
		Some (splug l (One _ t :: repeat Zero n)) =
		option_map (fun '(a, r) => Ral.cons a (splug l (Zero :: r)))
		(scatter t (repeat 1 n)).
Proof.
	intros l n t Ht.
	apply scatter_cons_zero_aux; [assumption|].
	destruct l; reflexivity.
Qed.

Lemma drop_zero : forall (l : RAL),
		is_well_formed l ->
		option_lift (eq l) (drop l Ob).
Proof.
	intros l Hl.
	unfold drop.
	pose proof (Hoz := open_zero l).
	pose proof (Hosn := open_Some_None l Ob).
	pose proof (Hv := open_valid l Ob (wf_valid _ Hl)).
	pose proof (Hz := open_zipper l Ob).

	destruct open as [z|]; [|apply I]; simpl.
	destruct z as [z|]; [|destruct l; [|discriminate Hosn]; reflexivity].
	destruct z as [tl t dl idx], Hv as [_ _ Ht Hlen]; simpl in *.
	destruct Hoz as [Hodl Hoidx].

	pose proof (scatter_cons_zero tl (List.length idx) t Ht).
	rewrite Hoidx.
	destruct scatter as [p|]; [|discriminate].
	destruct p as [a r]; simpl in *.
	inversion_clear H.
	unfold is_zipper in Hz; simpl in Hz.
	rewrite <- Hlen, <- Hodl, <- plug_eq_splug; [assumption|].
	rewrite <- Hz; exact (wf_canonical _ Hl).
Qed.


(*	does not work with fail monad !!!
Lemma drop_inc : forall (l : RAL) n,
		is_well_formed l -> BinNat.is_canonical n ->
		option_bind (drop l n) Ral.tl = drop l (BinNat.inc n).
Proof.
	intros l n Hl Hn.
	destruct Hl as [Hvl Hcl].
	unfold drop.
	
	pose proof (Hv := open_valid l n Hvl).
	pose proof (Hi := open_inc l n Hn).
	pose proof (Hz := open_zipper l n).
	rewrite Hi.
	
	destruct open as [zip|]; simpl; [|].
	destruct zip as [tl t dl idx], Hv as [_ _ Ht _]; simpl in *.
	unfold dec_zip.
	unfold is_zipper in Hz.
	destruct Hi as [_ _ _ _]; simpl in *.

	pose proof (Hsd := scatter_dec idx (ssnoc tl Zero) t).
	pose proof (Hdz := dt_dec_zero idx).

	{	destruct (BinNat.dt_dec idx) as [B dd], B; simpl.
	+	specialize (Hsd _ Ht eq_refl).
		destruct scatter as [p|], scatter as [p'|]; [|discriminate..|reflexivity].
		destruct p as [? s], p' as [a' s']; simpl in *.
		unfold Ral.is_canonical in Hcl.
		rewrite Hz, to_bin_plug in Hcl.
		rewrite tail_cons; [|eapply splug_canonical, is_canonical_plug, Hcl].
		assumption.
	+	destruct (Hdz _ eq_refl) as [Hidx Hdd].
		rewrite Hidx, Hdd.
		pose proof (Hbz := open_borrow_zero). 
	}
	
	unfold is_precanonical, strip in Hl.
	pose proof (Hv := open_valid l n).
	pose proof (Hi := open_inc l n Hn).
	pose proof (Hz := open_zipper l n).
	destruct (open l n) as [zip|]; rewrite Hi; [simpl|reflexivity].
	specialize (Hz _ eq_refl); unfold is_zipper in Hz.
	destruct (Hv _ Hvl eq_refl) as [Hvtl Hvdl Ht Hlen].
	destruct zip as [tl dl t nb]; simpl in *.
	rewrite <- Hlen in Ht.
	rewrite Hz, rev_append_rev, map_app in Hl.
	apply -> BinNat.is_canonical_struct_app in Hl; [|discriminate].
	unfold dec_zip; simpl.
	pose proof (Hsd := scatter_dec_aux nb (safe_zero tl) t).
	pose proof (Hdz := BinNat.dt_dec_zero nb).
	pose proof (Hdlen := BinNat.dt_dec_length nb).
	{	destruct BinNat.dt_dec as [b tdd], b; simpl in *.
	+	assert (Hpsl : is_precanonical (safe_zero tl))
			by (apply canonical_safe_zero; assumption).
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
			rewrite H0, rev_repeat, map_app in Hl.
			apply -> BinNat.is_canonical_struct_app in Hl; [|discriminate].
			simpl in Hl.
			unfold tail; rewrite Hzeroes, cons_uncons;
			  [|unfold is_precanonical, strip; rewrite app_comm_cons, !map_app, app_assoc; apply BinNat.is_canonical_struct_app; [discriminate|assumption] |discriminate].
			assert (forall {A : Type} (e : A) n, e :: repeat e n = repeat e (S n)) by reflexivity.
			rewrite app_comm_cons, app_assoc, H, <- repeat_app,
				Nat.add_comm, Nat.add_succ_comm, Hdlen.
			apply eq_sym, scatter_cons_zero.
			rewrite <- Hnlen, Hlen2.
			assumption.
		+	rewrite Hnone; [|reflexivity].
			pose proof (Hsez := scatter_empty_zeroes (length nb) t).
			destruct (scatter t (safe_zero empty)).
			simpl in *.
			rewrite Hsez.
			unfold tail; rewrite cons_uncons; reflexivity.
		}
	}
Qed.*)

(*Lemma drop_as_tail : forall l n,
	 	is_canonical_struct 0 l ->
		BinNat.is_canonical_struct n ->
		drop l n = fun_pow tail (BinNat.to_nat n) l.
Proof.
	intros l n Hl Hn.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply is_canonical_struct_equiv in Hl.
	revert l Hl.
	{	induction Hn as [|n Hn HR]; intros l Hl; simpl.
	+	apply drop_zero.
		assumption.
	+	rewrite BinNat.inc_S;simpl.
		rewrite <- fun_pow_comm.
		rewrite <- HR; [|assumption].
		apply BinNat.is_canonical_struct_equiv in Hn.
		apply is_canonical_struct_equiv in Hl.
		apply eq_sym, drop_inc; assumption.
	}
Qed.

 *)

End drop.

Section lookup.

Lemma scatter_lookup : forall dn (t : @CLBT.t A),
		CLBT.is_valid (length dn) t ->
		option_map fst (scatter t dn) = (CLBT.lookup t dn).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; intros t Ht;
			inversion_clear Ht; simpl.
	+	reflexivity.
	+	destruct bn; (rewrite <- HR; [|assumption]);
		  (destruct scatter as [p|]; [destruct p as [a ?]|]); reflexivity.
	}
Qed.


Lemma scatter_total : forall dn (t : @CLBT.t A),
		CLBT.is_valid (length dn) t ->
		exists a r, scatter t dn = Some (a, r).
Proof.
	intros dn.
	{	induction dn as [|bn tn HR]; intros t Ht; simpl;
			inversion_clear Ht as [|? l r Hl Hr].
	+	eexists; eexists; reflexivity.
	+	destruct bn; simpl; [destruct (HR _ Hl) as [a Hx]| destruct (HR _ Hr) as [a Hx]];
			destruct Hx as [x Hx]; rewrite Hx; eexists; eexists; reflexivity.
	}
Qed.
Lemma lookup_drop : forall (l : RAL) n,
		is_well_formed l ->
		lookup l n = option_bind (drop l n) Ral.hd.
Proof.
	intros l n Hl.
	destruct Hl as [Hlv Hlc].
	unfold lookup, drop.
	pose proof (Hz := open_zipper l n).
	pose proof (Hv := open_valid l n Hlv).
	destruct (open l n) as [zip|]; [|reflexivity].
	destruct zip as [tl t dl idx], Hv as [_ _ Ht Hlen]; simpl in *.
	pose proof (Hst := scatter_total idx t Ht).
	destruct Hst as [a Hst], Hst as [r Hst].
	rewrite <- scatter_lookup, Hst; [|assumption]; simpl.
	rewrite hd_cons; [reflexivity|].
	unfold is_zipper in Hz; simpl in Hz.
	rewrite Hz in Hlc.
	unfold is_canonical in Hlc.
	rewrite to_bin_plug in Hlc.
	apply is_canonical_plug in Hlc.
	apply splug_canonical; assumption.
Qed.
(*
Lemma lookup_zero : forall l,
		is_canonical l ->
		lookup l [] = head l.
Proof.
	intros l Hl.
	apply canonical_valid in Hl as Hvl.
	apply is_canonical_struct_equiv in Hl.
	rewrite lookup_drop, drop_as_tail; [|assumption|reflexivity|assumption].
	reflexivity.
Qed.
Lemma lookup_inc : forall l n,
	 	is_canonical l ->
		BinNat.is_canonical n ->
		lookup l (BinNat.inc n) = lookup (tail l) n.
Proof.
	intros l n Hl Hn.
	apply canonical_valid in Hl as Hvl.
	apply tail_valid in Hvl as Hvtl.
	apply is_canonical_struct_equiv in Hl as Hl2.
	apply canonical_tail in Hl as Htl.
	apply is_canonical_struct_equiv in Htl.
	apply BinNat.is_canonical_struct_equiv in Hn as Hn2.
	apply BinNat.canonical_inc in Hn as Hin.
	apply BinNat.is_canonical_struct_equiv in Hin.
	rewrite !lookup_drop, !drop_as_tail; [|assumption..].
	rewrite BinNat.inc_S.
	reflexivity.
Qed.

Lemma comprehension : forall l0 l1,
		is_canonical l0 -> is_canonical l1 ->
		(forall n, BinNat.is_canonical n -> lookup l0 n = lookup l1 n) ->
		l0 = l1.
Proof.
	intros l0 l1 Hl0.
	revert l1.
	{	induction Hl0 as [|l0 a Hl0 HR]; intros l1 Hl1 H;
			destruct Hl1 as [|l1 b Hl1]; simpl.
	+	reflexivity.
	+	specialize (H _ BinNat.canonical_0).
		rewrite !lookup_zero, head_cons in H;
			[|apply canonical_Cons; assumption|apply canonical_Empty].
		discriminate.
	+	specialize (H _ BinNat.canonical_0).
		rewrite !lookup_zero, head_cons in H;
			[|apply canonical_Empty|apply canonical_Cons; assumption].
		discriminate.
	+	pose proof (H0 := H _ BinNat.canonical_0).
		pose proof (canonical_Cons _ a Hl0).
		pose proof (canonical_Cons _ b Hl1).
		rewrite !lookup_zero, !head_cons in H0; [|assumption..].
		inversion_clear H0.
		f_equal.
		apply HR; [assumption|].
		intros n Hn.
		specialize (H _ (BinNat.canonical_inc _ Hn)).
		rewrite !lookup_inc in H; [|assumption..].
		rewrite !cons_tail in H; [|assumption..].
		assumption.
	}
Qed.

*)

End lookup.

Section update.

Lemma plug_eq : forall (l0 r0 : RAL) l1 r1 t t',
		length l1 = length r1 -> Num.plug l0 (t :: l1) = Num.plug r0 (t' :: r1) ->
		t = t'.
Proof.
	intros l0 r0 l1 r1 t t' Hl H.
	cbn [Num.plug Num.gplug] in H.
	apply (f_equal Num.to_list) in H.
	rewrite !Num.to_list_plug, !rev_append_rev, !Num.to_list_snoc in H.
	apply (f_equal (fun l => nth (length (rev l1)) l t)) in H.
	rewrite nth_middle, rev_length, Hl, <- rev_length, nth_middle in H.
	assumption.
Qed.
Theorem lookup_update_eq : forall (l : RAL) n a,
		is_well_formed l ->
		BinNat.is_canonical n ->
		to_bin l >? n = true ->
		Some a = (option_bind (update l n a) (fun l => lookup l n)).
Proof.
	intros l n a Hl Hn H.

	pose proof (Hutb := update_to_bin l n a).
	
	unfold update, lookup, gtb in *.

	pose proof (Hu := open_gt l n).
	pose proof (Hvu := open_valid l n (wf_valid _ Hl)).
	pose proof (Hzu := open_zipper l n).
	rewrite <- Hu in H.

	destruct (open l n) as [zu|]; [|discriminate].
	destruct zu as [utl ut udl uidx], Hvu as [_ _ Hut _]; simpl in *.
	destruct (CLBT.update_total _ _ a Hut) as [ux Hux].
	rewrite Hux in *; simpl in *.
	
	pose proof (Hlook := open_gt (Num.plug (Num.snoc utl (One CLBT.t ux)) udl) n).
	pose proof (Hzlook := open_zipper (Num.plug (Num.snoc utl (One CLBT.t ux)) udl) n).

	rewrite Hutb, <- Hu in Hlook.
	
	destruct open as [zl|]; [|discriminate].
	destruct zl as [ltl lt ldl lidx]; simpl in *.

	unfold is_zipper in *; simpl in *.

	inversion Hlook as [[Htn Hdn Hdiff]].
	apply (f_equal (@length (BinNat.Bit))) in Hdn.
	unfold dto_bin in Hdn; rewrite !map_length in Hdn.

	apply plug_eq in Hzlook; [|symmetry; assumption].
	inversion Hzlook as [Ht]; rewrite <- Ht.

	pose proof (Hlu := CLBT.lookup_update_eq _ _ a Hut).
	rewrite Hux in Hlu; simpl in Hlu.
	rewrite Hlu.
	reflexivity.
Qed.
(*
Proof.
	intros l n a Hl Hn H.

	(* hypothèses utiles *)
	pose proof (Hlookup := open_gtb (RAL.update l n a) n).
	rewrite update_strip in Hlookup; [|assumption..].
	apply RAL.canonical_valid in Hl as Hvl.
	pose proof (Hu := update_canonical _ _ a Hl Hn).
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply RAL.is_canonical_struct_equiv in Hl, Hu.
	destruct Hl as [_ Hl], Hu as [_ Hu].
	pose proof (Hgs := BinNat.gtb_decomp_equiv (RAL.strip l) n Hl Hn).
	rewrite H in Hgs.
	pose proof (Hzlookup := RAL.open_zipper (RAL.update l n a) n).
	assert (Hvupdate : forall zip,
			RAL.open l n = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	pose proof (Hupdate := open_gtb l n).
	destruct BinNat.gtb_decomp as [decomp|]; [|discriminate].
	destruct decomp as [tn dn an].

	(* élimination des cas impossibles *)
	unfold RAL.lookup, RAL.update in *.
	destruct (RAL.open l n) as [zip1|], RAL.open as [zip2|] eqn:Hz2; [|discriminate..].
	specialize (Hzlookup zip2 eq_refl).
	specialize (Hvupdate zip1 eq_refl).
	destruct zip1 as [tl1 dl1 t1 nb1], zip2 as [tl2 dl2 t2 nb2].
	unfold RAL.is_zipper, RAL.plug in *.
	simpl in *.

	(* décomposition *)
	inversion Hupdate as [(Htl1, Hdl1, Hnb1)].
	inversion Hlookup as [(Htl2, Hdl2, Hnb2)].
	apply (f_equal (@length BinNat.Bit)) in Hdl1, Hdl2, Htl1, Htl2.
	rewrite !RAL.strip_length, !rev_append_rev in *.
	apply (f_equal (fun l => nth (length (rev dl1)) l RAL.Zero)) in Hzlookup.
	rewrite nth_middle, rev_length, Hdl1, <- Hdl2, <- rev_length, nth_middle in Hzlookup.
	inversion Hzlookup as [Ht2].
	f_equal.
	rewrite Hnb1.
	apply CLBT.lookup_update_eq.
	destruct Hvupdate as [_ _ Ht Hlen]; simpl in Ht, Hlen.
	rewrite <- Hlen, Hnb1 in Ht.
	rewrite BinNat.complement_length.
	assumption.
Qed. *)

Theorem lookup_update_neq : forall (l : RAL) n m a,
		is_well_formed l ->
		BinNat.is_canonical n ->
		BinNat.is_canonical m ->
		n <> m ->
		to_bin l >? n = true ->
        option_bind (Ral.update l n a) (fun l => Ral.lookup l m) =
		Ral.lookup l m.
Proof.
	intros l n m a Hl Hn Hm Hdiff H.
	
	pose proof (Hutb := update_to_bin l n a).
	pose proof (Hdidx := gt_inj_neq (to_bin l) n m Hdiff (wf_canonical _ Hl) Hn Hm).
	
	unfold update, lookup, gtb in *.

	pose proof (Hu := open_gt l n).
	pose proof (Hvu := open_valid l n (wf_valid _ Hl)).
	pose proof (Hzu := open_zipper l n).
	pose proof (Hgtvu := gt_is_decomp (to_bin l) n Hn).
	
	rewrite <- Hu in H.

	destruct (open l n) as [zu|], (gt (to_bin l) n) as [zgtn|]; [|discriminate..].
	
	destruct zu as [utl ut udl uidx], Hvu as [_ _ Hut _]; simpl in *.
	destruct (CLBT.update_total _ _ a Hut) as [ux Hux].
	rewrite Hux in *; simpl in *.
	
	pose proof (Hlook1 := open_gt l m).
	pose proof (Hlook2 := open_gt (plug (snoc utl (One CLBT.t ux)) udl) m).
	
	pose proof (Hzl1 := open_zipper l m).
	pose proof (Hzl2 := open_zipper (plug (snoc utl (One CLBT.t ux)) udl) m).
	pose proof (Hgtvl := gt_is_decomp (to_bin l) m Hm).

	rewrite Hutb in Hlook2.
	rewrite <- Hlook2 in Hlook1.
	
	destruct (open l m) as [zl1|], open as [zl2|]; [|discriminate..|reflexivity].
	destruct (gt (to_bin l) m) as [zgtm|]; [|discriminate].
	destruct zl1 as [tl1 t1 dl1 idx1], zl2 as [tl2 t2 dl2 idx2]; simpl in *.

	inversion Hlook1 as [[Htl Hdl Hidx]].
	unfold is_zipper in *; simpl in *.

	rewrite Hzu in Hzl1.
	apply (f_equal to_list) in Hzl1, Hzl2.
	rewrite !to_list_plug, !rev_append_rev in Hzl1, Hzl2.
	rewrite to_list_snoc in Hzl2; simpl in Hzl1, Hzl2.
	rewrite <- !app_assoc in Hzl1, Hzl2; rewrite <- app_assoc in Hzl1.
	simpl in Hzl1, Hzl2.
	apply (f_equal (@List.length _)) in Hdl; unfold dto_bin in Hdl.
	rewrite !map_length in Hdl.

	{	destruct (PeanoNat.Nat.eq_dec (length udl) (length dl1)) as [Hlen|Hlen].
	+	apply (f_equal (fun l => nth (length (rev udl)) l (One _ ut))) in Hzl1, Hzl2.
		rewrite !nth_middle, rev_length, Hlen in Hzl1, Hzl2.
		rewrite <- rev_length, nth_middle in Hzl1.
		rewrite Hdl, <- rev_length, nth_middle in Hzl2.
		inversion Hzl1 as [Ht1]; inversion Hzl2 as [Ht2].
		destruct Hgtvl as [Hgtll _ _], Hgtvu as [Hgtlu _ _].
		revert Hdidx Hgtll Hgtlu;
			inversion_clear Hlook2; inversion_clear Hu; simpl;
			intros Hdidx Hgtll Hgtlu.
		unfold dto_bin in Hgtll, Hgtlu; rewrite map_length in Hgtll, Hgtlu.
		rewrite <- Hdl, <- Hlen, <- Hgtlu in Hgtll.
		pose proof (Hln := CLBT.lookup_update_neq uidx idx2 ut a (eq_sym Hgtll) Hdidx Hut).
		rewrite Hux in Hln.
		rewrite <- Ht1, <- Ht2.
		assumption.
	+	apply (f_equal (fun l => nth (length (rev dl1)) l (One _ ut))) in Hzl1.
		apply (f_equal (fun l => nth (length (rev dl1)) l (One _ ut))) in Hzl2.
		rewrite <- (rev_length udl), <- (rev_length dl1) in Hlen.
		pose proof (Hsel := list_select_neq (length (rev dl1)) (rev udl) (to_list utl)
			(One CLBT.t ut) (One CLBT.t ux) (not_eq_sym Hlen)).
		simpl in Hsel.
		rewrite Hsel, Hzl1 in Hzl2.
		rewrite nth_middle, rev_length, Hdl, <- rev_length, nth_middle in Hzl2.
		inversion_clear Hzl2.
		reflexivity.
	}	
Qed.


End update.

End Ral.
