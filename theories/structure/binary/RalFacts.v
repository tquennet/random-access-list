Require Import numerical.Num numerical.binary.BinNat structure.binary.Ral
	utils.Utils Lists.List.
Import ListNotations.
Import BinNat.Notations.

Section Ral.

Context {A : Type}.
Notation RAL := (@Ral.t A).

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

Lemma open_zero : forall l,
		option_lift (fun zip =>
		zip.(z_prefix _) = repeat Zero (length zip.(z_prefix _))
		/\ zip.(z_idx _) = repeat 1 (length zip.(z_idx _))) (open l Ob).
Proof.
	
	enough (Hob : forall l n,
		option_lift (fun zip =>
		zip.(z_prefix _) = repeat Zero (length zip.(z_prefix _))
		/\ zip.(z_idx _) = repeat 1 (length zip.(z_idx _)))
		(open_borrow l Ob (repeat 1 n) (repeat Zero n)))
		by (intros l; apply (Hob l O)).
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl]; intros n; simpl in *.
	+	apply I.
	+	apply (HR (S n)).
	+	split; rewrite repeat_length; reflexivity.
	}
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
		option_lift (fun z => open_aux l n dd dl = dec_zip z) (open_aux l n dbn dl)
with open_borrow_dt_true : forall (l : RAL) n dbn dl dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		option_lift (fun z => open_borrow l n dd dl = dec_zip z) (open_borrow l n dbn dl).
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

Lemma open_aux_inc : forall (l : RAL) n dbn dl dd,
		BinNat.is_canonical n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		option_lift (fun z => open_borrow l n dd dl = dec_zip z)
			(open_aux l n dbn dl)
with open_borrow_inc : forall (l : RAL) n dbn dl dd,
		BinNat.is_canonical n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		option_lift (fun z => open_borrow l (BinNat.inc n) dd dl = dec_zip z)
			(open_borrow l n dbn dl).
Proof.
	all: intro l; destruct l as [|tl bl]; [|destruct bl]; intros n dbn dl dd Hn Hdd;
		assert (Hd1 : BinNat.dt_dec (1 :: dbn) = (true, 0 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		assert (Hd0 : BinNat.dt_dec (0 :: dbn) = (false, 1 :: dd))
			by (simpl; rewrite Hdd; reflexivity);
		(destruct n as [|tn bn]; [|destruct bn; apply BinNat.is_canonical_tl in Hn as Htn]);
		try apply I; simpl.
	+	eapply lift_conseq, open_aux_inc, Hd0; [|assumption]; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hd1; trivial.
	+	destruct tn; eapply lift_conseq, open_aux_dt_true, Hd1; trivial.
	+	destruct tn; [|eapply lift_conseq, open_aux_inc, Hd0; [|assumption]; trivial].
		unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	eapply lift_conseq, open_borrow_dt_true, Hd1; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hd1; trivial.
	+	eapply lift_conseq, open_borrow_inc, Hd0; trivial.
	+	unfold dec_zip; simpl.
		rewrite Hdd; reflexivity.
	+	eapply lift_conseq, open_aux_inc, Hd0; trivial.
	+	eapply lift_conseq, open_borrow_dt_true, Hd1; simpl.
		intros x Hx.
		rewrite open_aux_borrow_inc; assumption.
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

Lemma open_inc : forall (l : RAL) n,
		BinNat.is_canonical n ->
		open l (BinNat.inc n) = option_bind (open l n) dec_zip.
Proof.
	intros l n Hn.
	unfold open.
	pose proof (Hnone := open_borrow_inc_None l n [] [] [] Hn).
	pose proof (Hsome := open_borrow_inc l n [] [] [] Hn eq_refl).
	{	destruct open_borrow as [z|]; simpl in *.
	+	assumption.
	+	apply Hnone; reflexivity.
	}
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

Lemma scatter_dec_aux : forall dn tl t dd,
		is_precanonical tl ->
		CLBT.is_valid (length dn) t ->
		BinNat.dt_dec dn = (true, dd) ->
		tail ((uncurry cons_tree) (scatter t tl dn)) = (uncurry cons_tree) (scatter t tl dd).
Proof.
	intros dn.
	{	induction dn as [|bn tdn HR]; [|destruct bn];
			intros tl t dd Htl Ht Hdd; simpl in *.
	+	discriminate.
	+	destruct BinNat.dt_dec as [b tdd], b; [|discriminate].
		inversion_clear Hdd; simpl.
		inversion_clear Ht; simpl.
		apply canonical_safe_zero in Htl.
		apply HR; [assumption..|reflexivity].
	+	pose proof (Hz := BinNat.dt_dec_zero tdn).
		pose proof (Hl := BinNat.dt_dec_length tdn).
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
			pose proof (Hc := scatter_precanonical
								  (repeat 0 (length tdn)) r (One l :: tl) Htl).
			destruct scatter as [st sr]; simpl in *.
			unfold tail.
			rewrite cons_uncons, Hzs, Hl; [reflexivity|discriminate|assumption].
		}
	}
Qed.*)

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
	pose proof (Hv := open_valid l Ob (wf_valid _ Hl)).
	pose proof (Hz := open_zipper l Ob).

	destruct open as [z|]; [|apply I]; simpl.
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

Lemma drop_inc : forall l n,
		is_canonical_struct 0 l -> BinNat.is_canonical_struct n ->
		tail (drop l n) = drop l (BinNat.inc n).
Proof.
	intros l n Hl Hn.
	destruct Hl as [Hvl Hl].
	unfold drop.
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
Qed.

Lemma drop_as_tail : forall l n,
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
(*

Lemma lookup_drop : forall l n,
		is_valid l ->
		lookup l n = head (drop l n).
Proof.
	intros l n Hl.
	unfold lookup, drop.
	pose proof (Hv := open_valid l n).
	destruct (open l n) as [zip|]; [|reflexivity].
	specialize (Hv zip Hl eq_refl).
	destruct Hv as [_ _ Ht Hlen].
	destruct zip as [tl dl t an]; simpl in *.
	rewrite <- Hlen in Ht.
	pose proof (CLBT.open_lookup t an Ht).
	destruct CLBT.open.
	pose proof (Hsl := scatter_lookup an t (safe_zero tl) Ht).
	destruct scatter; simpl in *.
	rewrite Hsl.
	symmetry.
	apply head_cons.
Qed.

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

Section Theory.

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

Theorem lookup_update_neq : forall l n m a,
		is_well_formed l ->
                BinNat.is_canonical n ->
                BinNat.is_canonical m ->
		n <> m ->
                option_bind (RAL.update l n a) (fun l =>
                RAL.lookup l m) = RAL.lookup l m.
Admitted.
(*
Proof.
	intros l n m a Hl Hn Hm H.
	apply RAL.canonical_valid in Hl as Hvl.
	apply strip_canonical in Hl as Hsl.
	pose proof (Hzupdate := RAL.open_zipper l n).
	pose proof (Hzlookup1 := RAL.open_zipper (RAL.update l n a) m).
	pose proof (Hzlookup2 := RAL.open_zipper l m).
	assert (Hvupdate : forall zip,
			RAL.open l n = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	assert (Hvlookup2 : forall zip,
			RAL.open l m = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	pose proof (Hupdate := open_gtb l n).
	pose proof (Hlookup1 := open_gtb (RAL.update l n a) m).
	pose proof (Hlookup2 := open_gtb l m).
	pose proof (Hcgt := BinNat.gtb_decomp_neq (RAL.strip l) _ _ H).
	rewrite update_strip, <- Hlookup2 in Hlookup1; [|assumption..].
	unfold RAL.lookup, RAL.update in *.
	destruct (RAL.open l n) as [zip|]; [|reflexivity].
	destruct (BinNat.gtb_decomp (RAL.strip l) n) as [decompn|]; [|discriminate].
	destruct (BinNat.gtb_decomp (RAL.strip l) m) as [decompm|],
		(RAL.open _ m) as [zipl1|], (RAL.open l m) as [zipl2|];
		try discriminate; [|reflexivity].
	specialize (Hvupdate zip eq_refl).
	specialize (Hzupdate zip eq_refl).
	specialize (Hzlookup1 zipl1 eq_refl).
	specialize (Hzlookup2 zipl2 eq_refl).
	specialize (Hvlookup2 zipl2 eq_refl).
	specialize (Hcgt decompn decompm Hsl Hn Hm eq_refl eq_refl).
	destruct zip as [tl dl t nb], zipl1 as [tl1 dl1 t1 nb1], zipl2 as [tl2 dl2 t2 nb2],
		decompn as [tn dn an], decompm as [tm dm am].
	f_equal.
	unfold RAL.is_zipper, RAL.plug in *.
	simpl in *.
	inversion Hlookup1 as [(Htl, Hdl, Hnb)].
	destruct Hvupdate as [_ _ Ht Hlnl]; simpl in Ht, Hlnl.
	destruct Hvlookup2 as [_ _ _ Hlnl2]; simpl in Hlnl2.
	apply (f_equal (@length BinNat.Bit)) in Hdl.
	rewrite !RAL.strip_length in Hdl.
	rewrite !rev_append_rev in *.
	{	destruct (PeanoNat.Nat.eq_dec (length dl) (length dl1)) as [Hlen|Hlen].
	+	rewrite <- Hlen in Hdl.
		pose proof (Hldl_copy := Hdl).
		rewrite <- (rev_length dl1), <- (rev_length dl) in Hlen.
		rewrite <- (rev_length dl2), <- (rev_length dl) in Hdl.
		apply (f_equal (fun l => nth (length (rev dl)) l RAL.Zero)) in Hzlookup1.
		rewrite nth_middle, Hlen, nth_middle in Hzlookup1.
		inversion_clear Hzlookup1.
		rewrite Hzlookup2 in Hzupdate.
		apply (f_equal (fun l => nth (length (rev dl)) l RAL.Zero)) in Hzupdate.
		rewrite nth_middle, Hdl, nth_middle in Hzupdate.
		inversion_clear Hzupdate.
		{	apply CLBT.lookup_update_neq.
		+	rewrite !BinNat.complement_length, Hlnl2, Hlnl.
			assumption.
		+	inversion_clear Hupdate.
			inversion_clear Hlookup2.
			intro Hc.
			apply BinNat.complement_inj in Hc.
			contradiction.
		+	rewrite BinNat.complement_length, Hlnl.
			assumption.
		}
	+	apply (f_equal (fun l => nth (length (rev dl1)) l (RAL.One t))) in Hzlookup1.
		rewrite nth_middle in Hzlookup1.
		{	rewrite (list_select_neq _ (rev dl) tl _
						 (RAL.One (RAL.CLBT.update t (BinNat.complement nb) a)))
				in Hzlookup1.
		+	simpl in Hzlookup1.
			rewrite <- (rev_length dl2), <- (rev_length dl1) in Hdl.
			rewrite <- Hzupdate, Hzlookup2, Hdl, nth_middle in Hzlookup1.
			inversion_clear Hzlookup1.
			reflexivity.
		+	rewrite !rev_length.
			symmetry.
			assumption.
		}
	}
Qed.
*)

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
