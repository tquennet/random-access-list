Require Import Lists.List FunInd.
Require Import utils.Utils.
Require numerical.binary.BinNat structure.binary.Ral structure.tree.Clbt.
Import ListNotations.
Import BinNat.Notations.

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

Definition open_compare_map :=
	option_map (fun zip : (@RAL.zipper A) =>(RAL.strip zip.(RAL.zip_dl),
						 RAL.strip zip.(RAL.zip_tl), zip.(RAL.zip_nb))).
Definition compare_forget comp :=
	match comp with
	| BinNat.Gt tn dn an => Some (dn, tn, an)
	| _ => None
	end.
Definition compare_forget_opt := option_join compare_forget.

Lemma open_borrow_compare_empty : forall l an dl,
		RAL.is_canonical_struct (length dl) l -> l <> [] ->
		open_compare_map (RAL.open_borrow l [] an dl) =
		compare_forget (BinNat.uc_Gt (BinNat.compare_empty (RAL.strip l) (RAL.strip dl) an)).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl];
			intros an dl Hl He; simpl.
	+	contradiction.
	+	apply proj2 in Hl as Hvl.
		assert (tl <> []) by (destruct tl; discriminate).
		apply RAL.is_canonical_struct_tl in Hl.
		apply HR; assumption.
	+	reflexivity.
	}
Qed.

Lemma open_aux_compare_borrow : forall l n dn dl an am,
		RAL.is_canonical_struct (length dl) l ->
	 	open_compare_map (RAL.open_aux l n an dl) =
		compare_forget_opt (BinNat.compare_borrow_m (RAL.strip l) n (RAL.strip dl) dn an am)
		/\ open_compare_map (RAL.open_borrow l n an dl) =
		compare_forget_opt (BinNat.compare_borrow_n (RAL.strip l) n (RAL.strip dl) dn an am).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; intros n dn dl an am Hl;
			[|destruct bl; apply RAL.is_canonical_struct_tl in Hl as Htl];
			(destruct n as [|bn tn]; [|destruct bn]);
			split; simpl; try reflexivity.
	+	destruct BinNat.compare_empty as [r1 r3], r1; reflexivity.
	+	apply proj2 in Hl as Hl2.
		assert (tl <> []) by (destruct tl; discriminate).
		apply open_borrow_compare_empty; assumption.
	+	apply HR; assumption.
	+	apply HR; assumption.
	+	apply HR; assumption.
	+	apply HR; assumption.
	+	destruct tl as [|bl tl]; [|destruct bl]; reflexivity.
	+	apply HR; assumption.
	+	{	destruct tl as [|bl tl].
			+	simpl.
				destruct tn; [reflexivity|].
				destruct BinNat.compare_empty as [r1 r3], r1.
				reflexivity.
			+	destruct bl; apply HR; assumption.
		}
	+	destruct tn; [reflexivity|].
		apply HR; assumption.
	+	destruct tl as [|bl tl]; [reflexivity|].
		destruct bl; apply HR; assumption.
	}
Qed.

Lemma open_borrow_compare_aux : forall l n dn dl an am,
		RAL.is_canonical_struct (length dl) l ->
	 	open_compare_map (RAL.open_borrow l n an dl) =
		compare_forget_opt (BinNat.compare_aux (RAL.strip l) n (RAL.strip dl) dn an am).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; intros n dn dl an am Hl;
			[|destruct bl; apply RAL.is_canonical_struct_tl in Hl as Htl];
			(destruct n as [|bn tn]; [|destruct bn]);
			simpl; try reflexivity.
	+	destruct BinNat.compare_empty as [r1 r3], r1.
		reflexivity.
	+	apply proj2 in Hl.
		assert (tl <> []) by (destruct tl; discriminate).
		apply open_borrow_compare_empty; assumption.
	+	apply HR; assumption.
	+	apply open_aux_compare_borrow; assumption.
	+	apply open_aux_compare_borrow; assumption.
	+	apply HR; assumption.
	}
Qed.

Theorem open_compare : forall l n,
		RAL.is_canonical l -> BinNat.is_canonical n ->
	 	open_compare_map (RAL.open l n) =
		compare_forget (BinNat.compare (RAL.strip l) n).
Proof.
	intros l n Hl Hn.
	unfold BinNat.compare, RAL.open.
	pose proof (Hnone := BinNat.compare_aux_none (RAL.strip l) n [] [] [] []).
	pose proof (H := open_borrow_compare_aux l n [] [] [] []).
	{	destruct BinNat.compare_aux; simpl.
	+	apply H.
		apply RAL.is_canonical_struct_equiv.
		assumption.
	+	exfalso.
		apply RAL.strip_canonical in Hl.
		apply Hnone; [assumption..|reflexivity].
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
		RAL.is_canonical l -> BinNat.is_canonical n ->
		RAL.strip (RAL.drop l n) = BinNat.sub (RAL.strip l) n.
Proof.
	intros l n Hl Hn.
	apply RAL.canonical_valid in Hl as Hvl.
	unfold BinNat.sub, RAL.drop.
	pose proof (H := open_compare l n Hl Hn).
	pose proof (Hv := RAL.open_valid l n).
	{	destruct RAL.open as [zip|] eqn:He, BinNat.compare as [| |tn dn an];
			simpl in*; try discriminate.
	+	destruct (Hv zip) as [_ _ Ht Hlen]; [assumption|reflexivity|].			
		destruct zip as [tl dl t nb]; simpl in *.
		rewrite <- Hlen in Ht.
		pose proof (Hzv := CLBT.make_zip_valid _ _ Ht).
		pose proof (Hopen := CLBT.open_trace nb (length nb) (length nb) _ Hzv).
		destruct CLBT.open as [ot odt].
		rewrite trim_strip, RAL.cons_aux_inc_strip.
		repeat f_equal.
		simpl in Hopen.
		rewrite DCLBT_to_RAL_strip, Hopen; [|apply le_n].
		rewrite !rev_append_rev, app_nil_r.
		inversion_clear H.
		reflexivity.
	+	reflexivity.
	+	reflexivity.
	}
Qed.

Lemma plug_strip : forall dl (l : @RAL.t A),
	  RAL.strip (RAL.plug l dl) = rev_append (RAL.strip dl) (RAL.strip l).
Proof.
	intro dl.
	{	induction dl as [|bl tdl HR]; [|destruct bl]; intro l; simpl.
	+	reflexivity.
	+	apply HR.
	+	apply HR.
	}
Qed.

Theorem update_strip : forall l n (a : A),
		RAL.is_canonical l -> BinNat.is_canonical n ->
		RAL.strip (RAL.update l n a) = RAL.strip l.
Proof.
	intros l n a Hl Hn.
	unfold RAL.update.
	apply strip_canonical in Hl as Hsl.
	pose proof (Hoc := open_compare l n Hl Hn).
	pose proof (Hcomp := BinNat.compare_decomp_Gt (RAL.strip l) n).
	{	destruct RAL.open as [zip|],
			BinNat.compare as [|rtn rdn ran|rtn rdn ran]; try discriminate.
	+	destruct zip as [tl dl t nb]; simpl in *.
		destruct (Hcomp rtn rdn ran) as [Hln Hz Hval]; [assumption..|reflexivity|].
		rewrite plug_strip, Hz.
		inversion_clear Hoc.
		reflexivity.
	+	reflexivity.
	+	reflexivity.
	}
Qed.

Lemma update_canonical : forall l n (a : A),
		RAL.is_canonical l -> BinNat.is_canonical n ->
		RAL.is_canonical (RAL.update l n a).
Proof.
	intros l n a Hl Hn.
	apply RAL.canonical_valid in Hl as Hvl.
	apply strip_canonical in Hl as Hsl.
	apply BinNat.is_canonical_struct_equiv in Hsl.
	apply RAL.is_canonical_struct_equiv.
	split; [apply RAL.update_valid; assumption|].
	rewrite update_strip; assumption.
Qed.

Theorem lookup_none : forall (l : @RAL.t A) n,
		RAL.is_canonical l -> BinNat.is_canonical n ->
		n <? (RAL.strip l) = false -> RAL.lookup l n = None.
Proof.
	intros l n Hl Hn H.
	unfold BinNat.ltb, RAL.lookup in *.
	rewrite BinNat.compare_sym in H.
	pose proof (Hco := open_compare l n Hl Hn).
	destruct RAL.open, (BinNat.compare (RAL.strip l) n); try discriminate.
	all : reflexivity.
Qed.

Theorem update_id : forall l n (a : A),
		RAL.is_canonical l -> BinNat.is_canonical n ->
		n <? (RAL.strip l) = false -> RAL.update l n a = l.
Proof.
	intros l n a Hl Hn H.
	unfold BinNat.ltb, RAL.update in *.
	rewrite BinNat.compare_sym in H.
	pose proof (Hco := open_compare l n Hl Hn).
	destruct RAL.open, (BinNat.compare (RAL.strip l) n); try discriminate.
	all : reflexivity.
Qed.

Theorem lookup_update_eq : forall (l : @RAL.t A) n a,
		RAL.is_canonical l -> BinNat.is_canonical n ->
		n <? (RAL.strip l) = true ->
		RAL.lookup (RAL.update l n a) n = Some a.
Proof.
	intros l n a Hl Hn H.

	(* hypothèses utiles *)
	apply BinNat.ltb_rev in H.
	apply RAL.canonical_valid in Hl as Hvl.
	destruct H as [tn H], H as [dn H], H as [an H].
	pose proof (Hzlookup := RAL.open_zipper (RAL.update l n a) n).
	assert (Hvupdate : forall zip,
			RAL.open l n = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	pose proof (Hupdate := open_compare l n Hl Hn).
	pose proof (Hlookup := open_compare _ n (update_canonical _ _ a Hl Hn) Hn).
	rewrite update_strip in Hlookup; [|assumption..].
	rewrite H in Hlookup, Hupdate.

	(* élimination des cas impossibles *)
	unfold RAL.lookup, RAL.update in *.
	destruct (RAL.open l n) as [zip1|], RAL.open as [zip2|] eqn:Hz2; [|discriminate..].
	specialize (Hzlookup zip2 eq_refl).
	specialize (Hvupdate zip1 eq_refl).
	destruct zip1 as [tl1 dl1 t1 nb1], zip2 as [tl2 dl2 t2 nb2].
	unfold RAL.is_zipper, RAL.plug in *.
	simpl in *.

	(* décomposition *)
	inversion Hupdate as [(Hdl1, Htl1, Hnb1)].
	inversion Hlookup as [(Hdl2, Htl2, Hnb2)].
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
	assumption.
Qed.

Theorem lookup_update_neq : forall (l : @RAL.t A) n m a,
		RAL.is_canonical l -> BinNat.is_canonical n -> BinNat.is_canonical m ->
		n <> m ->	RAL.lookup (RAL.update l n a) m = RAL.lookup l m.
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
	pose proof (Hupdate := open_compare l n Hl Hn).
	pose proof (Hlookup1 := open_compare _ _ (update_canonical l n a Hl Hn) Hm).
	pose proof (Hlookup2 := open_compare l m Hl Hm).
	pose proof (Hcgt := BinNat.compare_neq_gt (RAL.strip l) _ _ H).
	rewrite update_strip, <- Hlookup2 in Hlookup1; [|assumption..].
	unfold RAL.lookup, RAL.update in *.
	destruct (RAL.open l n) as [zip|]; [|reflexivity].
	destruct (BinNat.compare (RAL.strip l) n) as [| |tn dn an]; [discriminate..|].
	destruct (BinNat.compare (RAL.strip l) m) as [| | tlm dlm alm],
		(RAL.open _ m) as [zipl1|], (RAL.open l m) as [zipl2|];
		try discriminate; [reflexivity..|].
	specialize (Hvupdate zip eq_refl).
	specialize (Hzupdate zip eq_refl).
	specialize (Hzlookup1 zipl1 eq_refl).
	specialize (Hzlookup2 zipl2 eq_refl).
	specialize (Hvlookup2 zipl2 eq_refl).
	destruct zip as [tl dl t nb], zipl1 as [tl1 dl1 t1 nb1], zipl2 as [tl2 dl2 t2 nb2].
	f_equal.
	specialize (Hcgt tn dn an tlm dlm alm Hsl Hn Hm eq_refl eq_refl).
	unfold RAL.is_zipper, RAL.plug in *.
	simpl in *.
	inversion Hlookup1 as [(Hdl, Htl, Hnb)].
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
		+	rewrite Hlnl2, Hlnl.
			assumption.
		+	inversion_clear Hupdate.
			inversion_clear Hlookup2.
			assumption.
		+	rewrite Hlnl.
			assumption.
		}
	+	apply (f_equal (fun l => nth (length (rev dl1)) l (RAL.One t))) in Hzlookup1.
		rewrite nth_middle in Hzlookup1.
		{	rewrite (list_select_neq _ (rev dl) tl _ (RAL.One (RAL.CLBT.update t nb a)))
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
