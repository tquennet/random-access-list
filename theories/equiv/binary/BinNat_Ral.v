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

Definition open_compare_map :=
	option_map (fun '((dl, _, tl, dn) : ((@RAL.dt A) * (@CLBT.t A) * (@RAL.t A) * BinNat.t))
		=> (RAL.strip dl, RAL.strip tl, dn)).
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

Theorem open_borrow_compare_aux : forall l n dn dl an am,
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

Theorem open_borrow_compare : forall l n,
		RAL.is_valid l ->
	 	open_compare_map (RAL.open_borrow (RAL.trim l) (BinNat.trim n) [] []) =
		compare_forget (BinNat.compare (RAL.strip l) n).
Proof.
	intros l n Hl.
	unfold BinNat.compare.
	pose proof (Hnone := BinNat.compare_aux_none (RAL.strip (RAL.trim l)) (BinNat.trim n) [] [] [] []).
	pose proof (H := open_borrow_compare_aux (RAL.trim l) (BinNat.trim n) [] [] [] []).
	rewrite <- trim_strip.
	{	destruct BinNat.compare_aux; simpl.
	+	apply H.
		apply RAL.is_canonical_struct_equiv, RAL.trim_canonical.
		assumption.
	+	exfalso.
		rewrite trim_strip in Hnone.
		apply Hnone; [apply BinNat.trim_canonical..|reflexivity].
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
	intros l n Hl.
	unfold BinNat.sub, RAL.drop, RAL.open.
	pose proof (H := open_borrow_compare l n Hl).
	pose proof (Hv := RAL.open_aux_valid (RAL.trim l) (BinNat.trim n) [] []).
	{	destruct RAL.open_borrow as [p|] eqn:He, BinNat.compare as [| |tn dn an];
			simpl in*; try discriminate.
	+	destruct p as [p rn], p as [p rtl], p as [rdl t].
		pose proof (Hopen := CLBT.open_trace rn (length rn) (length rn) (CLBT.make_zip t)).
		destruct CLBT.open as [ot odt].
		rewrite trim_strip, RAL.cons_aux_inc_strip.
		repeat f_equal.
		simpl in Hopen.
		{	destruct (Hv rdl t rtl rn) as [Ht Hrdl Hrtl Hlen].
		+	right.
			reflexivity.
		+	apply RAL.trim_valid.
			assumption.
		+	apply RAL.valid_DNil.
		+	rewrite DCLBT_to_RAL_strip.
			pose proof (le_n (length rn)).
			rewrite Hopen; [|split; [rewrite Hlen; assumption|apply CLBT.valid_DRoot]
						   |assumption].
			inversion_clear H.
			rewrite !rev_append_rev, app_nil_r.
			reflexivity.
		}
	+	reflexivity.
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
