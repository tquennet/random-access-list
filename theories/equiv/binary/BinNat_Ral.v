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

Theorem open_compare : forall l n,
		RAL.is_valid l ->
	 	open_compare_map (RAL.open l n) =
		compare_forget (BinNat.compare (RAL.strip l) n).
Proof.
	intros l n Hl.
	unfold BinNat.compare, RAL.open.
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
	unfold BinNat.sub, RAL.drop.
	pose proof (H := open_compare l n Hl).
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

Lemma RAL_plug_strip : forall dl (l : @RAL.t A),
	  RAL.strip (RAL.plug l dl) = rev_append (RAL.strip dl) (RAL.strip l).
Proof.
	intro dl.
	{	induction dl as [|bl tdl HR]; [|destruct bl]; intro l; simpl.
	+	reflexivity.
	+	apply HR.
	+	apply HR.
	}
Qed.

Theorem RAL_update_strip : forall l n (a : A),
		RAL.is_valid l ->
		RAL.strip (RAL.update l n a) = RAL.strip (RAL.trim l).
Proof.
	intros l n a H.
	unfold RAL.update.
	pose proof (Hoc := open_compare l n H).
	pose proof (Hcomp := BinNat.compare_decomp_Gt (RAL.strip l) n).
	{	destruct RAL.open as [zip|],
			BinNat.compare as [|rtn rdn ran|rtn rdn ran]; try discriminate.
	+	destruct zip as [tl dl t nb]; simpl in *.
		destruct (Hcomp rtn rdn ran) as [Hl Hz Hval]; [reflexivity|].
		destruct CLBT.open as [ot odt]; simpl.
		rewrite RAL_plug_strip, trim_strip, Hz.
		inversion_clear Hoc.
		reflexivity.
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
