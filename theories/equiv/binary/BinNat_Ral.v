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

Definition open_forget :=
	option_map (fun zip : (@RAL.zipper A) => BinNat.mkZip (RAL.strip zip.(RAL.zip_tl))
						(RAL.strip zip.(RAL.zip_dl)) (zip.(RAL.zip_nb))).

Lemma open_gtb_aux : forall l n dl dn,
		open_forget (RAL.open_aux l n dn dl)
			= BinNat.gtb_decomp_aux (RAL.strip l) n (RAL.strip dl) dn
		/\ open_forget (RAL.open_borrow l n dn dl)
			= BinNat.gtb_decomp_borrow (RAL.strip l) n (RAL.strip dl) dn.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dl dn;
			(destruct n as [|bn tn]; [|destruct bn]); split; simpl; try reflexivity.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	destruct tn; [reflexivity|].
		apply HR.
	+	apply HR.
	}
Qed.
Lemma open_gtb : forall l n, open_forget (RAL.open l n)
							   = BinNat.gtb_decomp (RAL.strip l) n.
Proof.
	intros l n.
	apply open_gtb_aux.
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
	pose proof (Hoc := open_gtb l n).
	pose proof (Hcomp := BinNat.gtb_decomp_is_decomp (RAL.strip l) n).
	{	destruct RAL.open as [zip|], BinNat.gtb_decomp as [decomp|];
			try discriminate.
	+	specialize (Hcomp decomp Hn eq_refl).
		destruct zip as [tl dl t nb], decomp as [rtn rdn ran]; simpl in *.
		destruct Hcomp as [Hln Hz Hval].
		rewrite plug_strip, Hz.
		inversion_clear Hoc.
		reflexivity.
	+	reflexivity.
	}
Qed.

Theorem update_canonical : forall l n (a : A),
		RAL.is_canonical l -> BinNat.is_canonical n ->
		RAL.is_canonical (RAL.update l n a).
Proof.
	intros l n a Hl Hn.
	unfold RAL.is_canonical.
	rewrite update_strip; assumption.
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
	unfold RAL.is_canonical.
	rewrite create_strip.
	assumption.
Qed.

End BinNatRal.
