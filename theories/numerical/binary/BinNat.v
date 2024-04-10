Require Import Lists.List FunInd .
Require Import utils.Utils.
Import ListNotations.

Declare Scope bin_nat_scope.
Open Scope bin_nat_scope.

(********************************************************************************)
(*	Notations are defined in bin_nat_scope.										*)
(*	t == the type of binary numbers (lsb first).								*)
(*	dt == the type of binary numbers (msb first).								*)
(*	is_canonical == a predicate identifying canonical BinNat					*)
(*		zero  == a binary number representing 0									*)
(*			+: canonical_0 : is_canonical zero									*)
(*		inc n == the successor of n												*)
(*			+: canonical_inc n : is_canonical n -> is_canonical (inc n)			*)
(*																				*)
(*	**	Unary operator:															*)
(*			 to_nat n == n as native coq nat									*)
(*				dec n == the predecessor of n									*)
(*			   trim n == the canonical version of n								*)
(*	**	Binary operators:														*)
(*		 sub n m, n - m == the difference between n and m						*)
(*	** Lemmes:																	*)
(*		trim_canonical : forall n, is_canonical (trim n)						*)
(*		dec_canonical : forall n, is_canonical n -> is_canonical (dec n)		*)
(*		sub_canonical : forall n m, is_canonical (n - m)						*)
(*																				*)
(*		trim_to_nat : forall n, to_nat n = to_nat (trim n)						*)
(*		inc_S : forall n, to_nat (inc n) = S (to_nat n)							*)
(*		dec_pred : forall n, to_nat (dec n) = pred (to_nat n)					*)
(*		sub_minus : forall n m, to_nat (n - m) = (to_nat n - to_nat m)%nat		*)
(********************************************************************************)

Variant Bit := Zero | One.
Definition t := list Bit.
Definition dt := t.

Notation "0" := Zero.
Notation "1" := One.

Fixpoint to_nat n : nat :=
	match n with
	| [] => O
	| 0 :: t => 2 * (to_nat t)
	| 1 :: t => S (2 * to_nat t)
	end.

Definition zero : t := [].
Notation def_zero := (option_default zero).

Fixpoint inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 :: inc t
	end.

Functional Scheme inc_ind := Induction for inc Sort Prop.

Theorem inc_S : forall n, to_nat (inc n) = S (to_nat n).
Proof.
	intro n.
	{	functional induction (inc n); simpl.
	+	reflexivity.
	+	reflexivity.
	+	rewrite IHl.
		rewrite <- !plus_n_O, plus_Sn_m, <- plus_n_Sm.
		reflexivity.
	}
Qed.

Inductive is_canonical : t -> Prop :=
	| canonical_0 : is_canonical []
	| canonical_inc : forall (n : t),
		is_canonical n -> is_canonical (inc n).

Local Lemma canonical_1 : is_canonical [1].
Proof.
	replace [1] with (inc []) by reflexivity.
	apply canonical_inc, canonical_0.
Qed.

(*Lemma canonical_unicity : forall n m,
	is_canonical n -> is_canonical m ->
	to_nat n = to_nat m ->
	n = m.
Proof.
	intros n m Hn.
	generalize dependent m.
	{	induction Hn as [|n Hn HR]; intros m Hm Heq; destruct Hm as [|m Hm].
	+	reflexivity.
	+	rewrite inc_S in Heq.
		discriminate.
	+	rewrite inc_S in Heq.
		discriminate.
	+	f_equal.
		apply HR; [assumption|].
		rewrite !inc_S in Heq.
		injection Heq as Heq.
		assumption.
	}
Qed.*)

Fixpoint is_canonical_struct_fix b n :=
	match n with
	| [] => b
	| 0 :: tn => is_canonical_struct_fix false tn
	| 1 :: tn => is_canonical_struct_fix true tn
	end.

Definition is_canonical_struct n := is_canonical_struct_fix true n = true.

Local Lemma is_canonical_struct_false : forall n,
	is_canonical_struct_fix false n = true -> is_canonical_struct n.
Proof.
	intros n H.
	destruct n; [inversion_clear H|].
	assumption.
Qed.

Local Lemma is_canonical_struct_cons : forall b0 b1 n,
	is_canonical_struct (b1 :: n) -> is_canonical_struct (b0 :: b1 :: n).
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

Local Lemma is_canonical_struct_tl : forall b n, is_canonical_struct (b :: n) -> is_canonical_struct n.
Proof.
	intros b n H.
	{	destruct n.
	+	reflexivity.
	+	destruct b; destruct b0; assumption.
	}
Qed.

Local Lemma inc_decomp : forall (n : t),
	exists b tn, b :: tn = inc n.
Proof.
	intros n.
	{	destruct n as [|b tn]; [|destruct b].
	+	exists 1, []; reflexivity.
	+	exists 1, tn; reflexivity.
	+	exists 0, (inc tn); reflexivity.
	}
Qed.

Local Lemma inc_non_empty : forall n, inc n <> [].
Proof.
	intro n.
	pose (H := inc_decomp n).
	destruct H as [b H], H as [t H].
	rewrite <- H.
	discriminate.
Qed.

Local Lemma is_canonical_inc_struct : forall (n : t),
	is_canonical_struct n ->
	is_canonical_struct (inc n).
Proof.
	intros n H.
	{	functional induction (inc n).
	+	reflexivity.
	+	destruct t0; [discriminate|].
		exact H.
	+	apply IHl in H.
		pose proof (Hinc := inc_decomp t0).
		destruct Hinc as [b Hinc], Hinc as [tn Hinc].
		rewrite <- Hinc in *.
		apply is_canonical_struct_cons.
		assumption.
	}
Qed.

Local Lemma canonical_double : forall (n : t),
	is_canonical n -> is_canonical (0 :: (inc n)).
Proof.
	intros n H.
	{	induction H.
	+	replace (0 :: inc []) with (inc (inc [])) by reflexivity.
		apply canonical_inc, canonical_inc, canonical_0.
	+	apply canonical_inc, canonical_inc in IHis_canonical.
		simpl in IHis_canonical.
		assumption.
	}
Qed.

Local Lemma is_canonical_struct_equiv : forall (n : t),
	is_canonical n <-> is_canonical_struct n.
Proof.
	intro n.
	{	split; intro H.
	+	{	induction H as [|n H].
		+	reflexivity.
		+	apply is_canonical_inc_struct.
			assumption.
		}
	+	{	induction n as [|bn tn].
		+	apply canonical_0.
		+	destruct tn; [destruct bn; [discriminate|apply canonical_1]|].
			assert (Ht : is_canonical_struct (b :: tn)) by (destruct bn; assumption).
			apply IHtn in Ht.
			{	destruct Ht, bn.
			+	discriminate.
			+	apply canonical_1.
			+	apply canonical_double.
				assumption.
			+	replace (1 :: inc n) with (inc (0 :: inc n)) by reflexivity.
				apply canonical_inc.
				apply canonical_double.
				assumption.
			}
		}
	}
Qed.

Fixpoint trim n :=
	match n with
	| [] => []
	| 1 :: tl => 1 :: (trim tl)
	| 0 :: tl => match (trim tl) with
		| [] => []
		| r => 0 :: r
		end
	end.

Functional Scheme trim_ind := Induction for trim Sort Prop.

Lemma trim_canonical : forall l, is_canonical (trim l).
Proof.
	intro l.
	apply is_canonical_struct_equiv.
	{	functional induction (trim l).
	+	reflexivity.
	+	reflexivity.
	+	rewrite e1 in IHl0.
		apply IHl0.
	+	apply IHl0.
	}
Qed.

Lemma trim_nat : forall l, to_nat (trim l) = to_nat l.
Proof.
	intro l.
	{	functional induction (trim l); simpl.
	+	reflexivity.
	+	rewrite <- IHl0, e1.
		reflexivity.
	+	rewrite <- IHl0, e1.
		reflexivity.
	+	rewrite IHl0.
		reflexivity.
	}
Qed.

Fixpoint dec_aux n :=
	match n with
	| [] => None
	| [1] => Some []
	| 1 :: t => Some (0 :: t)
	| 0 :: t => option_map (fun r => 1 :: r) (dec_aux t)
	end.

Functional Scheme dec_aux_ind := Induction for dec_aux Sort Prop.

Definition dec n := def_zero (dec_aux n).

Lemma inc_dec : forall (n : t),
	is_canonical n -> dec (inc n) = n.
Proof.
	intros n Hn.
	unfold dec.
	enough (forall n, is_canonical n -> dec_aux (inc n) = Some n);
		[apply H in Hn; rewrite Hn; reflexivity|].
	clear n Hn.
	intros n Hn.
	apply is_canonical_struct_equiv in Hn.
	{	functional induction (inc n).
	+	reflexivity.
	+	destruct t0; [discriminate|].
		reflexivity.
	+	simpl.
		destruct t0; [reflexivity|].
		apply IHl in Hn.
		rewrite Hn.
		reflexivity.
	}
Qed.

Local Lemma dec_aux_None : forall n, dec_aux n = None <-> to_nat n = O.
Proof.
	intro n.
	{	split; intro H; functional induction (dec_aux n); simpl in *.
	+	reflexivity.
	+	destruct (dec_aux t0); [discriminate|].
		rewrite IHo; reflexivity.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	+	apply PeanoNat.Nat.eq_add_0 in H; destruct H as [H _].
		rewrite H in IHo.
		rewrite IHo; reflexivity.
	+	discriminate.
	+	destruct _x; [discriminate|].
		rewrite plus_Sn_m in H.
		discriminate.
	}
Qed.

Theorem dec_pred : forall n,
	to_nat (dec n) = pred (to_nat n).
Proof.
	intros n.
	unfold dec.
	{	functional induction (dec_aux n); simpl in *.
	+	reflexivity.
	+	{	apply option_default_map_inv.
		+	intro eq.
			apply dec_aux_None in eq.
			rewrite eq.
			reflexivity.
		+	intros n eq.
			rewrite eq in IHo.
			simpl in *.
			assert (to_nat t0 <> O)
				by (intro H; apply dec_aux_None in H; rewrite H in eq; discriminate).
			rewrite IHo, <- !plus_n_O, <- plus_Sn_m, <- PeanoNat.Nat.add_1_l.
			rewrite !PeanoNat.Nat.add_pred_r; [|assumption|assumption].
			rewrite PeanoNat.Nat.add_1_l.
			reflexivity.
		}
	+	reflexivity.
	+	reflexivity.
	}
Qed.

Lemma dec_canonical : forall (n : t),
	is_canonical n -> is_canonical (dec n).
Proof.
	intros n Hn.
	destruct Hn; [apply canonical_0|].
	rewrite inc_dec; assumption.
Qed.


Fixpoint sub_aux n m acc :=
	match n, m with
	| [], _ => None
	| _, [] => None (* unreachable from sub_borrow if m canonical *)
	| 1 :: tn, [1] => Some (rev_append acc (0 :: tn))
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> sub_aux tn tm (0 :: acc)
	| 1 :: tn, 0 :: tm => sub_aux tn tm (1 :: acc)
	| 0 :: tn, 1 :: tm => sub_borrow tn tm (1 :: acc)
	end
with sub_borrow n m acc :=
	match n, m with
	| [], _ => None
	| 1 :: tn, [] => Some (rev_append acc (0 :: tn))
	| 0 :: tn, [] => sub_borrow tn [] (1 :: acc)
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm
		=> sub_borrow tn tm (1 :: acc)
	| 0 :: tn, 1 :: tm => sub_borrow tn tm (0 :: acc)
	| 1 :: tn, 0 :: tm => sub_aux tn tm (0 :: acc)
	end.

Definition sub n m :=
	match sub_borrow n (trim m) [] with
	| Some r => trim (inc r)
	| None => []
	end.

Notation "n - m" := (sub n m) : bin_nat_scope.	
		
Local Lemma sub_aux_borrow_app : forall n m a b,
		sub_aux n m (b ++ a) = option_map (rev_append a) (sub_aux n m b) /\
		sub_borrow n m (b ++ a) = option_map (rev_append a) (sub_borrow n m b).
Proof.
	intros n.
	{	induction n as [|bn tn HR]; intros m a b;
			[|destruct bn; (destruct m as [|bm tm]; [|destruct bm])];
			simpl; split.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	apply (HR [] a (1 :: b)).
	+	apply (HR tm a (0 :: b)).
	+	apply (HR tm a (1 :: b)).
	+	apply (HR tm a (1 :: b)).
	+	apply (HR tm a (0 :: b)).
	+	reflexivity.
	+	rewrite !rev_append_rev, rev_app_distr, app_assoc.
		reflexivity.
	+	apply (HR tm a (1 :: b)).
	+	apply (HR tm a (0 :: b)).
	+	{	destruct tm.
		+	simpl.
			rewrite !rev_append_rev, rev_app_distr, app_assoc.
			reflexivity.
		+	apply (HR (b0 :: tm) a (0 :: b)).
		}		
	+	apply (HR tm a (1 :: b)).
	}
Qed.
Local Lemma sub_aux_app : forall n m a, sub_aux n m a = option_map (rev_append a) (sub_aux n m []).
Proof.
	intros n m a.
	rewrite <- (app_nil_l a).
	apply sub_aux_borrow_app.
Qed.
Local Lemma sub_borrow_app : forall n m a, sub_borrow n m a = option_map (rev_append a) (sub_borrow n m []).
Proof.
	intros n m a.
	rewrite <- (app_nil_l a).
	apply sub_aux_borrow_app.
Qed.

Lemma sub_canonical : forall n m, is_canonical (n - m).
Proof.
	intros n m.
	unfold sub.
	destruct (sub_borrow n (trim m) []); [|apply canonical_0].
	apply trim_canonical.
Qed.

Local Lemma sub_aux_O_None : forall n a,
		sub_borrow n [] a = None <-> to_nat n = O.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn]; intro a; split; intro H; simpl in *.
	+	reflexivity.
	+	reflexivity.
	+	apply HR in H.
		rewrite H.
		reflexivity.
	+	rewrite <- plus_n_O in H.
		apply PeanoNat.Nat.eq_add_0 in H.
		destruct H as [H _].
		apply (HR (1 :: a)) in H.
		assumption.
	+	discriminate.
	+	discriminate.
	}
Qed.

Local Lemma pred_double_O : forall x, (pred (2 * x) = 0 -> x = 0)%nat.
Proof.
	intros x H.
	destruct x; [reflexivity|].
	rewrite PeanoNat.Nat.mul_succ_r, <- !plus_n_Sm in H.
	discriminate.
Qed.

Local Lemma sub_aux_None : forall n m a,
		is_canonical m ->
		(m <> [] -> sub_aux n m a = None <-> (S (to_nat n) - to_nat m = 0)%nat)
		/\ (sub_borrow n m a = None <-> (to_nat n - to_nat m = 0)%nat).
Proof.
	intros n m a Hm.
	apply is_canonical_struct_equiv in Hm.
	revert m a Hm.
	assert (H2 : forall x, (x + (x + 0) = 2 * x)%nat) by reflexivity.
	{	induction n as [|bn tn HR]; intros m a Hm;
			[|destruct bn; (destruct m as [|bm tm];
				[|destruct bm; apply is_canonical_struct_tl in Hm as Htm])];
				(split; [intro He; split; intro H | split; intro H]);
			try (reflexivity || discriminate || contradiction); simpl in H |- *.
	+	apply is_canonical_struct_equiv in Hm.
		destruct Hm; [contradiction|].
		rewrite inc_S.
		reflexivity.
	+	apply sub_aux_O_None in H.
		rewrite H.
		reflexivity.
	+	rewrite <- plus_n_O, PeanoNat.Nat.sub_0_r in H.
		apply PeanoNat.Nat.eq_add_0 in H.
		destruct H as [H _].
		apply (sub_aux_O_None _ (1 :: a)) in H.
		assumption.
	+	apply HR in H; [|assumption|destruct tm; discriminate].
		apply is_canonical_struct_equiv in Htm.
		destruct Htm as [|xm Hxm]; [discriminate|].
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm.
		rewrite inc_S, PeanoNat.Nat.sub_succ in H.
		rewrite !H2, PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		apply HR; [assumption| apply inc_non_empty|].
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm  in H.
		rewrite inc_S, PeanoNat.Nat.sub_succ.
		rewrite PeanoNat.Nat.sub_succ_r, !H2, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply pred_double_O in H.
		assumption.
	+	apply HR in H; [|assumption].
		rewrite !H2, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply HR; [assumption|].
		rewrite !H2, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply PeanoNat.Nat.eq_mul_0_r in H; [|discriminate].
		assumption.
	+	apply HR in H; [|assumption].
		rewrite !H2, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply HR; [assumption|].
		rewrite !H2, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply PeanoNat.Nat.eq_mul_0_r in H; [|discriminate].
		assumption.
	+	apply HR in H; [|assumption].
		rewrite !H2, PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply HR; [assumption|].
		rewrite !H2, PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply pred_double_O in H.
		assumption.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		apply HR in H; [|assumption|apply inc_non_empty].
		rewrite inc_S, PeanoNat.Nat.sub_succ in H.
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm, !H2, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		apply HR; [assumption|apply inc_non_empty|].
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm, !H2, <- PeanoNat.Nat.mul_sub_distr_l in H.
		rewrite inc_S, PeanoNat.Nat.sub_succ.
		apply PeanoNat.Nat.eq_mul_0_r in H; [|discriminate].
		assumption.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		apply HR in H; [|assumption|apply inc_non_empty].
		rewrite inc_S, PeanoNat.Nat.sub_succ in H.
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm, !H2,
			PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		apply HR; [assumption|apply inc_non_empty|].
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm, !H2,
			PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply pred_double_O in H.
		rewrite inc_S, PeanoNat.Nat.sub_succ, H.
		reflexivity.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		pose (Hd := inc_decomp xm).
		destruct Hd as [b Hd], Hd as [t Hd].
		rewrite <- Hd, Hd in H.
		apply HR in H; [|assumption|apply inc_non_empty].
		rewrite inc_S, PeanoNat.Nat.sub_succ in H.
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm, !H2,
			PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply is_canonical_struct_equiv in Htm as Hd.
		destruct Hd as [|xm Hxm]; [discriminate|].
		rewrite inc_S, !plus_Sn_m, <- plus_n_Sm, !H2,
			PeanoNat.Nat.sub_succ_r, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply pred_double_O in H.
		pose (Hd := inc_decomp xm).
		destruct Hd as [b Hd], Hd as [t Hd].
		rewrite <- Hd, Hd.
		apply HR; [assumption| apply inc_non_empty|].
		rewrite inc_S, PeanoNat.Nat.sub_succ, H.
		reflexivity.
	+	apply HR in H; [|assumption].
		rewrite !H2, <- PeanoNat.Nat.mul_sub_distr_l, H.
		reflexivity.
	+	apply HR; [assumption|].
		rewrite !H2, <- PeanoNat.Nat.mul_sub_distr_l in H.
		apply PeanoNat.Nat.eq_mul_0_r in H; [|discriminate].
		assumption.
	}
Qed.


Local Lemma sub_aux_Some : forall n m a x,
		is_canonical m ->
		(sub_aux n m a = Some (rev_append a x) -> (to_nat n - to_nat m = to_nat x)%nat)
		/\ (sub_borrow n m a = Some (rev_append a x) -> (to_nat n - S (to_nat m) = to_nat x)%nat).
Proof.
	intros n m a x Hm.
	apply is_canonical_struct_equiv in Hm.
	revert m a x Hm.
	assert (H2 : forall x, (x + (x + 0) = 2 * x)%nat) by reflexivity.
	{	induction n as [|bn tn HR]; intros m a x Hm;
			[|destruct bn; (destruct m as [|bm tm];
				[|destruct bm; apply is_canonical_struct_tl in Hm as Htm])];
			(split; intro H); simpl in H |- *.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	specialize (HR [] (1 :: a)).
		rewrite sub_borrow_app in H, HR.
		apply is_canonical_struct_equiv in Hm as Hnone.
		apply (sub_aux_None tn [] []), proj2, proj2 in Hnone. 
		destruct (sub_borrow tn [] []); [|discriminate].
		simpl in H, HR, Hnone.
		assert (Htn : (to_nat tn - 1)%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		rewrite <- Ha.
		destruct (to_nat tn); [discriminate Hnone; reflexivity|].
		rewrite PeanoNat.Nat.sub_succ, PeanoNat.Nat.sub_0_r in Htn.
		simpl.
		rewrite <- plus_n_Sm, Htn.
		reflexivity.
	+	specialize (HR tm (0 :: a)).
		rewrite sub_aux_app in H, HR.
		destruct (sub_aux tn tm []); [|discriminate].
		simpl in H, HR.
		assert (Htn : (to_nat tn - to_nat tm)%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		rewrite <- Ha, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
		reflexivity.
	+	specialize (HR tm (1 :: a)).
		rewrite sub_borrow_app in H, HR.
		apply is_canonical_struct_equiv in Htm as Hnone.
		apply (sub_aux_None tn tm []), proj2, proj2 in Hnone. 
		destruct (sub_borrow tn tm []); [|discriminate].
		simpl in H, HR.
		assert (Htn : (to_nat tn - S(to_nat tm))%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		{	rewrite <- PeanoNat.Nat.sub_succ, PeanoNat.Nat.sub_succ_l.
		+	rewrite <- Ha, plus_n_Sm, <- !plus_Sn_m, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
			reflexivity.
		+	rewrite plus_n_Sm, <- !plus_Sn_m, !H2.
			apply PeanoNat.Nat.mul_le_mono_l.
			destruct (PeanoNat.Nat.le_gt_cases (S (to_nat tm)) (to_nat tn)) as [|Hl]; [assumption|].
			apply PeanoNat.Nat.sub_0_le in Hl.
			rewrite PeanoNat.Nat.sub_succ in Hl.
			apply Hnone in Hl.
			discriminate.
		}
	+	specialize (HR tm (1 :: a)).
		rewrite sub_borrow_app in H, HR.
		apply is_canonical_struct_equiv in Htm as Hnone.
		apply (sub_aux_None tn tm []), proj2, proj2 in Hnone. 
		destruct (sub_borrow tn tm []); [|discriminate].
		simpl in H, HR.
		assert (Htn : (to_nat tn - S(to_nat tm))%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		{	rewrite <- PeanoNat.Nat.sub_succ, PeanoNat.Nat.sub_succ_l.
		+	rewrite <- Ha, plus_n_Sm, <- !plus_Sn_m, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
			reflexivity.
		+	rewrite plus_n_Sm, <- !plus_Sn_m, !H2.
			apply PeanoNat.Nat.mul_le_mono_l.
			destruct (PeanoNat.Nat.le_gt_cases (S (to_nat tm)) (to_nat tn)) as [|Hl]; [assumption|].
			apply PeanoNat.Nat.sub_0_le in Hl.
			rewrite PeanoNat.Nat.sub_succ in Hl.
			apply Hnone in Hl.
			discriminate.
		}
	+	specialize (HR tm (0 :: a)).
		rewrite sub_borrow_app in H, HR.
		destruct (sub_borrow tn tm []); [|discriminate].
		simpl in H, HR.
		assert (Htn : (to_nat tn - S(to_nat tm))%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		rewrite <- Ha, plus_n_Sm, <- !plus_Sn_m, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
		reflexivity.
	+	discriminate.
	+	inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		rewrite <- Ha, H2, PeanoNat.Nat.sub_0_r.
		reflexivity.
	+	specialize (HR tm (1 :: a)).
		apply is_canonical_struct_equiv in Htm as Hnone.
		apply (sub_aux_None tn tm []), proj1, proj2 in Hnone; [|destruct tm; discriminate]. 
		apply is_canonical_struct_equiv in Htm as Hxm.
		destruct Hxm as [|xm Hxm]; [discriminate|].
		rewrite inc_S, plus_Sn_m.
		rewrite sub_aux_app in H, HR.
		destruct (sub_aux tn (inc xm) []); [|discriminate].
		simpl in H, HR.
		assert (Htn : (to_nat tn - to_nat (inc xm))%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		rewrite inc_S in Htn, Hnone.
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		{	rewrite <- PeanoNat.Nat.sub_succ, PeanoNat.Nat.sub_succ_l.
		+	rewrite <- Ha, <- plus_Sn_m, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
			reflexivity.
		+	rewrite <- plus_Sn_m, !H2.
			apply PeanoNat.Nat.mul_le_mono_l.
			destruct (PeanoNat.Nat.le_gt_cases (S (to_nat xm)) (to_nat tn)) as [|Hl]; [assumption|].
			apply PeanoNat.Nat.sub_0_le in Hl.
			apply Hnone in Hl.
			discriminate.
		}
	+	specialize (HR tm (0 :: a)).
		rewrite sub_aux_app in H, HR.
		destruct (sub_aux tn tm []); [|discriminate].
		assert (Htn : (to_nat tn - to_nat tm)%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha. 
		rewrite <- Ha, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
		reflexivity.
	+	{	destruct tm as [|bm tm].
		+	inversion H as [Ha].
			rewrite !rev_append_rev in Ha.
			apply app_inv_head in Ha.
			rewrite <- Ha, PeanoNat.Nat.sub_0_r.
			reflexivity.
		+	specialize (HR (bm :: tm) (0 :: a)).
			rewrite sub_aux_app in H, HR.
			destruct (sub_aux tn (bm :: tm) []); [|discriminate].
			assert (Htn : (to_nat tn - to_nat (bm :: tm))%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
			inversion H as [Ha].
			rewrite !rev_append_rev in Ha.
			apply app_inv_head in Ha.
			rewrite <- Ha, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
			reflexivity.
		}
	+	specialize (HR tm (1 :: a)).
		rewrite sub_borrow_app in H, HR.
		apply is_canonical_struct_equiv in Htm as Hnone.
		apply (sub_aux_None tn tm []), proj2, proj2 in Hnone. 
		destruct (sub_borrow tn tm []); [|discriminate].
		assert (Htn : (to_nat tn - S(to_nat tm))%nat = to_nat l) by (apply HR; [assumption|reflexivity]).
		inversion H as [Ha].
		rewrite !rev_append_rev in Ha.
		apply app_inv_head in Ha.
		{	rewrite <- PeanoNat.Nat.sub_succ, PeanoNat.Nat.sub_succ_l.
		+	rewrite <- Ha, plus_n_Sm, <- !plus_Sn_m, !H2, <- PeanoNat.Nat.mul_sub_distr_l, Htn.
			reflexivity.
		+	rewrite plus_n_Sm, <- !plus_Sn_m, !H2.
			apply PeanoNat.Nat.mul_le_mono_l.
			destruct (PeanoNat.Nat.le_gt_cases (S (to_nat tm)) (to_nat tn)) as [|Hl]; [assumption|].
			apply PeanoNat.Nat.sub_0_le in Hl.
			rewrite PeanoNat.Nat.sub_succ in Hl.
			apply Hnone in Hl.
			discriminate.
		}
	}
Qed.


Theorem sub_minus : forall n m, to_nat (n - m) = (to_nat n - to_nat m)%nat.
Proof.
	intros n m.
	unfold sub.
	pose proof (Htrim := trim_canonical m).
	pose proof (Hnone := proj2 (sub_aux_None n (trim m) [] Htrim)).
	pose proof (Hsome := sub_aux_Some n (trim m) []).
	rewrite trim_nat in Hnone.
	{	destruct (sub_borrow n (trim m) []).
	+	rewrite trim_nat, inc_S.
		rewrite PeanoNat.Nat.sub_succ_r, trim_nat in Hsome.
		destruct (to_nat n - to_nat m)%nat; [discriminate (proj2 Hnone); reflexivity|].
		apply (Hsome l), proj2 in Htrim.
		rewrite PeanoNat.Nat.pred_succ in Htrim.
		rewrite Htrim; reflexivity.
	+	rewrite (proj1 Hnone); reflexivity.
	}
Qed.

Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.

End Notations.
