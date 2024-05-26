Require Import Lists.List FunInd.
Require Import Init.Nat.
Require Import utils.Utils.
Import ListNotations.

Declare Scope bin_nat_scope.
Open Scope nat_scope.
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

Reserved Notation "n >? m" (at level 70).

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

Lemma to_nat_app : forall n m, to_nat (n ++ m) = (to_nat n + to_nat m * 2 ^ length n).
Proof.
	intros n m.
	{	induction n as [|bn tn HR]; [|destruct bn]; simpl.
	+	rewrite PeanoNat.Nat.mul_1_r.
		reflexivity.
	+	rewrite HR, <- !plus_n_O, PeanoNat.Nat.mul_add_distr_l.
		rewrite PeanoNat.Nat.add_shuffle0, !PeanoNat.Nat.add_assoc.
		reflexivity.
	+	f_equal.
		rewrite HR, <- !plus_n_O, PeanoNat.Nat.mul_add_distr_l.
		rewrite PeanoNat.Nat.add_shuffle0, !PeanoNat.Nat.add_assoc.
		reflexivity.
	}
Qed.

Definition not b :=
	match b with
	| 0 => 1
	| 1 => 0
	end.

Definition complement := map not.
Lemma complement_length : forall n,
		length (complement n) = length n.
Proof.
	intros n.
	apply map_length.
Qed.
Lemma complement_inj : forall n m,
		complement n = complement m -> n = m.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m H; destruct m as [|bm tm];
			[|discriminate..|]; simpl in *.
	+	reflexivity.
	+	inversion H.
		destruct bn, bm; [|discriminate..|]; f_equal; apply HR; assumption.		
	}
Qed.

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

Lemma canonical_unicity : forall n m,
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
Qed.

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

Lemma is_canonical_struct_equiv : forall (n : t),
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


Lemma is_canonical_struct_app_fix : forall l r b,
		r <> [] -> is_canonical_struct_fix b (l ++ r) = is_canonical_struct_fix false r.
Proof.
	intros l r b Hr.
	revert b.
	{	induction l as [|bl tl HR]; intros b; simpl in *.
	+	destruct r; [contradiction|reflexivity].
	+	destruct bl; apply HR.
	}
Qed.

Lemma is_canonical_struct_app : forall l r,
		r <> [] -> is_canonical_struct (l ++ r) <-> is_canonical_struct r.
Proof.
	intros l r Hr.
	{	split; unfold is_canonical_struct; intro H.
	+	rewrite is_canonical_struct_app_fix in H; [|assumption].
		apply is_canonical_struct_false in H.
		assumption.
	+	rewrite is_canonical_struct_app_fix; [|assumption].
		destruct r; [contradiction|assumption].
	}
Qed.

Lemma canonical_ones : forall n, is_canonical (repeat 1 n).
Proof.
	intros n.
	apply is_canonical_struct_equiv.
	{	induction n as [|n HR]; simpl.
	+	reflexivity.
	+	assumption.
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

Lemma trim_canonical : forall n, is_canonical (trim n).
Proof.
	intro n.
	apply is_canonical_struct_equiv.
	{	functional induction (trim n).
	+	reflexivity.
	+	reflexivity.
	+	rewrite e1 in IHl.
		apply IHl.
	+	apply IHl.
	}
Qed.
Lemma trim_canonical_id : forall n, is_canonical n -> trim n = n.
Proof.
	intros n H.
	apply is_canonical_struct_equiv in H.
	revert H.
	{	induction n as [|bn tn HR]; intro H;
			[|destruct bn; apply is_canonical_struct_tl in H as Htn];
			simpl.
	+	reflexivity.
	+	rewrite HR; [|assumption].
		destruct tn; [discriminate|].
		reflexivity.
	+	rewrite HR; [|assumption].
		reflexivity.
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

Fixpoint dt_dec dn :=
	match dn with
	| [] => (false, [])
	| b :: tdn =>
		match b, dt_dec tdn with
		| _, (true, r) => (true, b :: r)
		| 1, (false, r) => (true, 0 :: r)
		| 0, (false, r) => (false, 1 :: r)
		end
	end.

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

Notation rev_nat n := (to_nat (rev n)).

(*Variant comp :=
	| Eq : comp
	| Lt : t -> dt -> dt -> comp
	| Gt : t -> dt -> dt -> comp.*)

Record decomp := mkZip
{
	dec_tn : t;
	dec_dn : dt;
	dec_diff : dt;
}.

Record is_decomp x y decomp :=
{
	dec_length : length decomp.(dec_diff) = length decomp.(dec_dn);
	dec_zip : x = rev_append decomp.(dec_dn) (1 :: decomp.(dec_tn));
	dec_val : S (rev_nat decomp.(dec_diff) + to_nat y) = rev_nat (1 :: decomp.(dec_dn));
}.

Definition gt_decomp := option decomp.

Fixpoint gtb_decomp_aux (n : t) (m : t) (dn : dt) (an : dt) :=
	match n, m with
	| [], _ => None
	| _, [] => None (* unreachable if m canonical *)
	| 1 :: tn, [1] => Some (mkZip tn dn an)
	| 0 as bit :: tn, 0 :: tm | 1 as bit :: tn, 1 :: tm
		=> gtb_decomp_aux tn tm (bit :: dn) (0 :: an)
	| 1 as bit :: tn, 0 :: tm => gtb_decomp_aux tn tm (bit :: dn) (1 :: an)
	| 0 as bit :: tn, 1 :: tm => gtb_decomp_borrow tn tm (bit :: dn) (1 :: an)
	end
with gtb_decomp_borrow (n : t) (m : t) (dn : dt) (an : dt) :=
	match n, m with
	| [], _ => None
	| 0 as bit :: tn, [] => gtb_decomp_borrow tn [] (bit :: dn) (1 :: an)
	| 1 :: tl, [] => Some (mkZip tl dn an)
	| 0 as bit :: tn, 0 :: tm | 1 as bit :: tn, 1 :: tm
		=> gtb_decomp_borrow tn tm (bit :: dn) (1 :: an)
	| 0 as bit :: tn, 1 :: tm => gtb_decomp_borrow tn tm (bit :: dn) (0 :: an)
	| 1 as bit :: tn, 0 :: tm => gtb_decomp_aux tn tm (bit :: dn) (0 :: an)
	end.

Definition gtb_decomp n m := gtb_decomp_borrow n m [] [].

Fixpoint gtb_cont b n m :=
	match n, m with
	| [], [] => b
	| [], _ => false
	| _, [] => true
	| 0 :: tn, 0 :: tm | 1 :: tn, 1 :: tm => gtb_cont b tn tm
	| 1 :: tn, 0 :: tm => gtb_cont true tn tm
	| 0 :: tn, 1 :: tm => gtb_cont false tn tm
	end.

Definition gtb := gtb_cont false.
Notation "n >? m" := (gtb n m) : bin_nat_scope.

Lemma gtb_cont_decomp_equiv_empty : forall n dn an,
		is_canonical_struct n -> n <> [] ->
		is_some (gtb_decomp_borrow n [] dn an) = true.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn]; intros dn an Hn He; simpl.
	+	contradiction.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply is_canonical_struct_tl in Hn.
		apply HR; assumption.
	+	reflexivity.
	}
Qed.
Lemma gtb_cont_decomp_equiv : forall n m dn an,
		is_canonical_struct n ->
		is_canonical_struct m ->
		(m <> [] -> is_some (gtb_decomp_aux n m dn an) = gtb_cont true n m)
		/\ is_some (gtb_decomp_borrow n m dn an) = gtb_cont false n m.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m dn an Hn Hm;
			[|destruct bn; apply is_canonical_struct_tl in Hn as Htn];
			(destruct m as [|bm tm];
			 	[|destruct bm; apply is_canonical_struct_tl in Hm as Htm]);
			simpl; (split; [intro He|]); try reflexivity.
	+	contradiction.
	+	contradiction.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply gtb_cont_decomp_equiv_empty; assumption.
	+	assert (tm <> []) by (destruct tm; discriminate).
		apply HR; assumption.
	+	apply HR; assumption.
	+	apply HR; assumption.
	+	apply HR; assumption.
	+	contradiction.
	+	assert (tm <> []) by (destruct tm; discriminate).
		apply HR; assumption.
	+	assert (tm <> []) by (destruct tm; discriminate).
		apply HR; assumption.
	+	destruct tm; [destruct tn as [|bn tn]; [|destruct bn]; reflexivity|].
		apply HR; [assumption..|discriminate].
	+	apply HR; assumption.
	}
Qed.

Lemma gtb_decomp_equiv : forall n m,
		is_canonical_struct n ->
		is_canonical_struct m ->
		is_some (gtb_decomp n m) = (n >? m).
Proof.
	intros n m Hn Hm.
	apply gtb_cont_decomp_equiv; assumption.
Qed.

(*Lemma gtb_decomp_aux_is_decomp_empty : forall x y n dn dm an decomp,
		x = rev_append n dn -> y = rev_append [] dm ->
		is_canonical_struct m ->
		length an = length dn ->
		S (rev_nat an + rev_nat dm) = rev_nat (1 :: dn) ->
			Some decomp = gtb_decomp_borrow n m dn an ->
			is_decomp x y decomp.*)

Lemma is_decomp_app : forall x y decomp,
		is_decomp x (y ++ [0]) decomp -> is_decomp x y decomp.
Proof.
	intros x y decomp H.
	destruct H as [Hl Hz Hval].
	split; [assumption..|].
	rewrite to_nat_app in Hval.
	simpl in Hval.
	rewrite <- plus_n_O in Hval.
	assumption.
Qed.

Lemma gtb_decomp_aux_is_decomp : forall x y n m dn dm an decomp,
		x = rev_append dn n -> y = rev_append dm m ->
		is_canonical_struct m ->
		length an = length dn ->
		length dm = length dn ->
		(m <> [] ->
			Some decomp = gtb_decomp_aux n m dn an ->
			S (rev_nat an + rev_nat dm) = rev_nat dn ->
			is_decomp x y decomp)
		/\ (
			Some decomp = gtb_decomp_borrow n m dn an ->
			S (rev_nat an + rev_nat dm) = rev_nat (1 :: dn) ->
			is_decomp x y decomp).
Proof.
	intros x y n.
	revert y.
	{	induction n as [|bn tn HR]; [|destruct bn];
			intros y m dn dm an decomp Hx Hy Hm Hl1 Hl2;
			(destruct m as [|bm tm]; [|destruct bm; apply is_canonical_struct_tl in Hm as Htm]);
			(split; [intro He|]; intros H Hval); simpl in *; try discriminate;
			apply (f_equal S) in Hl1 as Hsl1; apply (f_equal S) in Hl2 as Hsl2.
		+	specialize (HR (y ++ [0]) [] (0 :: dn) (0 :: dm) (1 :: an) decomp).
			assert (y ++ [0] = rev_append (0 :: dm) [])
				by (rewrite Hy, !rev_append_rev, !app_nil_r; reflexivity).
			apply is_decomp_app.
			apply HR; [assumption..|].
			simpl.
			rewrite !to_nat_app in *.
			simpl in *.
			rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, last_length.
			simpl.
			rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, !rev_length, Hl1.
			reflexivity.
		+	specialize (HR y tm (0 :: dn) (0 :: dm) (0 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			assert (tm <> []) by (destruct tm; discriminate).
			apply (proj1 HR); [assumption..|].
			simpl.
			rewrite !to_nat_app in *.
			simpl.
			rewrite <- !plus_n_O.
			assumption.
		+	specialize (HR y tm (0 :: dn) (0 :: dm) (1 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			apply (proj2 HR); [assumption|].
			simpl.
			rewrite !to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, last_length.
			simpl.
			rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, !rev_length, Hl1.
			reflexivity.
		+	specialize (HR y tm (0 :: dn) (1 :: dm) (1 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			apply (proj2 HR); [assumption|].
			simpl.
			rewrite !to_nat_app.
			simpl; rewrite <- !plus_n_O.
			rewrite PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval, last_length, !rev_length,
				Hl1, Hl2.
			simpl; rewrite <- plus_n_O.
			reflexivity.
		+	specialize (HR y tm (0 :: dn) (1 :: dm) (0 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			apply (proj2 HR); [assumption|].
			simpl.
			rewrite !to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, last_length, !rev_length,
				Hl2.
			simpl; rewrite <- plus_n_O, PeanoNat.Nat.add_assoc.
			reflexivity.
		+	inversion_clear H.
			rewrite rev_append_rev, app_nil_r in Hy.
			rewrite <- Hy in Hval.
			split; simpl; assumption.
		+	specialize (HR y tm (1 :: dn) (0 :: dm) (1 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			assert (tm <> []) by (destruct tm; discriminate).
			apply (proj1 HR); [assumption..|].
			simpl.
			rewrite !to_nat_app.
			simpl; rewrite <- !plus_n_O.
			rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, !rev_length, Hl1.
			reflexivity.
		+	specialize (HR y tm (1 :: dn) (0 :: dm) (0 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			assert (tm <> []) by (destruct tm; discriminate).
			apply (proj1 HR); [assumption..|].
			simpl.
			rewrite !to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite Hval.
			reflexivity.
		+	{	destruct tm.
			+	inversion_clear H.
				split; [assumption..|]; simpl.
				rewrite Hy, rev_append_rev, !to_nat_app.
				simpl; rewrite <- !plus_n_O.
				rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, !rev_length, Hl2.
				reflexivity.
			+	specialize (HR y (b :: tm) (1 :: dn) (1 :: dm) (0 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
				apply (proj1 HR); [discriminate|assumption|].
				simpl.
				rewrite !to_nat_app.
				simpl; rewrite <- !plus_n_O.
				rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, !rev_length, Hl2.
				reflexivity.
			}
		+	specialize (HR y tm (1 :: dn) (1 :: dm) (1 :: an) decomp Hx Hy Htm Hsl1 Hsl2).
			apply (proj2 HR); [assumption..|].
			simpl.
			rewrite !to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval, last_length, !rev_length.
			simpl.
			rewrite <- !plus_n_O, Hl1, Hl2.
			reflexivity.
	}
Qed.

Lemma gtb_decomp_is_decomp : forall n m decomp,
		is_canonical_struct m ->
		Some decomp = gtb_decomp n m ->
		is_decomp n m decomp.
Proof.
	intros n m decomp Hm H.
	unfold gtb_decomp in *.
	apply (gtb_decomp_aux_is_decomp n m n m [] []) in H;
		(assumption || reflexivity).
Qed.


Lemma or_list_eq : forall (b : Bit) l1 l2 H, l1 = l2 \/ H -> b :: l1 = b :: l2 \/ H.
Proof.
	intros b l1 l2 H Ht.
	{	destruct Ht as [Ht|Ht].
	+	left.
		rewrite Ht.
		reflexivity.
	+	right.
		assumption.
	}
Qed.

Lemma gtb_cont_total : forall n m b,
		gtb_cont b n m = true \/ gtb_cont (negb b) m n = true.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn]; intros m b;
			(destruct m as [|bm tm]; [|destruct bm]); simpl.
	+	destruct b; [left|right]; reflexivity.
	+	right; reflexivity.
	+	right; reflexivity.
	+	left; reflexivity.
	+	apply HR.
	+	apply HR.
	+	left; reflexivity.
	+	apply HR.
	+	apply HR.
	}
Qed.

Lemma gtb_total : forall n m,
		n = m \/ n >? m = true \/ m >? n = true.
Proof.
	intro n.
	unfold gtb.
	{	induction n as [|bn tn HR]; [|destruct bn]; intro m;
			(destruct m as [|bm tm]; [|destruct bm]); simpl.
	+	left; reflexivity.
	+	right; right; reflexivity.
	+	right; right; reflexivity.
	+	right; left; reflexivity.
	+	apply or_list_eq, HR.
	+	right; apply gtb_cont_total.
	+	right; left; reflexivity.
	+	right; apply gtb_cont_total.
	+	apply or_list_eq, HR.
	}
Qed.

Lemma gtb_antireflexive : forall n, n >? n = false.
Proof.
	intros n.
	unfold gtb.
	{	induction n as [|bn tn HR].
	+	reflexivity.
	+	destruct bn; apply HR.
	}
Qed.
Lemma gtb_antisym_cont : forall n m b, gtb_cont b n m = false \/ gtb_cont (negb b) m n = false.
Proof.
	intros n.
	{	induction n as [|bn tn HR]; intros m b;
			(destruct m as [|bm tm]); simpl.
	+	destruct b; [right|left]; reflexivity.
	+	left; reflexivity.
	+	right; reflexivity.
	+	destruct bn; destruct bm; apply HR.
	}
Qed.

Lemma gtb_antisym : forall n m, n >? m = false \/ m >? n = false.
Proof.
	intro n.
	unfold gtb.
	{	induction n as [|bn tn HR]; intro m; destruct m as [|bm tm]; simpl.
	+	left; reflexivity.
	+	left; reflexivity.
	+	right; reflexivity.
	+	{	destruct bn, bm.
		+	apply HR.
		+	apply gtb_antisym_cont.
		+	apply gtb_antisym_cont.
		+	apply HR.
		}
	}
Qed.
Theorem gtb_nat : forall n m,
		is_canonical_struct n -> is_canonical_struct m ->
		n >? m = (to_nat m <? to_nat n)%nat.
Proof.
	intros n m Hn Hm.
	pose proof (Heq1 := gtb_decomp_equiv n m Hn Hm).
	pose proof (Heq2 := gtb_decomp_equiv m n Hm Hn).
	pose proof (Hdecomp1 := gtb_decomp_is_decomp n m).
	pose proof (Hdecomp2 := gtb_decomp_is_decomp m n).
	{	destruct (gtb_total n m) as [H|H]; [|destruct H as [H|H]].
	+	rewrite H, gtb_antireflexive, PeanoNat.Nat.ltb_irrefl.
		reflexivity.
	+	rewrite H in *.
		destruct (gtb_decomp n m) as [decomp|]; [|discriminate].
		apply eq_sym, PeanoNat.Nat.ltb_lt.
		destruct (Hdecomp1 decomp Hm eq_refl) as [_ Hzip Hval], decomp as [tn dn ddiff].
		simpl in *.
		replace (rev_append _ _) with (rev_append (1 :: dn) tn) in Hzip by reflexivity.
		rewrite Hzip, rev_append_rev, !to_nat_app.
		simpl.
		rewrite <- Hval, plus_Sn_m, PeanoNat.Nat.add_shuffle0, <- plus_Sn_m.
		apply PeanoNat.Nat.lt_add_pos_l, PeanoNat.Nat.lt_0_succ.
	+	destruct (gtb_antisym n m) as [Ha|Ha]; rewrite H in *; [|discriminate].
		rewrite Ha.
		destruct (gtb_decomp m n) as [decomp|]; [|discriminate].
		apply eq_sym, PeanoNat.Nat.ltb_ge.
		destruct (Hdecomp2 decomp Hn eq_refl) as [_ Hzip Hval], decomp as [tm dm ddiff].
		simpl in *.
		replace (rev_append _ _) with (rev_append (1 :: dm) tm) in Hzip by reflexivity.
		rewrite Hzip, rev_append_rev, !to_nat_app.
		simpl.
		rewrite <- Hval, plus_Sn_m, PeanoNat.Nat.add_shuffle0, <- plus_Sn_m.
		apply PeanoNat.Nat.le_add_l.
	}
Qed.

Lemma gtb_decomp_eq : forall x n m decompn decompm,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Some decompn = gtb_decomp x n ->
		Some decompm = gtb_decomp x m  ->
		n = m <-> decompn = decompm.
Proof.
	intros x n m decompn decompm Hx Hn Hm Hdn Hdm.
	{	split; intro H.
	+	rewrite H, <- Hdm in Hdn.
		inversion_clear Hdn.
		reflexivity.
	+	apply canonical_unicity; [assumption..|].
		apply is_canonical_struct_equiv in Hn, Hm.
		pose proof (Hxn := gtb_decomp_is_decomp x n decompn Hn Hdn).
		pose proof (Hxm := gtb_decomp_is_decomp x m decompm Hm Hdm).
		destruct decompn as [tn dn an], decompm as [tm dm am],
				Hxn as [_ _ Hnv], Hxm as [_ _ Hmv]; simpl in *.
		revert Hnv Hmv.
		inversion_clear H.
		intros Hnv Hmv.
		rewrite <- Hmv in Hnv.
		apply eq_add_S, PeanoNat.Nat.add_cancel_l in Hnv.
		assumption.
	}
Qed.

Lemma gtb_decomp_neq : forall x n m (H : n <> m) decompn decompm,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Some decompn = gtb_decomp x n ->
		Some decompm = gtb_decomp x m ->
		decompn.(dec_diff) <> decompm.(dec_diff).
Proof.
	intros x n m H decompn decompm Hx Hn Hm Hcn Hcm Ha.
	assert (Hc : gtb_decomp x n <> gtb_decomp x m)
		by (intro Hc; rewrite <- Hcn, <- Hcm in Hc; inversion Hc as [Hc1];
			apply (gtb_decomp_eq x n m) in Hc1; [contradiction|assumption..]).
	rewrite <- Hcn, <- Hcm in Hc.
	apply is_canonical_struct_equiv in Hn, Hm.
	pose proof (Hdn := gtb_decomp_is_decomp x n decompn Hn Hcn).
	pose proof (Hdm := gtb_decomp_is_decomp x m decompm Hm Hcm).
	destruct decompn as [tn dn an], decompm as [tm dm am],
		Hdn as [Hln Hzn Hvn], Hdm as [Hlm Hzm Hvm]; simpl in *.
	{	destruct (PeanoNat.Nat.eq_dec (length an) (length am)) as [Hl|Hl].
	+	rewrite Hlm, Hln, <- (rev_length dn), <- (rev_length dm) in Hl.
		rewrite Hzm in Hzn.
		apply (f_equal (firstn (length (rev dm)))) in Hzn as Hfz.
		rewrite (plus_n_O (length (rev dm))), !rev_append_rev, firstn_app_2,
			<- Hl, firstn_app_2, !app_nil_r in Hfz.
		apply rev_inj in Hfz.
		apply (f_equal (skipn (length (rev dm)))) in Hzn as Hsz.
		rewrite !rev_append_rev, !skipn_app, skipn_all, <- Hl, skipn_all,
			PeanoNat.Nat.sub_diag in Hsz.
		inversion Hsz as [Hs].
		rewrite Hfz, Hs, Ha in Hc.
		contradiction.
	+	rewrite Ha in Hl.
		contradiction.
	}
Qed.

(*Definition comp_op comp :=
	match comp with
	| Eq => Eq
	| Lt rtn rdn ran => Gt rtn rdn ran
	| Gt rtn rdn ran => Lt rtn rdn ran
	end.

Lemma comp_op_inv : forall comp, comp_op (comp_op comp) = comp.
Proof.
	intro comp.
	destruct comp; reflexivity.
Qed.
Lemma comp_op_inj : forall c1 c2, comp_op c1 = comp_op c2 -> c1 = c2.
Proof.
	intros c1 c2 H.
	destruct c1, c2; discriminate || (inversion H; reflexivity).
Qed.


Definition uc_Gt := uncurry (uncurry Gt).
Definition uc_Lt := uncurry (uncurry Lt).

Lemma uc_Lt_inj : forall a b, uc_Lt a = uc_Lt b -> a = b.
Proof.
	intros a b H.
	destruct a as [a1 a3], a1, b as [b1 b3], b1.
	inversion_clear H.
	reflexivity.
Qed.

Fixpoint compare_empty (n : t) (dn an : dt) :=
	match n with
	| [] => ([], [], [])
	| 1 :: tn => (tn, dn, an)
	| 0 :: tn => compare_empty tn (0 :: dn) (1 :: an)
	end.


Fixpoint compare_borrow_n (n m : t) (dn dm an am : dt) :=
	match n, m with
	| [], _ => None
	| _, [] => Some (uc_Gt (compare_empty n dn an))
	| [1], 1 :: tm => Some (Lt tm dm am)
	| 1 as bn :: tn, 1 as bm :: tm | 0 as bn :: tn, 0 as bm :: tm
		=> compare_borrow_n tn tm (bn :: dn) (bm :: dm) (1 :: an) (0 :: am) 
	| 0 :: tn, 1 :: tm => compare_borrow_n tn tm (0 :: dn) (1 :: dm) (0 :: an) (1 :: am)
	| 1 :: tn, 0 :: tm => compare_borrow_m tn tm (1 :: dn) (0 :: dm) (0 :: an) (1 :: am)
	end
with compare_borrow_m (n m : t) (dn dm an am : dt) :=
	match n, m with
	| _, [] => None
	| [], _ => Some (uc_Lt (compare_empty m dm am))
	| 1 :: tn, [1] => Some (Gt tn dn an)
	| 1 as bn :: tn, 1 as bm :: tm | 0 as bn :: tn, 0 as bm :: tm
		=> compare_borrow_m tn tm (bn :: dn) (bm :: dm) (0 :: an) (1 :: am)
	| 0 :: tn, 1 :: tm => compare_borrow_n tn tm (0 :: dn) (1 :: dm) (1 :: an) (0 :: am)
	| 1 :: tn, 0 :: tm => compare_borrow_m tn tm (1 :: dn) (0 :: dm) (1 :: an) (0 :: am)
	end.

Fixpoint compare_aux (n m : t) (dn dm an am : dt) :=
	match n, m with
	| [], [] => Some (Eq)
	| [], _ => Some (uc_Lt (compare_empty m dm am))
	| _, [] => Some (uc_Gt (compare_empty n dn an))
	| 0 as bn :: tn, 0 as bm :: tm | 1 as bn :: tn, 1 as bm :: tm
		=> compare_aux tn tm (bn :: dn) (bm :: dm) (1 :: an) (1 :: am)
	| 1 :: tn, 0 :: tm => compare_borrow_m tn tm (1 :: dn) (0 :: dm) (0 :: an) (0 :: am)
	| 0 :: tn, 1 :: tm => compare_borrow_n tn tm (0 :: dn) (1 :: dm) (0 :: an) (0 :: am)
	end.

Definition compare n m :=
	option_default Eq (compare_aux n m [] [] [] []).

Lemma compare_borrow_none : forall n m dn dm an am,
		is_canonical_struct n -> is_canonical_struct m ->
		(n <> [] -> compare_borrow_n n m dn dm an am <> None)
		/\ (m <> [] -> compare_borrow_m n m dn dm an am <> None).
Proof.
	intros n.
	{	induction n as [|bn tn HR]; intros m dn dm an am Hn Hm;
			[| destruct bn; apply is_canonical_struct_tl in Hn as Htn];
			(destruct m as [|bm tm]; [|destruct bm;
				apply is_canonical_struct_tl in Hm as Htm]);
	  		split; intro H; simpl; try contradiction.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply HR; assumption.
	+	assert (tm <> []) by (destruct tm; discriminate).
		apply HR; assumption.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply HR; assumption.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply HR; assumption.
	+	destruct tn; discriminate.
	+	assert (tm <> []) by (destruct tm; discriminate).
		destruct tn; apply HR; assumption.
	+	assert (tm <> []) by (destruct tm; discriminate).
		apply HR; assumption.
	+	destruct tn; [discriminate|].
		apply HR; [assumption..|discriminate].
	+	destruct tm; [discriminate|].
		apply HR; [assumption..|discriminate].
	}
Qed.
Lemma compare_aux_none : forall n m dn dm an am,
		is_canonical n -> is_canonical m ->
		compare_aux n m dn dm an am <> None.
Proof.
	intros n m dn dm an am Hn Hm.
	apply is_canonical_struct_equiv in Hn, Hm.
	revert m dn dm an am Hn Hm.
	{	induction n as [|bn tn HR]; intros m dn dm an am Hn Hm;
			[| destruct bn; apply is_canonical_struct_tl in Hn as Htn];
			(destruct m as [|bm tm]; [|destruct bm;
				apply is_canonical_struct_tl in Hm as Htm]);
	  		simpl.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	apply HR; assumption.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply compare_borrow_none; assumption.
	+	discriminate.
	+	assert (tm <> []) by (destruct tm; discriminate).
		apply compare_borrow_none; assumption.
	+	apply HR; assumption.
	}
Qed.

Lemma compare_some : forall n m comp,
		is_canonical n -> is_canonical m ->
		comp = compare n m ->
		Some comp = compare_aux n m [] [] [] [].
Proof.
	unfold compare.
	intros n m comp Hn Hm H.
	pose proof (HNone := compare_aux_none _ _ [] [] [] [] Hn Hm).
	destruct compare_aux; [|contradiction].
	simpl in *.
	rewrite H.
	reflexivity.
Qed.
Lemma compare_empty_decomp : forall x y n dn an rtn rdn ran,
		(rtn, rdn, ran) = compare_empty n dn an ->
		is_canonical_struct n -> n <> [] ->
		length an = length dn ->
		x = rev_append dn n ->
		S (rev_nat an + to_nat y) = rev_nat (1 :: dn) ->
		decomp x y rtn rdn ran.
Proof.
	intros x y n.
	{	induction n as [|bn tn HR]; intros dn an rtn rdn ran He Hn Hz Hl Happ Hval;
			[|destruct bn]; simpl in *.
	+	contradiction.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply is_canonical_struct_tl in Hn.
		assert (length (1 :: an) = length (0 :: dn)) by (simpl; rewrite Hl; reflexivity).
		assert (S (rev_nat (1 :: an) + to_nat y) = rev_nat (1 :: 0 :: dn)).
		{
			simpl.
			rewrite !to_nat_app, rev_length in Hval.
			rewrite !to_nat_app, app_length, !rev_length.
			rewrite Hl, (PeanoNat.Nat.add_comm _ 1).
			simpl in *.
			rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.add_assoc, <- plus_Sn_m,
			  (PeanoNat.Nat.add_comm (to_nat y)), Hval, PeanoNat.Nat.add_assoc.
			reflexivity.
		}
		apply HR in He; assumption.
	+	inversion_clear He.
		split; assumption.
	}
Qed.



Lemma compare_borrow_decomp_Lt : forall x y n m dn dm an am rtn rdn ran,
		x = rev_append dn n -> y = rev_append dm m ->
		is_canonical_struct n ->
		is_canonical_struct m ->
		length am = length dm ->
		length am = length dn ->
		(n <> [] ->
		Some (Lt rtn rdn ran) = compare_borrow_n n m dn dm an am ->
		S (rev_nat am + rev_nat dn) = rev_nat dm ->
		decomp y x rtn rdn ran)
		/\ (Some (Lt rtn rdn ran) = compare_borrow_m n m dn dm an am ->
		S (rev_nat am + rev_nat dn) = rev_nat (1 :: dm) ->
		decomp y x rtn rdn ran).
Proof.
	intros x y n.
	{	induction n as [|bn tn HR]; intros m dn dm an am rtn rdn ran Hx Hy Hn Hm Hl1 Hl2;
			[| destruct bn; apply is_canonical_struct_tl in Hn as Htn;
		 		(destruct m as [|bm tm]; [|destruct bm;
				apply is_canonical_struct_tl in Hm as Htm])];
			pose proof (Hsl1 := (f_equal S) _ _ Hl1);
			pose proof (Hsl2 := (f_equal S) _ _ Hl2);
			(split; [intros He H Hval|intros H Hval]); simpl in *.
	+	discriminate.
	+  	destruct m; [discriminate|].
		assert (b :: m <> []) by discriminate.
		rewrite rev_append_rev, app_nil_r in Hx.
		rewrite <- Hx in Hval.
		assert (He : (rtn, rdn, ran) = compare_empty (b :: m) dm am)
			by (destruct compare_empty as [r1 r3], r1; inversion H; reflexivity).
		apply (compare_empty_decomp y x) in He; assumption.
	+	destruct compare_empty as [r1 r3], r1.
		discriminate.
	+	discriminate.
	+	apply HR in H; [assumption..| destruct tn; discriminate |].
		simpl.
		rewrite !to_nat_app, <- !plus_n_O.
		assumption.
	+ 	apply HR in H; [assumption..|].
		simpl.
		rewrite !to_nat_app, <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, last_length.
		simpl.
		rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, !rev_length, Hl1.
		reflexivity.
	+	apply HR in H; [assumption..| destruct tn; discriminate|].
		simpl.
		rewrite !to_nat_app, <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, !rev_length, Hl1.
		reflexivity.
	+	apply HR in H; [assumption..| destruct tn; discriminate|].
		simpl.
		rewrite !to_nat_app, <- !plus_n_O in *.
		rewrite Hval.
		reflexivity.
	+	destruct tn; discriminate.
	+	discriminate.
	+	enough (S (rev_nat (1 :: am) + rev_nat (1 :: dn)) = rev_nat (1 :: 0 :: dm))
			by (destruct tn; apply HR in H; assumption).
		simpl.
		rewrite !to_nat_app, last_length.
		simpl.
		rewrite <- !plus_n_O, PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval.
		rewrite !rev_length, <- Hl2, Hl1.
		reflexivity.
	+	apply HR in H; [assumption..|].
		simpl.
		rewrite !to_nat_app, <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, last_length.
		simpl.
		rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, !rev_length.
		rewrite <- Hl1, Hl2.
		reflexivity.
	+	{	destruct tn.
		+	inversion_clear H.
			enough (S (rev_nat am + to_nat x) = rev_nat (1 :: dm))
				by (split; assumption).
			simpl.
			rewrite Hx, rev_append_rev, !to_nat_app, !rev_length.
			simpl.
			rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, <- Hl2, Hl1.
			reflexivity.
		+	apply HR in H; [assumption..|discriminate|].
			simpl.
			rewrite !to_nat_app, !rev_length.
			simpl.
			rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, <- Hl2, Hl1.
			reflexivity.
		}
	+	destruct tm; [discriminate|].
		apply HR in H; [assumption..| ].
		simpl.
		rewrite !to_nat_app, last_length, !rev_length in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite <- PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval, <- Hl2, <- Hl1.
		reflexivity.
	}
Qed.

Lemma compare_aux_decomp_Lt : forall x y n m dn dm an am rtn rdn ran,
		x = rev_append dn n -> y = rev_append dm m ->
		is_canonical_struct n ->
		is_canonical_struct m ->
		length am = length dm ->
		length am = length dn ->
		Some (Lt rtn rdn ran) = compare_aux n m dn dm an am ->
		S (rev_nat am + rev_nat dn) = rev_nat (1 :: dm) ->
		decomp y x rtn rdn ran.
Proof.
	intros x y n.
	{	induction n as [|bn tn HR]; intros m dn dm an am rtn rdn ran Hx Hy Hn Hm Hl1 Hl2;
			[| destruct bn; apply is_canonical_struct_tl in Hn as Htn];
		 	(destruct m as [|bm tm]; [|destruct bm;
				apply is_canonical_struct_tl in Hm as Htm]);
			pose proof (Hsl1 := (f_equal S) _ _ Hl1);
			pose proof (Hsl2 := (f_equal S) _ _ Hl2);
			intros H Hval; simpl in *.
	+	discriminate.
	+	assert (tm <> []) by (destruct tm; discriminate).
		assert (He : (rtn, rdn, ran) = compare_empty tm (0 :: dm) (1 :: am))
		  by (destruct compare_empty as [r1 r3], r1; inversion H; reflexivity).
		apply (compare_empty_decomp y x) in He; [assumption..|].
		simpl.
		rewrite !to_nat_app, last_length, !rev_length in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite Hx, rev_append_rev, app_nil_r, PeanoNat.Nat.add_shuffle0, <- plus_Sn_m,
			Hval, Hl1, PeanoNat.Nat.add_assoc.
		reflexivity.
	+	rewrite rev_append_rev, app_nil_r in Hx.
		rewrite <- Hx in Hval.
		inversion_clear H.
		split; assumption.
	+	destruct (compare_empty) as [r1 r3], r1; discriminate.
	+	apply HR in H; [assumption..|].
		simpl.
		rewrite !to_nat_app, last_length, !rev_length in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, Hl1,  PeanoNat.Nat.add_assoc.
		reflexivity.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply (compare_borrow_decomp_Lt x y) in H; [assumption..|].
		simpl.
		rewrite !to_nat_app, !rev_length in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		assumption.
	+	discriminate.
	+	apply (compare_borrow_decomp_Lt x y) in H; [assumption..|].
		simpl.
		rewrite !to_nat_app, last_length, !rev_length in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite !PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, <- Hl2, Hl1.
		reflexivity.
	+	apply HR in H; [assumption..|].
		simpl.
		rewrite !to_nat_app, last_length, !rev_length in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval, <- Hl2, Hl1.
		reflexivity.
	}
Qed.


Lemma compare_decomp_Lt : forall x y rtn rdn ran,
		is_canonical x -> is_canonical y  ->
		Lt rtn rdn ran = compare x y ->
		decomp y x rtn rdn ran.
Proof.
	intros x y rtn rdn ran Hx Hy H.
	apply compare_some in H; [|assumption..].
	apply is_canonical_struct_equiv in Hx, Hy.
	{	apply (compare_aux_decomp_Lt x y) in H.
	+	assumption.
	+	reflexivity.
	+	reflexivity.
	+	assumption.
	+	assumption.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	}
Qed.


Lemma compare_borrow_sym : forall n m dn dm an am,
		compare_borrow_n n m dn dm an am =
			option_map comp_op (compare_borrow_m m n dm dn am an)
		/\ compare_borrow_m n m dn dm an am
			= option_map comp_op (compare_borrow_n m n dm dn am an).
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m dn dm an am; [|destruct bn];
		(destruct m as [|bm tm]; [|destruct bm]); split; simpl; try reflexivity.
	+	destruct compare_empty as [r1 r3], r1 as [r1 r2].
		reflexivity.
	+	destruct tm; reflexivity.
	+	destruct compare_empty as [r1 r3], r1 as [r1 r2].
		reflexivity.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	destruct tm; apply HR.
	+	destruct tn; reflexivity.
	+	destruct tn; apply HR.
	+	apply HR.
	+	destruct tn; [reflexivity|apply HR].
	+	destruct tm; [reflexivity|apply HR].
	}
Qed.
	
Lemma compare_aux_sym : forall n m dn dm an am,
		compare_aux n m dn dm an am = option_map comp_op (compare_aux m n dm dn am an).
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m dn dm an am; [|destruct bn];
			(destruct m as [|bm tm]; [|destruct bm]); simpl.
	+	reflexivity.
	+	destruct compare_empty as [r1 r3], r1 as [r1 r2].
		reflexivity.
	+	reflexivity.
	+	destruct compare_empty as [r1 r3], r1 as [r1 r2].
		reflexivity.
	+	apply HR.
	+	apply compare_borrow_sym.
	+	reflexivity.
	+	apply compare_borrow_sym.
	+	apply HR.
	}
Qed.
Lemma compare_sym : forall n m, compare n m = comp_op (compare m n).
Proof.
	intros n m.
	unfold compare.
	rewrite compare_aux_sym.
	destruct compare_aux; reflexivity.
Qed.

Lemma compare_decomp_Gt : forall x y rtn rdn ran,
		is_canonical x -> is_canonical y ->
		Gt rtn rdn ran = compare x y ->
		decomp x y rtn rdn ran.
Proof.
	intros x y rtn rdn ran Hx Hy H.
	apply (f_equal comp_op) in H.
	rewrite <- compare_sym in H.
	apply compare_decomp_Lt in H; assumption.
Qed.

Lemma compare_borrow_Eq : forall n m dn dm an am,
		Some Eq <> compare_borrow_n n m dn dm an am
		/\ Some Eq <> compare_borrow_m n m dn dm an am.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn];
			(destruct m as [|bm tm]; [|destruct bm]); split; simpl;
			try discriminate.
	+	destruct compare_empty as [r1 r3], r1.
		discriminate.
	+	destruct compare_empty as [r1 r3], r1.
		discriminate.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	destruct tn; discriminate.
	+	destruct tn; apply HR.
	+	apply HR.
	+	destruct tn; [discriminate| apply HR].
	+	destruct tm; [discriminate| apply HR].
	}
Qed.
Lemma compare_aux_decomp_Eq : forall n m dn dm an am,
		Some Eq = compare_aux n m dn dm an am <-> n = m.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn];
			(destruct m as [|bm tm]; [|destruct bm]);
			split; intro H; simpl in *.
	+	reflexivity.
	+	reflexivity.
	+	destruct compare_empty as [r1 r3], r1.
		discriminate.
	+	destruct compare_empty as [r1 r3], r1.
		discriminate.
	+	discriminate.
	+	discriminate.
	+	destruct compare_empty as [r1 r3], r1.
		discriminate.
	+	discriminate.
	+	apply HR in H.
		rewrite H.
		reflexivity.
	+	apply HR.
		inversion_clear H.
		reflexivity.
	+	apply compare_borrow_Eq in H.
		contradiction.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	apply compare_borrow_Eq in H.
		contradiction.
	+	discriminate.
	+	apply HR in H.
		rewrite H.
		reflexivity.
	+	apply HR.
		inversion_clear H.
		reflexivity.
	}
Qed.

Lemma compare_decomp_Eq : forall n m,
		is_canonical n -> is_canonical m ->
		Eq = compare n m <-> n = m.
Proof.
	intros n m Hn Hm.
	{	split; intro H.
	+	apply compare_some in H; [|assumption..].
		apply compare_aux_decomp_Eq in H.
		assumption.
	+	apply (compare_aux_decomp_Eq n m [] [] [] []) in H.
		unfold compare.
		rewrite <- H.
		reflexivity.
	}
Qed.

Definition ltb n m :=
	match compare n m with
	| Lt _ _ _  => true
	| _ => false
	end.

Notation "n <? m" := (ltb n m).

Theorem ltb_nat : forall n m,
		is_canonical n -> is_canonical m ->
		n <? m = (to_nat n <? to_nat m)%nat.
Proof.
	intros n m Hn Hm.
	symmetry.
	pose proof (Heq := compare_decomp_Eq n m Hn Hm).
	pose proof (Hlt := compare_decomp_Lt n m).
	pose proof (Hgt := compare_decomp_Gt n m).
	unfold ltb.
	{	destruct compare as [|rtn rdn ran| rtn rdn ran].
	+	rewrite (proj1 Heq); [|reflexivity].
		rewrite PeanoNat.Nat.ltb_irrefl.
		reflexivity.
	+	destruct (Hlt rtn rdn ran) as [Hl Hz Hv]; [assumption..|reflexivity|].
		apply PeanoNat.Nat.ltb_lt.
		apply (f_equal to_nat) in Hz.
		rewrite rev_append_rev in Hz.
		simpl in *.
		rewrite !to_nat_app in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_assoc, <- Hv in Hz.
		rewrite Hz, <- plus_Sn_m, PeanoNat.Nat.add_shuffle0.
		apply PeanoNat.Nat.lt_add_pos_l.
		rewrite !plus_Sn_m.
		apply PeanoNat.Nat.lt_0_succ.
	+	destruct (Hgt rtn rdn ran) as [Hl Hz Hv]; [assumption..|reflexivity|].
		apply PeanoNat.Nat.ltb_ge.
		apply (f_equal to_nat) in Hz.
		rewrite rev_append_rev in Hz.
		simpl in *.
		rewrite !to_nat_app in *.
		simpl in *.
		rewrite <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_assoc, <- Hv in Hz.
		rewrite Hz, <- plus_Sn_m, PeanoNat.Nat.add_shuffle0.
		apply PeanoNat.Nat.le_add_l.
	}
Qed.

Lemma ltb_rev : forall n m, n <? m = true <-> exists tn dn an, compare m n = Gt tn dn an.
Proof.
	intros n m.
	unfold ltb.
	{	split; intro H.
	+	destruct compare as [|tn dn an|] eqn:He; try discriminate.
		exists tn, dn, an.
		apply comp_op_inj.
		rewrite <- compare_sym.
		assumption.
	+	destruct H as [tn H], H as [dn H], H as [an H].
		apply (f_equal comp_op) in H.
		rewrite <- compare_sym in H.
		rewrite H.
		reflexivity.
	}
Qed.

Definition sub n m :=
	match compare n m with
	| Gt rtn rdn ran => trim (inc (rev_append ran (0 :: rtn))) 
	| _ => []
	end.

Notation "n - m" := (sub n m) : bin_nat_scope.

Theorem sub_minus : forall n m,
		is_canonical n -> is_canonical m ->
		to_nat (n - m) = (to_nat n - to_nat m)%nat.
Proof.
	intros n m Hn Hm.
	unfold sub.
	pose proof (Heq := compare_decomp_Eq n m Hn Hm).
	pose proof (Hlt := ltb_nat n m Hn Hm).
	pose proof (Hgt := compare_decomp_Gt n m).
	unfold ltb in Hlt.
	{	destruct compare as [|rtn rdn ran|rtn rdn ran].
	+	rewrite (proj1 Heq); [|reflexivity].
		rewrite PeanoNat.Nat.sub_diag.
		reflexivity.
	+	apply eq_sym, PeanoNat.Nat.ltb_lt, PeanoNat.Nat.lt_le_incl in Hlt.
		symmetry.
		rewrite PeanoNat.Nat.sub_0_le.
		assumption.
	+	destruct (Hgt rtn rdn ran) as [Hl Hz Hv]; [assumption..|reflexivity|].
		rewrite Hz, trim_nat, inc_S, !rev_append_rev, !to_nat_app.
		simpl in *.
		rewrite !to_nat_app in Hv.
		simpl in Hv.
		rewrite <- !plus_n_O in *.
		rewrite PeanoNat.Nat.add_assoc, <- Hv, <- !plus_Sn_m, PeanoNat.Nat.add_shuffle0,
			PeanoNat.Nat.add_sub.
		rewrite !rev_length, Hl.
		reflexivity.
	}
Qed.


Theorem compare_eq : forall x n m,
		is_canonical x -> is_canonical n -> is_canonical m ->
		n = m <-> compare x n = compare x m.
Proof.
	intros x n m Hx Hn Hm.
	{	split; intro H.
	+	unfold compare.
		rewrite H.
		reflexivity.
	+	pose proof (Heqn := proj1 (compare_decomp_Eq x n Hx Hn)).
		pose proof (Heqm := proj1 (compare_decomp_Eq x m Hx Hm)).
		pose proof (Hltn := compare_decomp_Lt x n).
		pose proof (Hltm := compare_decomp_Lt x m).
		pose proof (Hgtn := compare_decomp_Gt x n).
		pose proof (Hgtm := compare_decomp_Gt x m).
		{	destruct (compare x n) as [|tn dn an | tn dn an],
				(compare x m) as [|tm dm am | tm dm am]; try discriminate.
		+	rewrite <- Heqn, Heqm; reflexivity.
		+	destruct (Hltn tn dn an) as [Hnl Hnz Hnv]; [assumption..|reflexivity|].
			destruct (Hltm tm dm am) as [Hml Hmz Hmv]; [assumption..|reflexivity|].
			apply canonical_unicity; [assumption..|].
			rewrite Hnz, Hmz.
			inversion_clear H.
			reflexivity.
		+	destruct (Hgtn tn dn an) as [Hnl Hnz Hnv]; [assumption..|reflexivity|].
			destruct (Hgtm tm dm am) as [Hml Hmz Hmv]; [assumption..|reflexivity|].
			apply canonical_unicity; [assumption..|].
			rewrite <- plus_Sn_m in Hnv, Hmv.
			apply (f_equal (fun x => x - S (rev_nat an))%nat) in Hnv.
			apply (f_equal (fun x => x - S (rev_nat am))%nat) in Hmv.
			rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub in Hnv.
			rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub in Hmv.
			rewrite Hnv, Hmv.
			inversion_clear H.
			reflexivity.
		}
	}
Qed.
Lemma compare_neq_gt : forall x n m (H : n <> m) tn dn an tm dm am,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Gt tn dn an = compare x n ->
		Gt tm dm am = compare x m ->
		an <> am.
Proof.
	intros x n m H tn dn an tm dm am Hx Hn Hm Hcn Hcm Ha.
	assert (Hc : compare x n <> compare x m)
		by (intro Hc; apply compare_eq in Hc; [contradiction|assumption..]).
	rewrite <- Hcn, <- Hcm in Hc.
	apply compare_decomp_Gt in Hcn, Hcm; [|assumption..].
	destruct Hcn as [Hnl Hnz _], Hcm as [Hml Hmz _].
	rewrite Hmz, !rev_append_rev in Hnz.
	{	destruct (PeanoNat.Nat.eq_dec (length an) (length am)) as [Hl|Hl].
	+	rewrite Hml, Hnl, <- (rev_length dn), <- (rev_length dm) in Hl.
		apply (f_equal (firstn (length (rev dm)))) in Hnz as Hfz.
		rewrite (plus_n_O (length (rev dm))), firstn_app_2,
			<- Hl, firstn_app_2, !app_nil_r in Hfz.
		apply (f_equal (skipn (length (rev dm)))) in Hnz as Hsz.
		rewrite !skipn_app, skipn_all, PeanoNat.Nat.sub_diag,
			<- Hl, skipn_all, PeanoNat.Nat.sub_diag in Hsz.
		inversion Hsz as [Hs].
		apply rev_inj in Hfz.
		rewrite Hfz, Hs, Ha in Hc.
		contradiction.
	+	rewrite Ha in Hl.
		contradiction.
	}
Qed.*)

Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.
Notation "n >? m" := (gtb n m).
End Notations.
