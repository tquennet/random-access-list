From QuickChick Require Import QuickChick Tactics.

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

Fixpoint from_nat (n : nat) : t :=
  match n with
  | O => zero
  | S n => inc (from_nat n)
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

Variant comp :=
	| Eq : comp
	| Lt : t -> dt -> dt -> comp
	| Gt : t -> dt -> dt -> comp.

Record decomp x y tn dn an :=
{
	dec_length : length an = length dn;
	dec_zip : x = rev_append dn (1 :: tn);
	dec_val : S (rev_nat an + to_nat y) = rev_nat (1 :: dn);
}.

Definition comp_op comp :=
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
Qed.

(*********************************)
(* Quick-chick generators *)

Definition bin_eqb := eqb.

Section GMonadDef.
Instance GMonad : `{Monad G} | 3 :=
  {
    ret := @returnGen;
    bind := @bindGen
  }.
End GMonadDef.

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

#[export] Instance ShowBit : Show Bit :=
  {| show := fun b =>
       match b with
         | Zero => "Zero"%string
         | One => "One"%string
       end
  |}.

(* Based on shrinkBool *)
#[export] Instance shrinkBit : Shrink Bit :=
  {| shrink := fun x => match x with One => [Zero] | Zero => [] end |}.

Definition GenBit := elems_ Zero [ Zero ; One ].
Definition GenT : G t := listOf GenBit.

(*
Sample (GenT).

===> QuickChecking GenT
     [[Zero]; [Zero; Zero; One; Zero; One; Zero; Zero; Zero]; [One; One; Zero]; [One; One; Zero]; []; [One]; []; [Zero; Zero; One]; [Zero; One]; []; []]
     Time Elapsed: 0.002667s
*)

Definition GenSizedT : GenSized t :=
  {| arbitrarySized := fun n =>
       do! x <- choose (0, n)%nat ;
       ret (from_nat x) |}.

(*
===> QuickChecking (@arbitrarySized _ GenSizedT 3)
     [[One]; [Zero; One]; [One]; []; [Zero; One]; [One; One]; []; [One]; []; [One]; [Zero; One]]
     Time Elapsed: 0.002629s
*)

(* XXX: decidable equality *)
#[export] Instance Eq__Dec (x y : t) : Dec (x = y).
Admitted.

(*
Lemma compare_decomp_Eq : forall n m,
		is_canonical n -> is_canonical m ->
		Eq = compare n m <-> n = m.
*)

(*********************************)


Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.
Notation "n <? m" := (ltb n m).
End Notations.
