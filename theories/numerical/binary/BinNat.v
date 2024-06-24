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

Inductive is_positive : t -> Prop :=
| positive_top : is_positive [1]
| positive_cons : forall b n, is_positive n -> is_positive (b :: n).

Variant is_canonical : t -> Prop :=
| canonical_0 : is_canonical zero
| canonical_pos : forall n, is_positive n -> is_canonical n.

Fixpoint is_canonical_fix b n :=
	match n with
	| [] => b
	| 0 :: tn => is_canonical_fix false tn
	| 1 :: tn => is_canonical_fix true tn
	end.

Definition is_canonical_struct n := is_canonical_fix true n = true.

Lemma one_canonical : forall n, is_canonical n -> is_canonical (1 :: n).
Proof.
	intros n Hn.
	apply canonical_pos.
	{	destruct Hn.
	+	apply positive_top.
	+	apply positive_cons.
		assumption.
	}
Qed.
Lemma is_positive_neq_zero : forall n, is_positive n -> n <> zero.
Proof.
	intros n H.
	destruct H; discriminate.
Qed.

Lemma is_canonical_equiv : forall n, is_canonical n <-> is_canonical_struct n.
Proof.
	intro n.
	unfold is_canonical_struct.
	{	split; intro H.
	+	destruct H; [reflexivity|].
		induction n as [|bn tn HR]; inversion_clear H; [reflexivity|].
		specialize (HR H0).
		apply is_positive_neq_zero in H0.
		destruct tn as [|b tn]; [contradiction|].
		destruct bn, b; assumption.
	+	destruct n as [|bn tn]; [apply canonical_0|].
		apply canonical_pos.
		enough (He:bn :: tn <> [] -> is_positive (bn :: tn))
			by (apply He; discriminate).
		{	induction (bn :: tn) as [|b t HR]; intro He; [contradiction|destruct t].
		+	destruct b; [discriminate|].
			apply positive_top.
		+	apply positive_cons, HR; [|discriminate].
			destruct b, b0; assumption.
		}
	}
Qed.

Theorem is_canonical_decidable : forall n, is_canonical n + {~is_canonical n}.
Proof.
	intro n.
	pose proof (He := is_canonical_equiv n).
	unfold is_canonical_struct in *.
	{	destruct is_canonical_fix.
	+	left; apply He; reflexivity.
	+	right; intro H; apply He in H; discriminate.
	}
Qed.

Lemma inc_positive : forall n, is_canonical n -> is_positive (inc n).
Proof.
	intros n Hn.
	destruct Hn as [|n Hn]; [apply positive_top|].
	{	induction n as [|bn tn HR]; [|destruct bn]; simpl.
	+	apply positive_top.
	+	inversion Hn.
		apply positive_cons.
		assumption.
	+	apply positive_cons.
		inversion Hn; [apply positive_top|].
		apply HR.
		assumption.
	}
Qed.

Lemma is_canonical_struct_false : forall n,
	is_canonical_fix false n = true -> is_canonical_struct n.
Proof.
	intros n H.
	destruct n; [inversion_clear H|].
	assumption.
Qed.
Lemma is_canonical_tl : forall b n, is_canonical (b :: n) -> is_canonical n.
Proof.
	intros b n H.
	inversion_clear H as [|_a Ht].
	inversion_clear Ht; [apply canonical_0|apply canonical_pos; assumption].
Qed.
Lemma is_canonical_struct_tl : forall b n, is_canonical_struct (b :: n) -> is_canonical_struct n.
Proof.
	intros b n H.
	{	destruct n.
	+	reflexivity.
	+	destruct b; destruct b0; assumption.
	}
Qed.

Lemma is_canonical_app : forall n m, is_canonical (n ++ m) -> is_canonical m.
Proof.
	intros n m H.
	{	induction n as [|bn tn HR].
	+	assumption.
	+	{	inversion_clear H as [|_a Ht]; inversion Ht.
		+	apply eq_sym, app_eq_nil, proj2 in H1.
			rewrite H1.
			apply canonical_0.
		+	apply HR, canonical_pos.
			assumption.
		}
	}
Qed.
Lemma app_is_positive : forall n m, is_positive m -> is_positive (n ++ m).
Proof.
	intros n m H.
	{	induction n as [|bn tn HR].
	+	assumption.
	+	apply positive_cons.
		apply HR.
	}
Qed.

Lemma positive_induction (P : t -> Prop) :
		P [1] ->
		(forall m, is_positive m -> P m -> P (inc m)) ->
		forall n, is_positive n -> P n.
Proof.
	intros P1 Pi n Hn.
	revert P P1 Pi.
	assert (is_positive [1]) by (apply positive_top).
	assert (is_positive [0; 1]) by (apply positive_cons, positive_top).
	induction Hn as [|bn tn Hn HR]; intros P P1 Pi; [assumption|].
	{	apply HR; destruct bn.
	+	apply (Pi [1]), P1; assumption.
	+	apply (Pi [0; 1]), (Pi [1]), P1; assumption.
	+	intros m Hm Hp.
		apply (Pi (1 :: m)), (Pi (0 :: m)), Hp; apply positive_cons; assumption.
	+	intros m Hm Hp.
		apply canonical_pos in Hm as Him; apply inc_positive in Him.
		apply (Pi (0 :: (inc m))), (Pi (1 :: m)), Hp; apply positive_cons; assumption.
	}
Qed.
Theorem canonical_induction (P : t -> Prop) :
		P zero ->
		(forall m, is_canonical m -> P m -> P (inc m)) ->
		forall n, is_canonical n -> P n.
Proof.
	intros P0 Pi n Hn.
	destruct Hn as [|n Hn]; [assumption|].
	apply positive_induction; [apply (Pi zero), P0; apply canonical_0| |assumption].
	intros m Hm Hp.
	apply canonical_pos in Hm.
	apply Pi; assumption.
Qed.
Theorem canonical_destruct (P : t -> Prop) :
		P zero ->
		(forall m, is_canonical m -> P (inc m)) ->
		forall n, is_canonical n -> P n.
Proof.
	intros P0 Pi n Hn.
	apply canonical_induction; [assumption| |assumption].
	intros m Hm _.
	apply Pi.
	assumption.
Qed.

Definition safe_zero l :=
	match l with
	| [] => []
	| _ => 0 :: l
	end.

Lemma safe_zero_canonical : forall n, is_canonical n -> is_canonical (safe_zero n).
Proof.
	intros n Hn.
	destruct n; [apply canonical_0|simpl].
	inversion_clear Hn.
	apply canonical_pos, positive_cons.
	assumption.
Qed.

Lemma safe_zero_double : forall n, to_nat (safe_zero n) = 2 * (to_nat n).
Proof.
	intro n.
	destruct n as [|bn tn]; reflexivity.
Qed.

Lemma canonical_unicity : forall n m,
	is_canonical n -> is_canonical m ->
	to_nat n = to_nat m ->
	n = m.
Proof.
	intros n m Hn.
	generalize dependent m.
	{	induction Hn as [|n Hn HR] using canonical_induction;
			intros m Hm Heq; destruct Hm as [|m Hm] using canonical_destruct.
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

Lemma is_canonical_struct_app_fix : forall l r b,
		r <> [] -> is_canonical_fix b (l ++ r) = is_canonical_fix false r.
Proof.
	intros l r b Hr.
	revert b.
	{	induction l as [|bl tl HR]; intros b; simpl in *.
	+	destruct r; [contradiction|reflexivity].
	+	destruct bl; apply HR.
	}
Qed.

Lemma canonical_ones : forall n, is_canonical (repeat 1 n).
Proof.
	intros n.
	apply is_canonical_equiv.
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
	apply is_canonical_equiv.
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
	apply is_canonical_equiv in H.
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
	| 1 :: t => Some (safe_zero t)
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


Lemma dt_dec_length : forall dn dd b, dt_dec dn = (b, dd) -> length dn = length dd.
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; [|destruct bn]; intros dd b H; simpl in *.
	+	inversion_clear H.
		reflexivity.
	+	destruct dt_dec as [tb tdd], tb; inversion_clear H;
			rewrite (HR tdd _ eq_refl); reflexivity.
	+	destruct dt_dec as [tb tdd], tb; inversion_clear H;
			rewrite (HR tdd _ eq_refl); reflexivity.
	}
Qed.

Lemma dt_dec_zero : forall dn dd,
		dt_dec dn = (false, dd) ->
		dn = repeat 0 (length dn) /\ dd = repeat 1 (length dd).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; [|destruct bn]; intros dd H; simpl in *.
	+	inversion_clear H.
		split; reflexivity.
	+	destruct dt_dec as [b tdd], b; [discriminate|].
		specialize (HR tdd eq_refl).
		inversion_clear H.
		rewrite (proj1 HR), (proj2 HR) at 1.
		split; reflexivity.
	+	destruct dt_dec as [b tdd], b; discriminate.
	}
Qed.

Lemma dec_inc : forall (n : t),
	is_canonical n -> dec (inc n) = n.
Proof.
	intros n Hn.
	unfold dec.
	enough (forall n, is_canonical n -> dec_aux (inc n) = Some n);
		[apply H in Hn; rewrite Hn; reflexivity|].
	clear n Hn.
	intros n Hn.
	apply is_canonical_equiv in Hn.
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

Lemma dec_aux_None : forall n, dec_aux n = None <-> to_nat n = O.
Proof.
	intro n.
	{	split; intro H; functional induction (dec_aux n); simpl in *.
	+	reflexivity.
	+	destruct (dec_aux t0); [discriminate|].
		rewrite IHo; reflexivity.
	+	discriminate.
	+	reflexivity.
	+	apply PeanoNat.Nat.eq_add_0 in H; destruct H as [H _].
		rewrite H in IHo.
		rewrite IHo; reflexivity.
	+	discriminate.
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
	+	apply safe_zero_double.
	}
Qed.

Lemma uncons_canonical : forall n r,
		is_canonical n -> dec_aux n = Some r -> is_canonical r.
Proof.
	intros n r Hn Hr.
	apply is_canonical_equiv in Hn.
	apply is_canonical_equiv.
	revert r Hn Hr.
	{	induction n as [|bn tn HR]; [|destruct bn]; intros r Hn Hr; simpl in Hr |- * .
	+	inversion_clear Hr.
	+	destruct dec_aux; [|discriminate].
		specialize (HR l (is_canonical_struct_tl _ _ Hn) eq_refl).
		inversion_clear Hr.
		assumption.
	+	destruct tn; inversion_clear Hr; [reflexivity|].
		destruct b; assumption.
	}
Qed.

Lemma dec_canonical : forall (n : t),
	is_positive n -> is_canonical (dec n).
Proof.
	intros n Hn.
	apply canonical_pos in Hn.
	unfold dec.
	pose proof (H := uncons_canonical n).
	{	destruct (dec_aux n).
	+	exact (H l Hn eq_refl).
	+	apply canonical_0.
	}
Qed.

Notation rev_nat n := (to_nat (rev n)).

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
		is_positive n ->
		is_some (gtb_decomp_borrow n [] dn an) = true.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn]; intros dn an Hn; simpl.
	+	inversion_clear Hn.
	+	inversion_clear Hn.
		apply HR; assumption.
	+	reflexivity.
	}
Qed.
Lemma gtb_cont_decomp_equiv : forall n m dn an,
		is_canonical n ->
		(is_positive m -> is_some (gtb_decomp_aux n m dn an) = gtb_cont true n m)
		/\ (is_canonical m -> is_some (gtb_decomp_borrow n m dn an) = gtb_cont false n m).
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m dn an Hn;
			[|destruct bn; apply is_canonical_tl in Hn as Htn];
			(split; intro Hm; [|inversion_clear Hm as [|_m _Hm]; try rename _Hm into Hm];
		 		try inversion_clear Hm as [|bm tm Htm]); try destruct bm;
			simpl; try reflexivity.
	+	apply HR, canonical_0; assumption.
	+	apply HR; assumption.
	+	apply HR, canonical_pos; assumption.
	+	inversion_clear Hn as [|_a _Htn]; inversion_clear _Htn.
		apply gtb_cont_decomp_equiv_empty; assumption.
	+	apply HR, canonical_0; assumption.
	+	apply HR, canonical_pos; assumption.
	+	apply HR, canonical_pos; assumption.
	+	destruct tn as [|bn tn]; [|destruct bn]; reflexivity.
	+	apply HR; assumption.
	+	destruct tm; [|apply HR; assumption].
		destruct tn as [|bn tn]; [|destruct bn]; reflexivity.
	+	inversion_clear Htn as [|n Hptn]; [reflexivity|].
		destruct tn as [|bn tn]; [inversion_clear Hptn|destruct bn];
			apply gtb_cont_decomp_equiv_empty; assumption.
	+	apply HR; assumption.
	+	apply HR, canonical_pos; assumption.
	}
Qed.

Lemma gtb_decomp_equiv : forall n m,
		is_canonical n ->
		is_canonical m ->
		is_some (gtb_decomp n m) = (n >? m).
Proof.
	intros n m Hn Hm.
	apply gtb_cont_decomp_equiv; assumption.
Qed.

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
		is_canonical m ->
		Some decomp = gtb_decomp n m ->
		is_decomp n m decomp.
Proof.
	intros n m decomp Hm H.
	unfold gtb_decomp in *.
	apply is_canonical_equiv in Hm.
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
		is_canonical n -> is_canonical m ->
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

Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.
Notation "n >? m" := (gtb n m).
End Notations.
