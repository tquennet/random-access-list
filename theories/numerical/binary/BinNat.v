Require Import Lists.List FunInd Arith.
Require Import Init.Nat.
Require Import utils.Utils.
Import ListNotations.

Require Import numerical.Num.

Declare Scope bin_nat_scope.
Open Scope nat_scope.
Open Scope bin_nat_scope.

(********************************************************************************)
(** * Binary numbers

Notations are defined in [bin_nat_scope].

** Predicates:

- [is_canonical n] <=> there is no trailing zeros

All the constructors in the file produce canonical binary numbers and
operations preserve canonicity.

** Constructors:

- [t] == the type of binary numbers, with lowest-significant-bit first
- [dt] == the type of binary numbers with most-significant-bit first,
  understood as the one-hole context of the type [t].
- [zero] == binary number representing 0

** Operations:

- [inc n] == the successor of [n] [dec n] == the predecessor of [n]
- [gtb n m], [n >? m] <=> [n] is (strictly) greater than [m]
- [sub n m], [n - m] == the difference between [n] and [m]

** Conversions:

- [to_nat n] == convert [n] to Coq Peano natural number
- [normalize bs] == turn any element of [t] into an equivalent,
  canonical binary number

*)
(********************************************************************************)

Reserved Notation "n >? m" (at level 70).

Variant Bit := Zero | One.
Definition t := Num Bit.
Definition dt := list Bit.

Notation "0" := Zero.
Notation "1" := One.

(** Canonicity *)

Inductive is_positive : t -> Prop :=
  | is_positive_Ob1 : is_positive (snoc Ob 1)
  | is_positive_snoc1 : forall n, is_positive n -> is_positive (snoc n 1)
  | is_positive_snoc0 : forall n, is_positive n -> is_positive (snoc n 0).

Inductive is_canonical : t -> Prop :=
  | is_pos : forall n, is_positive n -> is_canonical n
  | is_Ob : is_canonical Ob.

Fixpoint is_canonicalb_aux b n :=
	match n with
	| Ob => b
	| snoc tn 0 => is_canonicalb_aux false tn
	| snoc tn 1 => is_canonicalb_aux true tn
	end.

Definition is_canonicalb n := is_canonicalb_aux true n.

Lemma is_canonicalb_false : forall n,
	is_canonicalb_aux false n = true -> is_canonicalb n = true.
Proof.
	intros n H.
	destruct n; [inversion_clear H|].
	assumption.
Qed.

Theorem decide_is_canonicalb: forall n, is_canonicalb n = true <-> is_canonical n.
	intro n.
	unfold is_canonicalb.
	{	split; intro H.
	+	destruct n as [|tn bn]; [apply is_Ob|].
		apply is_pos.
		enough (He: (snoc tn bn) <> Ob -> is_positive (snoc tn bn))
			by (apply He; discriminate).
		{	induction (snoc tn bn) as [|t HR b]; intro He; [contradiction|destruct t].
		+	destruct b; [discriminate|].
			apply is_positive_Ob1.
		+	assert (is_positive (snoc t0 a)) by
				(apply HR; [destruct b; assumption|discriminate]).
			destruct b; [apply is_positive_snoc0|apply is_positive_snoc1]; assumption.
		}
	+	destruct H; [|reflexivity].
		induction n as [|tn HR bn]; [reflexivity|].
		{	inversion_clear H as[| _tn Htn | _tn Htn].
		+	reflexivity.
		+	apply HR.
			assumption.
		+	destruct tn as [|tn b]; [inversion Htn|].
			apply is_canonicalb_false, HR.
			assumption.
		}
	}
Qed.

(*
Lemma is_canonicalb_aux_false : forall n,
	is_canonicalb_aux false n = true -> is_canonicalb n = true.
Proof.
	intros n H.
	destruct n; [inversion_clear H|].
	assumption.
Qed.

Lemma is_canonicalb_snoc : forall b0 b1 n,
	is_canonicalb (snoc n b1) = true -> is_canonicalb (snoc (snoc n b1) b0) = true.
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

Lemma is_canonical_struct_tl : forall b n, is_canonical_struct (snoc n b) -> is_canonical_struct n.
Admitted.
(*
Proof.
	intros b n H.
	{	destruct n.
	+	reflexivity.
	+	destruct b; destruct b0; assumption.
	}
Qed.
*)
*)


(* XXX: delete?
Definition not b :=
	match b with
	| 0 => 1
	| 1 => 0
	end.

Definition complement := mapi (fun _ => not).
Lemma complement_length : forall n,
		length (complement n) = length n.
Proof.
	intros n.
	apply mapi_length.
Qed.
Lemma complement_inj : forall n m,
		complement n = complement m -> n = m.
Admitted.
(*
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m H; destruct m as [|bm tm];
			[|discriminate..|]; simpl in *.
	+	reflexivity.
	+	inversion H.
		destruct bn, bm; [|discriminate..|]; f_equal; apply HR; assumption.
	}
Qed.*)
*)

(*

Lemma is_canonicalb_snoc : forall b0 b1 n,
	is_canonicalb (snoc n b1) = true -> is_canonicalb (snoc (snoc n b1) b0) = true.
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

Lemma is_canonical_struct_tl : forall b n, is_canonical_struct (snoc n b) -> is_canonical_struct n.
Admitted.
(*
Proof.
	intros b n H.
	{	destruct n.
	+	reflexivity.
	+	destruct b; destruct b0; assumption.
	}
Qed.
*)
*)


(* XXX: delete?
Definition not b :=
	match b with
	| 0 => 1
	| 1 => 0
	end.

Definition complement := mapi (fun _ => not).
Lemma complement_length : forall n,
		length (complement n) = length n.
Proof.
	intros n.
	apply mapi_length.
Qed.
Lemma complement_inj : forall n m,
		complement n = complement m -> n = m.
Admitted.
(*
Proof.
	intro n.
	{	induction n as [|bn tn HR]; intros m H; destruct m as [|bm tm];
			[|discriminate..|]; simpl in *.
	+	reflexivity.
	+	inversion H.
		destruct bn, bm; [|discriminate..|]; f_equal; apply HR; assumption.
	}
Qed.*)
*)

(** [to_nat] *)

(*Fixpoint to_nat_rec n : nat :=
	match n with
	| Ob => O
	| snoc t 0 => 2 * (to_nat_rec t)
	| snoc t 1 => S (2 * to_nat_rec t)
	end.*)

Definition bit_to_nat (k: nat)(b: Bit): nat :=
  match b with
  | 0 => 0%nat
  | 1 => 2 ^ k
  end.

Definition to_nat := foldMap Monoid_nat bit_to_nat.

Lemma to_nat_snoc : forall n b, to_nat (snoc n b) = 2 * (to_nat n) + bit_to_nat O b.
Proof.
	intros n.
	unfold to_nat, foldMap, mapi.
	cbn [mapi_aux foldM Monoid_nat monoid_plus].
	enough (He : forall k, foldM Monoid_nat (mapi_aux bit_to_nat (S k) n) =
		2 * foldM Monoid_nat (mapi_aux bit_to_nat k n)) by
		(rewrite He; reflexivity).
	{	induction n as [|tn HR bn]; intro k.
	+	reflexivity.
	+	cbn [mapi_aux foldM monoid_plus Monoid_nat].
		rewrite Nat.mul_add_distr_l, HR.
		destruct bn; reflexivity.
	}
Qed.

Lemma to_nat_app : forall n m, to_nat (app m n) = (to_nat n + to_nat m * 2 ^ length n).
	intros n m.
	{	induction n as [|tn HR bn]; [|destruct bn]; cbn [length app].
	+	rewrite PeanoNat.Nat.mul_1_r.
		reflexivity.
	+	rewrite !to_nat_snoc, Nat.pow_succ_r', Nat.mul_shuffle3, <- !plus_n_O,
			<- Nat.mul_add_distr_l, <- HR.
		reflexivity.
	+	rewrite !to_nat_snoc, Nat.pow_succ_r', Nat.mul_shuffle3, Nat.add_shuffle0,
			<- Nat.mul_add_distr_l, <- HR.
		reflexivity.
	}
Qed.

(*
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
*)

(** Zero *)

Definition zero : t := Ob.

Theorem is_canonical_zero: is_canonical zero.
Proof. apply is_Ob. Qed.

(** Inc *)

Fixpoint inc n :=
	match n with
	| Ob => snoc Ob 1
	| snoc t 0 => snoc t 1
	| snoc t 1 => snoc (inc t) 0
	end.

Lemma positive_non_zero : forall n, is_positive n -> n <> zero.
Proof.
	intros n Hn.
	destruct n; [inversion Hn|].
	discriminate.
Qed.

Theorem is_positive_inc: forall n, is_canonical n -> is_positive (inc n).
Proof.
	intros n Hn.
	destruct Hn as [n Hn|]; [|apply is_positive_Ob1].
	{	induction n as [|tn HR bn]; [|destruct bn]; simpl.
	+	apply is_positive_Ob1.
	+	inversion Hn.
		apply is_positive_snoc1.
		assumption.
	+	apply is_positive_snoc0.
		inversion Hn; [apply is_positive_Ob1|].
		apply HR.
		assumption.
	}
Qed.

Theorem inc_S : forall n, to_nat (inc n) = S (to_nat n).
Proof.
	intro n.
	{	induction n as [|tn HR bn]; [|destruct bn]; simpl.
	+	reflexivity.
	+	rewrite !to_nat_snoc, plus_n_Sm.
		reflexivity.
	+	rewrite !to_nat_snoc, plus_n_Sm, <- plus_n_O, HR, Nat.mul_succ_r.
		reflexivity.
	}
Qed.

Lemma positive_induction (P : t -> Prop) :
		P (snoc Ob 1) ->
		(forall m, is_positive m -> P m -> P (inc m)) ->
		forall n, is_positive n -> P n.
Proof.
	intros P1 Pi n Hn.
	revert P P1 Pi.
	pose (V1 := snoc Ob 1).
	pose (V01 := (snoc (snoc Ob 1) 0)).
	assert (H1 : is_positive V1)
		by (apply is_positive_Ob1).
	assert (H01 : is_positive V01)
		by (apply is_positive_snoc0, is_positive_Ob1).
	{	induction Hn as [|tn Hn HR|tn Hn HR]; intros P P1 Pi; [assumption|apply HR..].
	+	apply (Pi V01), (Pi V1), P1; assumption.
	+	intros m Hm Hp.
		apply is_pos in Hm as Him; apply is_positive_inc in Him.
		apply (Pi (snoc (inc m) 0)), (Pi (snoc m 1)), Hp;
			[apply is_positive_snoc0|apply is_positive_snoc1]; assumption.
	+	apply (Pi V1), P1; assumption.
	+	intros m Hm Hp.
		apply (Pi (snoc m 1)), (Pi (snoc m 0)), Hp;
			[apply is_positive_snoc1|apply is_positive_snoc0]; assumption.
	}
Qed.
Theorem canonical_induction (P : t -> Prop) :
		P zero ->
		(forall m, is_canonical m -> P m -> P (inc m)) ->
		forall n, is_canonical n -> P n.
Proof.
	intros P0 Pi n Hn.
	destruct Hn as [|n Hn]; [|assumption].
	apply positive_induction; [apply (Pi zero), P0; apply is_Ob| |assumption].
	intros m Hm Hp.
	apply is_pos in Hm.
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

Lemma to_nat_zero : forall n, is_canonical n -> to_nat n = O -> n = zero.
Proof.
	intros n Hn H.
	{	destruct Hn as [|n Hn] using canonical_destruct.
	+	reflexivity.
	+	rewrite inc_S in H.
		discriminate.
	}
Qed.
Lemma to_nat_inj : forall n m,
	is_canonical n -> is_canonical m ->
	to_nat n = to_nat m ->
	n = m.
Proof.
	intros n m Hn.
	revert m.
	{	induction Hn as [|n Hn HR] using canonical_induction; intros m Hm H.
	+	apply eq_sym in H.
		apply eq_sym, to_nat_zero; assumption.
	+	destruct Hm as [|m Hm] using canonical_destruct;
		  rewrite !inc_S in H; [discriminate|].
		inversion H as [Ht].
		rewrite (HR m); [reflexivity|assumption..].
	}
Qed.

(*
Lemma inc_decomp : forall (n : t),
	exists b tn, snoc tn b = inc n.
Admitted.
(*
Proof.
	intros n.
	{	destruct n as [|b tn]; [|destruct b].
	+	exists 1, Ob; reflexivity.
	+	exists 1, tn; reflexivity.
	+	exists 0, (inc tn); reflexivity.
	}
Qed.
*)

Lemma inc_non_empty : forall n, inc n <> Ob.
Proof.
	intro n.
	pose (H := inc_decomp n).
	destruct H as [b H], H as [t H].
	rewrite <- H.
	discriminate.
Qed.
*)

(*
Lemma is_canonical_inc_struct : forall (n : t),
	is_canonical_struct n ->
	is_canonical_struct (inc n).
Admitted.
(*
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
*)
*)

(*
Lemma canonical_double : forall (n : t),
	is_canonical n -> is_canonical (snoc (inc n) 0).
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
*)

(*
Lemma is_canonical_struct_app_fix : forall l r b,
		r <> Ob -> is_canonical_struct_fix b (app l r) = is_canonical_struct_fix false r.
Admitted.
(*
Proof.
	intros l r b Hr.
	revert b.
	{	induction l as [|bl tl HR]; intros b; simpl in *.
	+	destruct r; [contradiction|reflexivity].
	+	destruct bl; apply HR.
	}
Qed.
*)

Lemma is_canonical_struct_app : forall l r,
		r <> Ob -> is_canonical_struct (app l r) <-> is_canonical_struct r.
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

(*
Lemma canonical_ones : forall n, is_canonical (repeat 1 n).
Proof.
	intros n.
	apply is_canonical_struct_equiv.
	{	induction n as [|n HR]; simpl.
	+	reflexivity.
	+	assumption.
	}
Qed.
*)
*)

(** normalize *)

Definition ssnoc n b :=
	match n, b with
	| Ob, 0 => Ob
	| _, _ => snoc n b
	end.

Lemma ssnoc_of_positive : forall n b, is_positive n -> ssnoc n b = snoc n b.
Proof.
	intros n b Hn.
	pose proof (positive_non_zero _ Hn).
	destruct n; [contradiction|].
	reflexivity.
Qed.
Lemma to_nat_snocc : forall n b, to_nat (ssnoc n b) = 2 * (to_nat n) + bit_to_nat O b.
Proof.
	intros n b.
	destruct n; [destruct b; reflexivity|cbn [ssnoc]].
	apply to_nat_snoc.
Qed.

Lemma is_canonical_ssnoc : forall n b, is_canonical n -> is_canonical (ssnoc n b).
Proof.
	intros n b Hn.
	{	destruct n as [|n bn], b.
	+	apply is_Ob.
	+	apply is_pos, is_positive_Ob1.
	+	inversion_clear Hn as [_n Hpn|].
		apply is_pos, is_positive_snoc0.
		assumption.
	+	inversion_clear Hn as [_n Hpn|].
		apply is_pos, is_positive_snoc1.
		assumption.
	}
Qed.

Definition normalize n := foldr ssnoc Ob n.

Lemma normalize_snoc : forall n b, normalize (snoc n b) = ssnoc (normalize n) b.
Proof.
	intros n b.
	apply fold_snoc.
Qed.
Theorem is_canonical_normalize : forall n, is_canonical (normalize n).
Proof.
	intro n.
	{	induction n as [|tn HR bn]; [|destruct bn].
	+	apply is_Ob.
	+	rewrite normalize_snoc.
		apply is_canonical_ssnoc.
		assumption.
	+	rewrite normalize_snoc.
		apply is_canonical_ssnoc.
		assumption.
	}
Qed.
Lemma to_nat_normalize : forall n, to_nat (normalize n) = to_nat n.
Proof.
	intro n.
	{	induction n as [|tn HR bn].
	+	reflexivity.
	+	rewrite normalize_snoc, to_nat_snoc, <- HR, to_nat_snocc.
		reflexivity.
	}
Qed.

(** [dec] *)

Fixpoint dec n :=
	match n with
	| Ob => None
	| snoc t 1 => Some (ssnoc t 0)
	| snoc t 0 => option_map (fun r => snoc r 1) (dec t)
	end.

(* XXX: REMOVE
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
Qed. *)

Lemma dec_inc : forall (n : t),
	is_canonical n -> dec (inc n) = Some n.
Proof.
	intros n Hn.
	destruct Hn as [n Hn|]; [|reflexivity].
	{	induction Hn as [|tn Hn HR|tn Hn HR]; simpl.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	+	rewrite ssnoc_of_positive; [|assumption].
		reflexivity.
	}
Qed.

(*Local Lemma dec_aux_None : forall n, dec n = None <-> to_nat n = O.
Admitted.
Proof.
	intro n.
	{	split; intro H; functional induction (dec n); simpl in *.
	+	reflexivity.
	+	destruct (dec t0); [discriminate|].
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
Qed. *)

Definition option_lift {A} (P : A -> Prop)(a: option A): Prop :=
  match a with
  | None => True
  | Some a => P a
  end.

Definition splug := plug ssnoc.
Definition plug : t -> dt -> t := plug snoc.

Lemma dec_Some : forall n, is_some (dec n) = true -> to_nat n <> O.
Proof.
	intros n H.
	{	induction n as [|tn HR bn]; [|destruct bn; rewrite to_nat_snoc]; simpl in H.
	+	discriminate.
	+	rewrite <- plus_n_O.
		destruct (dec tn); [|discriminate].
		apply Nat.neq_mul_0.
		split; [discriminate|].
		apply HR; reflexivity.
	+	simpl.
		rewrite <- plus_n_Sm.
		discriminate.
	}
Qed.

Theorem dec_pred : forall n,
	option_lift (fun r => to_nat r = pred (to_nat n)) (dec n).
Proof.
	intro n.
	{	induction n as [|tn HR bn]; [|destruct bn]; simpl.
	+	apply I.
	+	pose proof (Hds := dec_Some tn).
		destruct (dec tn) as [r|]; simpl in *; [|apply I].
		rewrite !to_nat_snoc, <- plus_n_O, HR, Nat.mul_pred_r, <- Nat.sub_1_r,
			Nat.add_comm, Nat.add_sub_assoc; [reflexivity|].
		destruct (to_nat tn); [contradiction Hds; reflexivity|].
		simpl.
		rewrite <- plus_n_O, <- plus_n_Sm.
		apply le_n_S, le_n_S, le_0_n.
	+	rewrite to_nat_snoc, to_nat_snocc.
		cbn [bit_to_nat pow].
		rewrite <- plus_n_Sm.
		reflexivity.
	}
Qed.

Lemma dec_canonical : forall (n : t),
	is_canonical n -> option_lift is_canonical (dec n).
Proof.
	intros n Hn.
	destruct Hn as [n Hn|]; [|apply I].
	{	induction Hn as [|n Hn HR|n Hn HR]; cbn [dec].
	+	apply is_Ob.
	+	apply is_canonical_ssnoc, is_pos.
		assumption.
	+	destruct (dec n) as [r|]; simpl in *; [|apply I].
		apply is_pos.
		destruct HR as [r HR|]; [|apply is_positive_Ob1].
		apply is_positive_snoc1.
		assumption.
	}
Qed.

(** [gt] *)

Notation ctxt_to_nat n := (to_nat (plug Ob n)).

Record decomp := mkZip
{
	dec_tn : t;
	dec_dn : dt;
	dec_diff : dt;
}.

Record is_decomp x y decomp :=
{
	dec_length : List.length decomp.(dec_diff) = List.length decomp.(dec_dn);
	dec_zip : x = plug (snoc decomp.(dec_tn) 1) decomp.(dec_dn);
	dec_val : S (ctxt_to_nat decomp.(dec_diff) + to_nat y) = ctxt_to_nat (1 :: decomp.(dec_dn));
}.

Fixpoint gt_aux (n : t) (m : t) (dn : dt) (an : dt) :=
	match n, m with
	| Ob, _ => None
	| _, Ob => None (* unreachable if m canonical *)
	| snoc tn 1, snoc Ob 1 => Some (mkZip tn dn an)
	| snoc tn (0 as bit), snoc tm 0
        | snoc tn (1 as bit), snoc tm 1
		=> gt_aux tn tm (bit :: dn) (0 :: an)
	| snoc tn (1 as bit), snoc tm 0 => gt_aux tn tm (bit :: dn) (1 :: an)
	| snoc tn (0 as bit), snoc tm 1 => gt_borrow tn tm (bit :: dn) (1 :: an)
	end
with gt_borrow (n : t) (m : t) (dn : dt) (an : dt) :=
	match n, m with
	| Ob, _ => None
	| snoc tn (0 as bit), Ob => gt_borrow tn Ob (bit :: dn) (1 :: an)
	| snoc tl 1, Ob => Some (mkZip tl dn an)
	| snoc tn (0 as bit), snoc tm 0 | snoc tn (1 as bit), snoc tm 1
		=> gt_borrow tn tm (bit :: dn) (1 :: an)
	| snoc tn (0 as bit), snoc tm 1 => gt_borrow tn tm (bit :: dn) (0 :: an)
	| snoc tn (1 as bit), snoc tm 0 => gt_aux tn tm (bit :: dn) (0 :: an)
	end.

Definition gt n m := gt_borrow n m [] [].

Definition gtb n m := 
  match gt n m with
  | None => false
  | Some _ => true
  end.

Notation "n >? m" := (gtb n m) : bin_nat_scope.

Definition sub n m :=
  option_map (fun d => splug d.(dec_tn) (0 :: d.(dec_diff))) (gt n m).

Notation "n - m" := (sub n m) : bin_nat_scope.

(* XXX: Delete
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
*)

(*
Lemma gtb_cont_decomp_equiv_empty : forall n dn an,
		is_canonical_struct n -> n <> Ob ->
		is_some (gtb_decomp_borrow n Ob dn an) = true.
Admitted.
*)
(*
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
*)


(*
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
*)

Theorem gtb_nat : forall n m,
		is_canonical n -> is_canonical m ->
		n >? m = (to_nat m <? to_nat n)%nat.
Admitted.
(*
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
*)

Lemma gt_inj : forall x n m decompn decompm,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Some decompn = gt x n ->
		Some decompm = gt x m  ->
		n = m <-> decompn = decompm.
Admitted.
(*
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
*)

Lemma gtb_decomp_neq : forall x n m (H : n <> m) decompn decompm,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Some decompn = gt x n ->
		Some decompm = gt x m ->
		decompn.(dec_diff) <> decompm.(dec_diff).
Admitted.
(*
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
*)

(** Peano *)

Inductive is_Nat : t -> Prop :=
	| canonical_0 : is_Nat Ob
	| canonical_inc : forall (n : t),
		is_Nat n -> is_Nat (inc n).

Local Lemma canonical_1 : is_Nat (snoc Ob 1).
Proof.
	replace (snoc Ob 1) with (inc Ob) by reflexivity.
	apply canonical_inc, canonical_0.
Qed.

Theorem nat_ind: forall (P: t -> Prop),
    P Ob ->
    (forall n, is_canonical n -> P n -> P (inc n)) ->
    forall n, is_canonical n -> P n.
Admitted.

(** Notations *)

Module Notations.

Notation "0" := Zero : bin_nat_scope.
Notation "1" := One : bin_nat_scope.
Notation "n - m" := (sub n m) : bin_nat_scope.
Notation "n >? m" := (gtb n m) : bin_nat_scope.

End Notations.
