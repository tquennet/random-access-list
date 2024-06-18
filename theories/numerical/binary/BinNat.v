Require Import Lists.List FunInd Arith.
Require Import Init.Nat.
Require Import utils.Utils.
Import ListNotations.

Require Import numerical.Num.

(*Set Mangle Names.*)

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
		{	induction (snoc tn bn) as [|t HR b]; intro He;
				[contradiction|destruct t as [|t0 a]].
		+	destruct b; [discriminate|].
			apply is_positive_Ob1.
		+	assert (is_positive (snoc t0 a)) by
				(apply HR; [destruct b; assumption|discriminate]).
			destruct b; [apply is_positive_snoc0|apply is_positive_snoc1]; assumption.
		}
	+	destruct H as [n Hn|]; [|reflexivity].
		induction n as [|tn HR bn]; [reflexivity|].
		{	inversion_clear Hn as[| _tn Htn | _tn Htn].
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

Lemma is_canonicalb_snoc : forall b0 b1 n,
	is_canonicalb (snoc n b1) = true -> is_canonicalb (snoc (snoc n b1) b0) = true.
Proof.
	intros b0 b1 n H.
	destruct b0; assumption.
Qed.

*)

Lemma is_positive_tl : forall b n, is_positive (snoc n b) -> is_canonical n.
Proof.
	intros b n H.
	{	inversion_clear H.
	+	apply is_Ob.
	+	apply is_pos.
		assumption.
	+	apply is_pos.
		assumption.
	}
Qed.
Lemma is_canonical_tl : forall b n, is_canonical (snoc n b) -> is_canonical n.
Proof.
	intros b n H.
	inversion_clear H as [_n Hn|].
	apply is_positive_tl in Hn.
	assumption.
Qed.

Lemma is_canonical_plug : forall l dl, is_canonical (plug l dl) -> is_canonical l.
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intros l H.
	+	assumption.
	+	apply HR, is_canonical_tl in H.
		assumption.
	}
Qed.

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

Definition bit_to_nat (k: nat)(b: Bit): nat :=
  match b with
  | 0 => 0%nat
  | 1 => 2 ^ k
  end.

Definition list_to_nat := fold_right (fun b a => bit_to_nat O b + 2 * a) O.
Definition to_nat := foldMap Monoid_nat bit_to_nat 0.
Notation ctxt_to_nat n := (to_nat (rev n)).

Lemma to_nat_snoc : forall n b, to_nat (snoc n b) = 2 * (to_nat n) + bit_to_nat O b.
Proof.
	intros n.
	unfold to_nat, foldMap, mapi.
	cbn [mapi foldM Monoid_nat monoid_plus].
	enough (He : forall k, foldM Monoid_nat (mapi bit_to_nat (S k) n) =
		2 * foldM Monoid_nat (mapi bit_to_nat k n)) by
		(rewrite He; reflexivity).
	{	induction n as [|tn HR bn]; intro k.
	+	reflexivity.
	+	cbn [mapi foldM monoid_plus Monoid_nat].
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

(** Zero *)

Lemma to_list_to_nat : forall n, to_nat n = list_to_nat (to_list n).
Proof.
	intro n.
	{	induction n as [|tn HR bn].
	+	reflexivity.
	+	rewrite to_nat_snoc, to_list_snoc, Nat.add_comm, HR.
		reflexivity.
	}
Qed.
Lemma list_to_nat_app : forall m n,
		list_to_nat (n ++ m) = list_to_nat n + list_to_nat m * 2 ^ List.length n.
Proof.
	intros m n.
	{	induction n as [|bn tn HR].
	+	rewrite Nat.mul_1_r.
		reflexivity.
	+	rewrite <- app_comm_cons.
		cbn [list_to_nat fold_right List.length].
		rewrite HR, Nat.mul_add_distr_l, Nat.add_assoc, Nat.mul_shuffle3.
		reflexivity.
	}
Qed.
Lemma to_nat_plug : forall n m,
		to_nat (plug n m) = 2 ^ (List.length m) * to_nat n + ctxt_to_nat m.
Proof.
	intros n m.
	revert n.
	{	induction m as [|bm tm HR]; intro n; cbn [plug gplug].
	+	rewrite <- plus_n_O, Nat.mul_1_l.
		reflexivity.
	+	rewrite HR, (HR (snoc Ob bm)), to_nat_snoc.
		rewrite Nat.mul_add_distr_l, Nat.mul_assoc, (Nat.mul_comm _ 2), <- Nat.pow_succ_r',
			Nat.add_assoc.
		reflexivity.
	}
Qed.
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
Lemma positive_to_nat : forall n, is_positive n -> to_nat n <> O.
Proof.
	intros n Hn.
	{	induction Hn as [|n Hn HR|n Hn HR].
	+	discriminate.
	+	rewrite to_nat_snoc; simpl.
		rewrite <- plus_n_Sm.
		discriminate.
	+	rewrite to_nat_snoc; simpl.
		destruct (to_nat n); [contradiction|].
		rewrite !plus_Sn_m.
		discriminate.
	}
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


(** Peano *)

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
	destruct Hn as [n Hn|]; [|assumption].
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
Lemma to_nat_ssnoc : forall n b, to_nat (ssnoc n b) = 2 * (to_nat n) + bit_to_nat O b.
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
	apply foldr_snoc.
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
	+	rewrite normalize_snoc, to_nat_snoc, <- HR, to_nat_ssnoc.
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

(* necessary for ral facts open proof *)
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


Lemma dt_dec_length : forall dn dd b, dt_dec dn = (b, dd) -> List.length dn = List.length dd.
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
		dn = repeat 0 (List.length dn) /\ dd = repeat 1 (List.length dd).
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
	+	rewrite to_nat_snoc, to_nat_ssnoc.
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
	+	eapply lift_map_conseq; [|exact HR].
		intros x Hx.
		apply is_pos.
		destruct Hx as [x Hx|]; [|apply is_positive_Ob1].
		apply is_positive_snoc1.
		assumption.
	}
Qed.

(** [gt] *)


Definition splug := gplug ssnoc.

Lemma is_canonical_splug : forall l dl, is_canonical l -> is_canonical (splug l dl).
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intros l Hl; simpl.
	+	assumption.
	+	cbn [splug gplug].
		apply HR, is_canonical_ssnoc.
		assumption.
	}
Qed.

Lemma to_nat_splug : forall l dl,
		to_nat (splug l dl) = 2 ^ (List.length dl) * to_nat l + ctxt_to_nat dl.
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intro l; cbn [splug gplug].
	+	rewrite <- plus_n_O, Nat.mul_1_l.
		reflexivity.
	+	rewrite HR, to_nat_ssnoc, !to_list_to_nat, !to_list_rev.
		cbn [List.rev].
		rewrite list_to_nat_app, Nat.mul_add_distr_l, Nat.mul_assoc,
			(Nat.mul_comm _ 2), <- Nat.pow_succ_r', rev_length,
			(Nat.mul_comm (2 ^ (List.length tl))), <- Nat.add_assoc,
			(Nat.add_comm ((bit_to_nat 0 bl) * _)).
		destruct bl; reflexivity.
	}
Qed.

Lemma list_cxt_to_nat : forall n, ctxt_to_nat n = list_to_nat (to_list (rev n)).
Proof.
	intro n.
	rewrite to_list_to_nat.
	reflexivity.
Qed.
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

(*	gérer correctement sub n n *)
Definition sub n m :=
	option_map (fun d => inc (splug d.(dec_tn) (0 :: d.(dec_diff)))) (gt n m).

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



Lemma is_decomp_app : forall x y decomp,
		is_decomp x (app (snoc Ob 0) y) decomp -> is_decomp x y decomp.
Proof.
	intros x y decomp H.
	destruct H as [Hl Hz Hval].
	split; [assumption..|].
	rewrite to_nat_app in Hval.
	simpl in Hval.
	rewrite <- plus_n_O in Hval.
	assumption.
Qed.

Lemma gt_aux_is_decomp : forall x y n m dn dm an decomp,
		x = plug n dn -> y = plug m dm ->		
		List.length an = List.length dn ->
		List.length dm = List.length dn ->
		( is_positive m ->
			Some decomp = gt_aux n m dn an ->
			S (ctxt_to_nat an + ctxt_to_nat dm) = ctxt_to_nat dn ->
			is_decomp x y decomp)
		/\ ( is_canonical m ->
			Some decomp = gt_borrow n m dn an ->
			S (ctxt_to_nat an + ctxt_to_nat dm) = ctxt_to_nat (1 :: dn) ->
			is_decomp x y decomp).
Proof.
	intros x y n m dn dm an decomp Hx Hy.
	apply (f_equal to_list) in Hx, Hy.
	revert y m dn dm an decomp Hx Hy.
	{	induction n as [|tn HR bn]; [|destruct bn];
			intros y m dn dm an decomp Hx Hy Hl1 Hl2;
			(destruct m as [|tm bm]; [|destruct bm]);
			(split; intros Hm H Hval); simpl in *; try discriminate;
			apply (f_equal S) in Hl1 as Hsl1; apply (f_equal S) in Hl2 as Hsl2.
		+	specialize (HR (app (snoc Ob 0) y) Ob (0 :: dn) (0 :: dm) (1 :: an) decomp).
			assert (to_list (app (snoc Ob 0) y) = to_list (plug Ob (0 :: dm))) by
				(rewrite to_list_app, to_list_snoc, Hy, !to_list_rev; reflexivity).
			apply is_decomp_app.
			apply HR; [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app in *.
			simpl in *.
			rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, last_length, !list_to_nat_app.
			simpl.
			rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, !rev_length, Hl1.
			reflexivity.
		+	specialize (HR y tm (0 :: dn) (0 :: dm) (0 :: an) decomp Hx Hy Hsl1 Hsl2).
			inversion_clear Hm as [| |_m Htm].
			apply (proj1 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app in *.
			rewrite <- !plus_n_O.
			assumption.
		+	specialize (HR y tm (0 :: dn) (0 :: dm) (1 :: an) decomp Hx Hy Hsl1 Hsl2).
			apply is_canonical_tl in Hm.
			apply (proj2 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, last_length,
				!list_to_nat_app.
			simpl.
			rewrite <- !plus_n_O, PeanoNat.Nat.add_assoc, !rev_length, Hl1.
			reflexivity.
		+	specialize (HR y tm (0 :: dn) (1 :: dm) (1 :: an) decomp Hx Hy Hsl1 Hsl2).
			apply is_positive_tl in Hm.
			apply (proj2 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app.
			simpl; rewrite <- !plus_n_O.
			rewrite PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval, last_length, !rev_length,
				Hl1, Hl2.
			simpl; rewrite <- plus_n_O.
			reflexivity.
		+	specialize (HR y tm (0 :: dn) (1 :: dm) (0 :: an) decomp Hx Hy Hsl1 Hsl2).
			apply is_canonical_tl in Hm.
			apply (proj2 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, last_length,
				!list_to_nat_app, !rev_length, Hl2.
			simpl; rewrite <- plus_n_O, PeanoNat.Nat.add_assoc.
			reflexivity.
		+	inversion_clear H.
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			rewrite <- Hy in Hval.
			{	split; simpl.
			+	assumption.
			+	apply to_list_inj.
				assumption.
			+	rewrite !list_cxt_to_nat, !to_list_to_nat, !to_list_rev.
				assumption.
			}
		+	specialize (HR y tm (1 :: dn) (0 :: dm) (1 :: an) decomp Hx Hy Hsl1 Hsl2).
			inversion_clear Hm as [| |_m Htm].
			apply positive_non_zero in Htm as Hnz.
			destruct tm; [contradiction|].
			apply (proj1 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app.
			simpl; rewrite <- !plus_n_O.
			rewrite PeanoNat.Nat.add_shuffle0, <- plus_Sn_m, Hval, !rev_length, Hl1.
			reflexivity.
		+	specialize (HR y tm (1 :: dn) (0 :: dm) (0 :: an) decomp Hx Hy Hsl1 Hsl2).
			inversion_clear Hm as [_m Hm2|].
			inversion_clear Hm2 as [| |_m Htm].
			apply (proj1 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app in *.
			simpl in *; rewrite !list_to_nat_app, <- !plus_n_O in *.
			rewrite Hval.
			simpl.
			rewrite <- plus_n_O.
			reflexivity.
		+	{	inversion Hm as [Hvtm|_m Htm Hvtm|].
			+	rewrite <- Hvtm in *; simpl in *.
				inversion_clear H.
				{	split; simpl.
				+	assumption.
				+	apply to_list_inj.
					assumption.
				+	rewrite !list_cxt_to_nat, !to_list_to_nat, !to_list_rev,
						Hy, to_list_plug, to_list_snoc in *.
					simpl.
					rewrite !rev_append_rev, !list_to_nat_app.
					rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval.
					simpl; rewrite <- !plus_n_O, !rev_length, Hl2.
					reflexivity.
				}
			+	apply positive_non_zero in Htm as Hnz.
				destruct tm as [|tm b]; [contradiction|].
				specialize (HR y (snoc tm b) (1 :: dn) (1 :: dm) (0 :: an) decomp Hx Hy Hsl1 Hsl2).
				apply (proj1 HR); [assumption..|].
				rewrite !list_cxt_to_nat, !to_list_rev in *.
				simpl.
				rewrite !list_to_nat_app.
				simpl; rewrite <- !plus_n_O.
				rewrite PeanoNat.Nat.add_assoc, <- plus_Sn_m, Hval, !rev_length, Hl2.
				reflexivity.
			}
		+	specialize (HR y tm (1 :: dn) (1 :: dm) (1 :: an) decomp Hx Hy Hsl1 Hsl2).
			apply is_canonical_tl in Hm as Htm.
			apply (proj2 HR); [assumption..|].
			rewrite !list_cxt_to_nat, !to_list_rev in *.
			simpl.
			rewrite !list_to_nat_app in *.
			simpl in *; rewrite <- !plus_n_O in *.
			rewrite PeanoNat.Nat.add_shuffle1, <- plus_Sn_m, Hval, last_length,
				!list_to_nat_app, !rev_length.
			simpl.
			rewrite <- !plus_n_O, Hl1, Hl2.
			reflexivity.
	}
Qed.

Lemma gt_is_decomp : forall n m decomp,
		is_canonical m ->
		Some decomp = gt n m ->
		is_decomp n m decomp.
Proof.
	intros n m decomp Hm H.
	unfold gt in *.
	apply (gt_aux_is_decomp n m n m [] []) in H;
		(assumption || reflexivity).
Qed.


Lemma sub_canonical : forall n m, is_canonical n -> is_canonical m ->
		option_lift is_canonical (n - m).
Proof.
	intros n m Hn Hm.
	pose proof (H := gt_is_decomp n m).
	unfold sub.
	destruct gt; [|apply I]; simpl.
	destruct (H _ Hm eq_refl) as [_ Hzip _].
	rewrite Hzip in Hn.
	apply is_canonical_plug, is_canonical_tl in Hn.
	apply is_pos, is_positive_inc, is_canonical_splug.
	assumption.
Qed.

Lemma sub_to_nat : forall n m, is_canonical m ->
		option_lift (fun x => to_nat x = (to_nat n - to_nat m)%nat) (n - m).
Proof.
	intros n m Hm.
	pose proof (H := gt_is_decomp n m).
	unfold sub.
	destruct gt as [d|]; [|apply I]; simpl.
	destruct (H _ Hm eq_refl) as [Hlen Hzip Hval], d as [tl dl diff]; simpl in *.
	rewrite inc_S, to_nat_splug, <- (Nat.add_sub _ (to_nat m)), list_cxt_to_nat, to_list_rev.
	cbn [List.rev List.length].
	rewrite list_to_nat_app, plus_Sn_m, (Nat.add_comm (list_to_nat _)), Nat.add_assoc,
		<- Nat.add_assoc, plus_n_Sm, <- to_list_rev, <- list_cxt_to_nat, Hval, Nat.mul_0_l,
		<- plus_n_O.
	replace (plug (snoc tl 1) dl) with (plug tl (1 :: dl)) in Hzip by reflexivity.
	rewrite Hzip, (to_nat_plug tl), Hlen.
	reflexivity.
Qed.

(*Lemma or_list_eq : forall (b : Bit) l1 l2 H, l1 = l2 \/ H -> b :: l1 = b :: l2 \/ H.
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


(*Lemma gtb_total : forall n m,
		n = m \/ n >? m = true \/ m >? n = true.
Proof.
	intro n.
	unfold gtb.
	{	induction n as [|tn HR bn]; [|destruct bn]; intro m;
			(destruct m as [|tm bm]; [|destruct bm]); simpl.
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
*)
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

Lemma le_double_0 : forall n, n <= 0 -> 2 * n <= 0.
Proof.
	intros n H.
	rewrite <- (Nat.mul_0_r 2) at 2.
	apply Nat.mul_le_mono_l.
	assumption.
Qed.

Lemma lt_double_S : forall n m, n < m -> S (2 * n) < 2 * m.
Proof.
	intros n m H.
	simpl; rewrite <- !plus_n_O, <- plus_Sn_m.
	apply Nat.add_le_lt_mono; assumption.
Qed.
Lemma gt_aux_None : forall n m dn an,
		(is_positive m -> gt_aux n m dn an = None -> to_nat n < to_nat m)
		/\ (is_canonical m -> gt_borrow n m dn an = None -> to_nat n <= to_nat m).
Proof.
	intro n.
	{	induction n as [|tn HR bn]; [|destruct bn]; intros m dn an;
			(destruct m as [|tm bm]; [|destruct bm]);
			split; intros Hm H; simpl in *.
	+	inversion_clear Hm.
	+	apply le_n.
	+	apply positive_to_nat in Hm.
		destruct (to_nat (snoc tm 0)); [contradiction|].
		apply Nat.lt_0_succ.
	+	apply le_0_n.
	+	rewrite to_nat_snoc; simpl.
		rewrite <- plus_n_Sm.
		apply Nat.lt_0_succ.		
	+	apply le_0_n.
	+	inversion_clear Hm.
	+	rewrite to_nat_snoc, <- plus_n_O.
		apply le_double_0, (proj2 (HR Ob (0 :: dn) (1 :: an))); assumption.
	+	rewrite !to_nat_snoc, <- !plus_n_O.
		inversion_clear Hm as [| |_n Htm].
		apply Nat.mul_lt_mono_pos_l, (proj1 (HR tm (0 :: dn) (0 :: an))); auto.
	+	rewrite !to_nat_snoc, <- !plus_n_O.
		apply is_canonical_tl in Hm as Htm.
		apply Nat.mul_le_mono_l, (proj2 (HR tm (0 :: dn) (1 :: an))); assumption.
	+	rewrite !to_nat_snoc.
		apply is_positive_tl in Hm as Htm.
		cbn [bit_to_nat pow].
		rewrite <- plus_n_Sm, <- !plus_n_O.
		apply le_n_S, Nat.mul_le_mono_l, (proj2 (HR tm (0 :: dn) (1 :: an))); assumption.
	+	rewrite !to_nat_snoc.
		apply is_canonical_tl in Hm as Htm.
		cbn [bit_to_nat pow].
		rewrite <- plus_n_Sm, <- !plus_n_O.
		apply le_S, Nat.mul_le_mono_l, (proj2 (HR tm (0 :: dn) (0 :: an))); assumption.
	+	inversion_clear Hm.
	+	discriminate.
	+	rewrite !to_nat_snoc.
		inversion_clear Hm as [| |_m Htm].
		cbn [bit_to_nat pow].
		rewrite <- plus_n_Sm, <- !plus_n_O.
		apply lt_double_S.
		destruct tm eqn:Hd; rewrite <- Hd in *;
			apply (proj1 (HR tm (1 :: dn) (1 :: an))); assumption.
	+	rewrite !to_nat_snoc.
		inversion_clear Hm as [_m Hm2|].
		inversion_clear Hm2 as [| |_m Htm].
		cbn [bit_to_nat pow].
		rewrite <- plus_n_Sm, <- !plus_n_O.
		apply Nat.lt_le_incl, lt_double_S.
		apply (proj1 (HR tm (1 :: dn) (0 :: an))); assumption.
	+	rewrite !to_nat_snoc.
		cbn [bit_to_nat pow].
		rewrite <- !plus_n_Sm, <- !plus_n_O.
		apply le_n_S.
		destruct tm as [|tm b]; [discriminate|].
		inversion_clear Hm as [|_m Htm|].
		apply Nat.mul_lt_mono_pos_l, (proj1 (HR (snoc tm b) (1 :: dn) (0 :: an))); auto.
	+	rewrite !to_nat_snoc.
		apply is_canonical_tl in Hm as Htm.
		cbn [bit_to_nat pow].
		rewrite <- !plus_n_Sm, <- !plus_n_O.
		apply le_n_S.
		apply Nat.mul_le_mono_l, (proj2 (HR tm (1 :: dn) (1 :: an))); assumption.
	}
Qed.

Lemma gt_None : forall n m,
		is_canonical m ->
		gt n m = None ->
		to_nat n <= to_nat m.
Proof.
	intros n m Hm H.
	apply (gt_aux_None n m [] []); assumption.
Qed.

Theorem gtb_nat : forall n m,
		is_canonical n -> is_canonical m ->
		n >? m = (to_nat m <? to_nat n)%nat.
Proof.
	intros n m Hn Hm.
	pose proof (Hsome := gt_is_decomp n m).
	pose proof (Hnone := gt_None n m Hm).
	unfold gtb.
	{	destruct gt as [decomp|] eqn:H.
	+	apply eq_sym, Nat.ltb_lt.
		destruct (Hsome decomp Hm eq_refl) as [Hl Hz Hval],
			decomp as [tn dn diff]; simpl in *.
		rewrite <- plus_Sn_m in Hval.
		assert (H1 : to_nat m < ctxt_to_nat (1 :: dn)) by
			(rewrite <- Hval; apply Nat.lt_add_pos_l, Nat.lt_0_succ).
		apply (f_equal to_nat) in Hz.
		rewrite (to_list_to_nat (plug _ _)) in Hz.
		rewrite to_list_plug, to_list_snoc in Hz.
		replace (rev_append dn (1 :: to_list tn)) with (rev_append (1 :: dn) (to_list tn))
			in Hz by reflexivity.
		rewrite rev_append_rev, list_to_nat_app, <- to_list_rev, <- list_cxt_to_nat in Hz.
		assert (H2 : ctxt_to_nat (1 :: dn) <= to_nat n) by (rewrite Hz; apply Nat.le_add_r).
		apply (Nat.lt_le_trans _ (ctxt_to_nat (1 :: dn))); assumption.
	+	apply eq_sym, Nat.ltb_ge, Hnone.
		reflexivity.
	}
Qed.

Lemma gt_inj : forall x n m decompn decompm,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Some decompn = gt x n ->
		Some decompm = gt x m  ->
		n = m <-> decompn = decompm.
Proof.
	intros x n m decompn decompm Hx Hn Hm Hdn Hdm.
	{	split; intro H.
	+	rewrite H, <- Hdm in Hdn.
		inversion_clear Hdn.
		reflexivity.
	+	apply to_nat_inj; [assumption..|].
		pose proof (Hxn := gt_is_decomp x n decompn Hn Hdn).
		pose proof (Hxm := gt_is_decomp x m decompm Hm Hdm).
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

Lemma gt_inj_neq : forall x n m (H : n <> m) decompn decompm,
		is_canonical x -> is_canonical n -> is_canonical m ->
		Some decompn = gt x n ->
		Some decompm = gt x m ->
		decompn.(dec_diff) <> decompm.(dec_diff).
Proof.
	intros x n m H decompn decompm Hx Hn Hm Hcn Hcm Ha.
	assert (Hc : gt x n <> gt x m)
		by (intro Hc; rewrite <- Hcn, <- Hcm in Hc; inversion Hc as [Hc1];
			apply (gt_inj x n m) in Hc1; [contradiction|assumption..]).
	rewrite <- Hcn, <- Hcm in Hc.
	pose proof (Hdn := gt_is_decomp x n decompn Hn Hcn).
	pose proof (Hdm := gt_is_decomp x m decompm Hm Hcm).
	destruct decompn as [tn dn an], decompm as [tm dm am],
		Hdn as [Hln Hzn Hvn], Hdm as [Hlm Hzm Hvm]; simpl in *.
	{	destruct (PeanoNat.Nat.eq_dec (List.length an) (List.length am)) as [Hl|Hl].
	+	rewrite Hlm, Hln, <- (rev_length dn), <- (rev_length dm) in Hl.
		rewrite Hzm in Hzn.
		apply (f_equal to_list) in Hzn.
		apply (f_equal (firstn (List.length (List.rev dm)))) in Hzn as Hfz.
		rewrite !to_list_plug, !to_list_snoc, !rev_append_rev in Hfz.
		rewrite (plus_n_O (List.length (List.rev dm))), firstn_app_2,
			<- Hl, firstn_app_2, !app_nil_r in Hfz.
		apply rev_inj in Hfz.
		apply (f_equal (skipn (List.length (List.rev dm)))) in Hzn as Hsz.
		rewrite !to_list_plug, !to_list_snoc in Hsz.
		rewrite !rev_append_rev, !skipn_app, skipn_all, <- Hl, skipn_all,
			PeanoNat.Nat.sub_diag in Hsz.
		inversion Hsz as [Hs].
		apply to_list_inj in Hs.
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
Notation "n >? m" := (gtb n m) : bin_nat_scope.

End Notations.
