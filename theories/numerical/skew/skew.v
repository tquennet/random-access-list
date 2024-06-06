Require Import Lists.List Init.Nat Arith Psatz.
Require Import utils.FailMonad.
Import ListNotations.

Section skew.

Open Scope nat_scope.

Variables (A T : Type) (merge : A -> T -> T -> T) (leaf : A -> T) (left right : T -> T).
Context {M : Type -> Type} (failMonad : FailMonad unit M).
Hypothesis (left_merge : forall a t t', left (merge a t t') = t).
Hypothesis (right_merge : forall a t t', right (merge a t t') = t').

Local Instance ret : MRet M := failMonad.(monad).(ret).
Local Instance bind : MBind M := failMonad.(monad).(bind).
Local Instance throw : MThrow unit M := failMonad.(throw).

Variant firstbit :=
	| One : nat -> T -> firstbit
	| Two : nat -> T -> T -> firstbit.

Definition bit := (nat * T)%type.

Variant skew :=
	| SNil : skew
	| SIn : firstbit -> list bit -> skew.

Fixpoint to_nat_aux (l : list bit) p :=
	match l with
	| [] => 0
	| (i, _) :: tl => let p := (2 ^ (1 + i)) * p in (p - 1) + to_nat_aux tl p
	end.

Definition to_nat n :=
	match n with
	| SNil => 0
	| SIn (One i _) l => let p := (2 ^ (1 + i)) in (p - 1) + to_nat_aux l p
	| SIn (Two i _ _) l => let p := (2 ^ (1 + i)) in (2 * (p - 1)) + to_nat_aux l p
	end.

Definition cons_aux (l : list bit) n t :=
	match l with
	| [] => (One n t, [])
	| (0, t') :: tl => (Two n t' t, tl)
	| (S m, t') :: tl => (One n t, (m, t') :: tl)
	end.

Definition cons_pos (n : skew) a :=
	match n with
	| SNil => (One 0 (leaf a), [])
	| SIn (One 0 t) l => (Two 0 t (leaf a), l)
	| SIn (One (S n) t) l => (One 0 (leaf a), (n, t) :: l)
	| SIn (Two n t t') l => cons_aux l (S n) (merge a t t')
	end.

Definition sin_of_pair '(fb, l) := SIn fb l.
Definition cons n a := sin_of_pair (cons_pos n a).

Definition shiftl (l : list bit) :=
	match l with
	| [] => SNil
	| (n, t) :: tl => SIn (One (S n) t) tl
	end.

Definition shiftr (l : list bit) :=
	match l with
	| [] => []
	| (n, t) :: tl => (S n, t) :: tl
	end.
Definition tail_pos '(fb, l) :=
	match fb with
	| One 0 t => shiftl l
	| One (S n) t => SIn (Two n (left t) (right t)) (shiftr l)
	| Two 0 t t' => SIn (One 0 t) l
	| Two (S n) t t' => SIn (Two n (left t') (right t')) ((0, t) :: l)
	end.
Definition tail (n : skew) :=
	match n with
	| SNil => throw _ ()
	| SIn fb l => ret _ (tail_pos (fb, l))
	end.

Lemma skew_not_zero : forall n, 2 ^ (S n) - 1 <> 0.
Proof.
	intro n.
	pose proof (Hpow := Nat.pow_nonzero 2 n).
	rewrite Nat.pow_succ_r'.
	destruct (2 ^ n); [contradiction Hpow; [discriminate|reflexivity]|].
	simpl.
	rewrite <- plus_n_Sm.
	discriminate.
Qed.
Lemma le_pow : forall n, 1 <= 2 ^ n.
Proof.
	intro n.
	assert (2 ^ n <> 0) by (apply Nat.pow_nonzero; discriminate).
	destruct (2 ^ n); [contradiction|].
	apply le_n_S, le_0_n.
Qed.
Lemma cons_aux_to_nat : forall n l t0 t1 t2,
		to_nat (sin_of_pair (cons_aux l (S n) t0)) = S (to_nat (SIn (Two n t1 t2) l)).
Proof.
	intros n l t0 t1 t2.
	assert (Hd : forall p, p + p = 2 * p) by (intro p; rewrite (plus_n_O p) at 2; reflexivity).
	{	destruct l as [|bl tl]; [|destruct bl as [m t], m];
			cbn [sin_of_pair cons_aux to_nat to_nat_aux].
	+	rewrite <- (Nat.succ_pred (_ - 1)), <- Nat.sub_succ_r, Nat.mul_sub_distr_l,
			Nat.pow_succ_r'; [|apply skew_not_zero].
		reflexivity.
	+	rewrite Nat.pow_1_r, <- !Nat.pow_succ_r', Nat.add_assoc, <- plus_Sn_m, plus_n_Sm.
		rewrite !Nat.mul_sub_distr_l, Nat.sub_1_r, Nat.succ_pred,
			<- (Nat.add_sub_swap (2 ^ S (1 + n))), Hd;
			[|apply Nat.mul_le_mono_nonneg_l, le_pow; auto
			|apply Nat.pow_nonzero; discriminate].
		reflexivity.
	+	rewrite Nat.mul_sub_distr_l, <- !Nat.pow_add_r, <- Nat.pow_succ_r',
			!plus_Sn_m, <- !plus_n_Sm, plus_O_n.
		rewrite <- (plus_Sn_m ((2 ^ S (S n) - 2))), (Nat.sub_succ_r _ 1), Nat.succ_pred;
			[|apply skew_not_zero].
		reflexivity.
	}
Qed.
Lemma cons_to_nat : forall n a, to_nat (cons n a) = S (to_nat n).
Proof.
	intros n a.
	destruct n as [|fb l]; [reflexivity|].
	{	destruct fb as [n t|n t t'].
	+	destruct n; simpl; [reflexivity|].
		rewrite !(Nat.mul_comm _ 2).
		reflexivity.
	+	cbn [cons].
		apply cons_aux_to_nat.
	}
Qed.
Lemma shiftl_to_nat : forall l, to_nat (shiftl l) = to_nat_aux l 2.
Proof.
	intro l.
	destruct l as [|bl tl]; [reflexivity|destruct bl as [n t]].
	cbn [shiftl to_nat to_nat_aux].
	rewrite !plus_Sn_m, !Nat.pow_succ_r', Nat.mul_comm.
	reflexivity.
Qed.
Lemma shiftr_to_nat : forall l p, to_nat_aux (shiftr l) p = to_nat_aux l (2 * p).
Proof.
	intros l p.
	destruct l as [|bl tl]; [reflexivity|destruct bl as [n t]].
	cbn [shiftr to_nat_aux].
	rewrite Nat.mul_assoc, (Nat.mul_comm _ 2), plus_Sn_m, Nat.pow_succ_r'.
	reflexivity.
Qed.
Lemma tail_to_nat : forall n, (fun r => to_nat r = pred (to_nat n))◻ (tail n).
Proof.
	intro n.
	destruct n as [|fb l]; [apply liftthrow|].
	{	destruct fb as [n t|n t t'], n as [|n]; cbn [tail tail_pos]; rewrite <- liftret.
	+	apply shiftl_to_nat.
	+	cbn [to_nat].
		rewrite plus_Sn_m, Nat.mul_sub_distr_l, Nat.mul_1_r, <- Nat.add_pred_l,
		  	<- Nat.sub_succ_r, shiftr_to_nat, <- !Nat.pow_succ_r'; [|apply skew_not_zero].
		reflexivity.
	+	reflexivity.
	+	cbn [to_nat to_nat_aux plus].
		assert (Hd : forall n, n + n = 2 * n) by
			(intro x; rewrite (plus_n_O x) at 2; reflexivity).
		assert (Hnz : forall n, n <> 0 -> 2 * n <> 0)
			by (intro x; destruct x; simpl; [contradiction|rewrite <- plus_n_Sm;discriminate]).
		rewrite <- Nat.add_pred_l, !Nat.mul_sub_distr_l, <- !Nat.pow_succ_r',
			<- Nat.sub_succ_r; [|apply Hnz, skew_not_zero].
		rewrite Nat.add_assoc, <- Nat.add_sub_swap, Nat.add_sub_assoc;
			[..|apply Nat.mul_le_mono_l; rewrite <- Nat.pow_succ_r']; [|apply le_pow..].
		rewrite Hd, <- Nat.pow_succ_r', <- Nat.sub_add_distr.
		reflexivity.
	}
Qed.


Lemma tail_cons : forall n a, (fun r => r = n)◻ (tail (cons n a)).
Proof.
	intros n a.
	destruct n as [|fb l]; simpl; [rewrite <- liftret; reflexivity|].
	{	destruct fb as [n t|n t t']; [destruct n|]; simpl.
	+	rewrite <- liftret.
		reflexivity.
	+	rewrite <- liftret.
		reflexivity.
	+	destruct l as [|bl tl]; [|destruct bl as [m t''], m];
			simpl; rewrite <- liftret, left_merge, right_merge; reflexivity.
	}
Qed.

Lemma tail_success : forall n s, to_nat n = S s -> exists x, (tail n) = ret _ x /\ (to_nat x) = s.
Proof.
	intros n s H.
	pose proof (Htnat := tail_to_nat n).
	destruct n as [|fb l]; [discriminate|].
	destruct fb as [n t|n t t'], n; trivial; eexists;
		(apply and_wlog_r; [simpl; trivial |
		intro Ht; rewrite Ht, H, <- liftret, <- pred_Sn in Htnat; assumption]).
Qed.
Lemma zero_to_nat : forall n, to_nat n = 0 <-> n = SNil.
Proof.
	intro n.
	{	split; intro H.
	+	destruct n as [|fb l]; [reflexivity|].
		destruct fb as [n t|n t t']; simpl in H;
			assert (2 ^ n <> 0)
			by (intro Hc; apply Nat.pow_nonzero in Hc; [assumption|discriminate]);
			(destruct (2 ^ n); [contradiction|]); simpl in H;
			rewrite <- plus_n_Sm, Nat.sub_0_r, !plus_Sn_m in H; discriminate.
	+	rewrite H.
		reflexivity.
	}
Qed.

End skew.


Section skew_num.

Context {M : Type -> Type} (failMonad : FailMonad unit M).

Let unit_merge : unit -> unit -> unit -> unit := fun _ _ _ => ().
Let unit_leaf : unit -> unit := fun _ => ().
Let liftbind {A B : Type} {P : A -> Prop} {P' : B -> Prop} x Hb f H
	:= failMonad.(liftbind) P P' f x H Hb.

Definition t := skew unit.
Definition inc (n : t) := cons _ _ unit_merge unit_leaf n ().
Definition dec (n : t) := tail _ unit_leaf unit_leaf _ n.

Definition zero := SNil unit.

Lemma skew_S_inc : forall n s, to_nat _ n = S s -> exists m, inc m = n /\ to_nat _ m = s.
Proof.
	intros n s Hs.
	pose proof (Htn := tail_to_nat _ unit_leaf unit_leaf _ n).
	rewrite Hs in Htn.
	destruct n as [|fb l]; [discriminate|cbn [tail] in Htn].
	rewrite <- (liftret _ (tail_pos _ unit_leaf unit_leaf (fb, l))) in Htn.
	exists (tail_pos _ unit_leaf unit_leaf (fb, l)).
	destruct fb as [n t|n t t'], n; (destruct l as [|bl tl]; [|destruct bl]);
		simpl in *;
		(split; [destruct t; try destruct t'; reflexivity|assumption]).
Qed.

Theorem skew_num_induction (P : t -> Prop) :
		P zero ->
		(forall n, P n -> P (inc n)) ->
		forall n, P n.
Proof.
	intros Pz Pi n.
	remember (to_nat _ n) as s eqn:Hs.
	symmetry in Hs.
	revert n Hs.
	{	induction s as [|s HR]; intros n Hs.
	+	apply zero_to_nat in Hs.
		rewrite Hs.
		apply Pz.
	+	destruct (skew_S_inc n s Hs) as [x Hx], Hx as [Hx Hxs].
		rewrite <- Hx.
		apply Pi, HR.
		assumption.
		
	}
Qed.

End skew_num.
