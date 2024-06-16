Require Import Lists.List Arith.
Import ListNotations.

Section Monoid.

Record Monoid (S : Type) : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

Definition Monoid_nat : Monoid nat :=
  {| monoid_plus := Init.Nat.add ; monoid_unit := 0%nat |}.

Definition Monoid_endol {A} : Monoid (A -> A) :=
  {| monoid_plus := fun f g a => f (g a);
     monoid_unit := fun a => a |}.
Definition Monoid_endor {A} : Monoid (A -> A) :=
  {| monoid_plus := fun f g a => g (f a);
     monoid_unit := fun a => a |}.

Definition Monoid_Prop : Monoid Prop :=
  {| monoid_plus := and ; monoid_unit := True |}.

End Monoid.

Arguments monoid_unit {S} m.
Arguments monoid_plus {S} m m2.

Section Option.

Context {A : Type}.

Definition is_some (o : option A) :=
	match o with
	| None => false
	| Some _ => true
	end.

Definition option_lift {A} (P : A -> Prop)(a: option A): Prop :=
  match a with
  | None => True
  | Some a => P a
  end.

Lemma lift_map {X Y}: forall (P : Y -> Prop)(r: option X)(f: X -> Y),
    option_lift P (option_map f r)
    = option_lift (fun t => P (f t)) r.
Proof. intros *; destruct r; auto. Qed.

Lemma lift_conseq {X}: forall (P Q : X -> Prop)(r: option X),
    (forall x, P x -> Q x) ->
    option_lift P r -> option_lift Q r.
Proof. intros; destruct r; simpl; auto. Qed.

(*Variant option_predicate : option A -> Prop :=
	| OP_None : option_predicate None
	| OP_Some : forall a, P a -> option_predicate (Some a).*)


Lemma lift_map_conseq {X Y} : forall (P : X -> Prop) (Q : Y -> Prop) (r : option X) (f : X -> Y),
		(forall x, P x -> Q (f x)) ->
		option_lift P r -> option_lift Q (option_map f r).
Proof.
	intros P Q r f Hf H.
	rewrite lift_map.
	eapply lift_conseq; [apply Hf|apply H].
Qed.
Definition option_default d (o : option A) :=
	match o with
	| None => d
	| Some x => x
	end.

End Option.

Section Options.

Context {A B C : Type} (P : B -> Prop) (f g : A -> B) (h : B -> C) (i : A -> A) (j : A -> option B).

Definition option_join o :=
	match o with
	| Some a => j a
	| None => None
	end.

Lemma option_map_map : forall o,
		option_map h (option_map f o) = option_map (fun x => h (f x)) o.
Proof.
	intro o.
	destruct o; reflexivity.
Qed.

Lemma option_default_map_inv : forall d (o : option A),
	(o = None -> P d) ->
	(forall x, o = Some x -> P (f x)) ->
	P (option_default d (option_map f o)).
Proof.
	intros d o Hd Hf.
	{	destruct o; simpl.
	+	apply Hf.
		reflexivity.
	+	apply Hd.
		reflexivity.
	}
Qed.

Lemma option_map_inj : forall o1 o2,
		(forall x y, (f x = f y -> x = y)) ->
		option_map f o1 = option_map f o2 ->
		o1 = o2.
Proof.
	intros o1 o2 Hinj H.
	destruct o1, o2; [|discriminate..|reflexivity].
	inversion H.
	apply Hinj in H1.
	rewrite H1.
	reflexivity.
Qed.
Lemma option_map_inv : forall o,
		(forall x, (i x = x)) ->
		option_map i o = o.
Proof.
	intros o Hrew.
	destruct o; [|reflexivity].
	simpl.
	rewrite Hrew.
	reflexivity.
Qed.
End Options.

Definition option_bind {A B}(o: option A)(f : A -> option B) := option_join f o.

Lemma bind_fail {X Y}: forall (m: option X),
    option_bind (B := Y) m (fun _ => None) = None.
Proof. intros; destruct m; auto. Qed.

Lemma bind_map {X Y Z}: forall (f: X -> Y)(r: option X)(k: Y -> option Z),
    option_bind
      (option_map f r) k
    = option_bind r (fun t => k (f t)).
Proof. intros *; destruct r; auto. Qed.

Section List.

Context {A : Type}.

Lemma list_select_neq : forall n l0 l1 (a b : A),
		n <> (length l0) ->
		nth n (l0 ++ [b] ++ l1) a = nth n (l0 ++ [a] ++ l1) a.
Proof.
	intros n l0 l1 a b Hn.
	{	destruct (le_lt_dec (length l0) n).
	+	rewrite !(app_nth2 l0); [|assumption..].
		assert (n - length l0 <> 0).
		{
			intro H.
			apply (f_equal (fun x => plus x (length l0))) in H.
			rewrite Nat.sub_add in H; [contradiction|assumption].
		}
		destruct (n - length l0); [contradiction|].
		reflexivity.
	+	rewrite !(app_nth1 l0); [|assumption..].
		reflexivity.
	}
Qed.
		

Lemma repeat_simpl : forall l (a : A) n, l = repeat a n -> l = repeat a (length l).
Proof.
	intros l a n.
	revert l.
	{	induction n as [|n HR]; intros l H.
	+	rewrite H.
		reflexivity.
	+	destruct l as [|x tl]; [discriminate|].
		inversion H; simpl.
		f_equal.
		apply HR.
		reflexivity.
	}
Qed.

End List.

Section Fun.

Context {A : Type} (f : A -> A).

Fixpoint fun_pow n x :=
	match n with 
	| O => x
	| S n => fun_pow n (f x)
	end.

Lemma fun_pow_comm : forall n x, f (fun_pow n x) = fun_pow n (f x).
Proof.
	intro n.
	{	induction n as [|n HR]; intro x.
	+	reflexivity.
	+	simpl.
		rewrite HR.
		reflexivity.
	}
Qed.

End Fun.
