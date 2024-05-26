Require Import Lists.List Arith.
Import ListNotations.

Section Option.

Context {A : Type} (P : A -> Prop).

Definition is_some (o : option A) :=
	match o with
	| None => false
	| Some _ => true
	end.

Variant option_predicate : option A -> Prop :=
	| OP_None : option_predicate None
	| OP_Some : forall a, P a -> option_predicate (Some a).

Definition option_default d (o : option A) :=
	match o with
	| None => d
	| Some x => x
	end.

(*Variant option_bpredicate : option A -> option A -> Prop :=
	| OBP_None : option_bpredicate None None
	| OBP_Some : forall x y,
		BP x y -> option_bpredicate (Some x) (Some y).
 *)
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
		
End List.
