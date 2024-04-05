
Require Import Lists.List.
Import ListNotations.

Section Option.

Context {A : Type} (P : A -> Prop) (BP : A -> A -> Prop).

Variant option_predicate : option A -> Prop :=
	| OP_None : option_predicate None
	| OP_Some : forall a, P a -> option_predicate (Some a).

Definition option_default d (o : option A) :=
	match o with
	| None => d
	| Some x => x
	end.

Variant option_bpredicate : option A -> option A -> Prop :=
	| OBP_None : option_bpredicate None None
	| OBP_Some : forall x y,
		BP x y -> option_bpredicate (Some x) (Some y).

Lemma option_default_map_inv : forall d f (o : option A),
	(o = None -> P d) ->
	(forall x, o = Some x -> P (f x)) ->
	P (option_default d (option_map f o)).
Proof.
	intros d f o Hd Hf.
	{	destruct o; simpl.
	+	apply Hf.
		reflexivity.
	+	apply Hd.
		reflexivity.
	}
Qed.
End Option.

(*Section List.

Context {A : Type} (P : A -> Prop).

Fixpoint last_opt (l : list A) : option A :=
	match l with
	| [] => None
	| [a] => Some a
	| x :: tl => last_opt tl
	end.

Definition ends_pred l := option_predicate P (last_opt l).

End List.*)
