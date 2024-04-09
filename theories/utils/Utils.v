
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

(*Variant option_bpredicate : option A -> option A -> Prop :=
	| OBP_None : option_bpredicate None None
	| OBP_Some : forall x y,
		BP x y -> option_bpredicate (Some x) (Some y).*)

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

Section Options.

Context {A B C : Type}.

Lemma option_map_map : forall (f : B -> C) (g : A -> B) (o : option A),
	  option_map f (option_map g o) = option_map (fun x => f (g x)) o.
Proof.
	intros f g o.
	destruct o; reflexivity.
Qed.

Lemma option_default_map_eq : forall (d1 d2 : B) (f1 f2 : A -> B)
											 (g1 g2 : B -> C) (o : option A),
		g1 d1 = g2 d2 ->
		(forall x, g1 (f1 x) = g2 (f2 x)) ->
		g1 (option_default d1 (option_map f1 o)) = g2 (option_default d2 (option_map f2 o)).
Proof.
	intros d1 d2 f1 f2 g1 g2 o Hd Hgf.
	{	destruct o; simpl.
	+	apply Hgf.
	+	apply Hd.
	}
Qed.
					  

End Options.

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
