
Require Import Lists.List.
Import ListNotations.

Section Option.

Context {A : Type} (P : A -> Prop).

Inductive option_predicate : option A -> Prop :=
	| OP_None : option_predicate None
	| OP_Some : forall a, P a -> option_predicate (Some a).

End Option.

Section List.

Context {A : Type} (P : A -> Prop).

Fixpoint last_opt (l : list A) : option A :=
	match l with
	| [] => None
	| [a] => Some a
	| x :: tl => last_opt tl
	end.

Definition ends_pred l := option_predicate P (last_opt l).

End List.
