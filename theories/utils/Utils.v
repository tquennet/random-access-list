
Section Option.

Context {A : Type} (P : A -> Prop).

Inductive option_predicate : option A -> Prop :=
	| OP_None : option_predicate None
	| OP_Some : forall a, P a -> option_predicate (Some a).

End Option.