Require Import utils.Utils.

Reserved Notation "m >>= f" (at level 50, left associativity).
Reserved Notation "↑ P" (at level 0, right associativity).

Class Monad :=
{
	m : Type -> Type;
	ret : forall {A : Type}, A -> m A;
	bind : forall {A B : Type}, (A -> m B) -> m A -> m B
		where "m >>= f" := (bind f m);
	left_comp : forall {A B : Type} (a : A) (f : A -> m B), ret a >>= f = f a;
	right_comp : forall {A : Type} (x : m A), x >>= ret = x;
	assoc : forall {A B C : Type} (x : m A) (f : A -> m B) (g : B -> m C),
		x >>= f >>= g = x >>= (fun a => f a >>= g)
}.

Notation "m >>= f" := (bind f m).

Class FailMonad :=
{
	monad :: Monad;
	fail : forall {A : Type}, m A;
	bind_fail : forall {A B : Type} (f : A -> m B), fail >>= f = fail;
	lift : forall {A : Type}, (A -> Prop) -> (m A -> Prop) where "↑ P" := (lift P);
	lift_fail : forall {A : Type} (P : A -> Prop), ↑P (fail);
	lift_ret : forall {A : Type} (P : A -> Prop) (a : A), P a <-> ↑P (ret a);
	lift_bind : forall {A B : Type} (P : B -> Prop) (f : A -> m B) (x : m A),
		↑(fun y => ↑P (f y)) x -> ↑P (x >>= f)
}.

Notation "↑ P" := (lift P).

#[refine] Instance OptionMonad : Monad :=
{
	m := option;
	ret := @Some;
	bind := @option_join;
}.
+	reflexivity.
+	destruct x; reflexivity.
+	destruct x; reflexivity.
Defined.

#[refine] Instance OptionFailMonad : FailMonad :=
{
	monad := OptionMonad;
	lift := @option_predicate;
	fail := @None;
}.
+	reflexivity.
+	intros A P.
	apply OP_None.
+	intros A P a.
	{	split; intro H.
	+	apply OP_Some.
		assumption.
	+	inversion_clear H.
		assumption.
	}
+	intros A B P f x H.
	destruct x; [inversion_clear H; assumption|apply OP_None].
Defined.
