Require Import utils.Utils.
Require Export stdpp.base.

Class Monad (M : Type -> Type) :=
{
	ret : MRet M;
	bind : MBind M;
	leftcomp : forall [A B : Type] (a : A) (f : A -> M B), ret A a ≫= f = f a;
	rightcomp : forall [A : Type] (x : M A), x ≫= ret A = x;
	assoc : forall [A B C : Type] (x : M A) (f : A -> M B) (g : B -> M C),
		(x ≫= f) ≫= g = x ≫= (fun a => f a ≫= g);
}.

Reserved Notation "P ◻" (at level 0, no associativity).


Class FailMonad (E : Type) (M : Type -> Type) :=
{
	monad :: Monad M;
	throw : MThrow E M;
	(*bindfail : forall {A B : Type} e (f : A -> M B), bind _ _ f (throw A e) = throw B e;*)
	lift : forall {A : Type}, (A -> Prop) -> (M A -> Prop) where "P ◻" := (lift P);
	liftthrow : forall [A : Type] e (P : A -> Prop), P◻ (throw A e);
	liftret : forall [A : Type] (P : A -> Prop) (a : A), P a <-> P ◻ (ret A a);
	liftbind : forall [A B : Type] (P : A -> Prop) (P' : B -> Prop) (f : A -> M B) (x : M A),
		(forall a, P a -> P'◻ (f a)) -> P◻ x -> P'◻ (bind _ _ f x);
}.

Notation "P ◻" := (lift P).

#[refine] Instance OptionMonad : Monad option :=
{
	ret := @Some;
	bind := @option_join;
}.
+	reflexivity.
+	destruct x; reflexivity.
+	destruct x; reflexivity.
Defined.

#[refine] Instance OptionFailMonad : FailMonad unit option :=
{
	monad := OptionMonad;
	lift := @option_predicate;
	throw := fun A _ => @None A;
}.
(* +	reflexivity.*)
+	intros A P.
	apply OP_None.
+	intros A P a.
	{	split; intro H.
	+	apply OP_Some.
		assumption.
	+	inversion_clear H.
		assumption.
	}
+	intros A B P P' f x H Hx.
	destruct x; [|apply OP_None].
	apply H.
	inversion_clear Hx.
	assumption.
Defined.


Section FailMonadProps.

Context {E : Type} {M : Type -> Type} (failmonad : FailMonad E M).
			
Definition success [A : Type] (x : M A) := exists a, x = ret _ a.

Lemma liftimp : forall [A : Type] (P P' : A -> Prop) (H : forall a, P a -> P' a) (x : M A), P◻ x -> P'◻ x.
Proof.
	intros A P P' H x Hl.
	rewrite <- rightcomp.
	apply (liftbind P); [|assumption].
	intros a Ha.
	rewrite <- liftret.
	apply H.
	assumption.
Qed.
End FailMonadProps.
