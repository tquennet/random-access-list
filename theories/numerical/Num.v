

Inductive Num (A : Type) :=
| Ob : Num A
| snoc (n : Num A)(a : A) : Num A.

Arguments Ob {A}.
Arguments snoc {A} n a.

Fixpoint length {A}(n : Num A): nat :=
  match n with
  | Ob => O
  | snoc n _ => S (length n)
  end.

Section mapi.

Context {A B : Type} (f: nat -> A -> B).

Fixpoint mapi_aux (i : nat) (n: Num A) : Num B :=
  match n with
  | Ob => Ob
  | snoc n a => snoc (mapi_aux (S i) n) (f i a)
  end.

Definition mapi (n: Num A): Num B := mapi_aux 0 n.

Lemma mapi_length : forall (n: Num A), length (mapi n) = length n.
Admitted.

End mapi.

Record Monoid (S : Type) : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

Arguments monoid_unit {S} m.
Arguments monoid_plus {S} m m2.

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

Fixpoint foldM {M} (Mon : Monoid M)(n: Num M): M :=
  match n with
  | Ob => monoid_unit Mon
  | snoc n b => monoid_plus Mon (foldM Mon n) b
  end.

Definition foldMap {A M}(Mon : Monoid M)(f: nat -> A -> M) (n: Num A): M := foldM Mon (mapi f n).

Section fold.

Context {A B : Type} (f : B -> A -> B).
Let f' := (fun (_ : nat) a b => f b a).

Definition foldl (b: B) (n: Num A) := foldMap Monoid_endol f' n b.
Definition foldr (b: B) (n: Num A) := foldMap Monoid_endor f' n b.

Lemma fold_snoc : forall b bn tn, foldr b (snoc tn bn) = f (foldr b tn) bn.
Proof.
	intros b bn tn.
	unfold foldr, foldMap.
	simpl.
	assert (forall k, mapi_aux f' (S k) tn = mapi_aux f' k tn) by
		(induction tn as [|tn HR b0]; intro k; [|simpl; rewrite HR]; reflexivity).
	rewrite H.
	reflexivity.
Qed.

End fold.

Definition foldir  {A B : Type} (f : nat -> B -> A -> B) (b: B)(n: Num A): B :=
  foldMap Monoid_endor (fun n a b => f n b a) n b.

Definition Num_lift {A} (P : nat -> A -> Prop)(n: Num A): Prop :=
  foldMap Monoid_Prop P n.

Fixpoint app {A} (m n : Num A): Num A :=
  match n with
  | Ob => m
  | snoc n a => snoc (app m n) a
  end.

Fixpoint plug {A} (snoc : Num A -> A -> Num A) (n: Num A)(ctxt: list A): Num A :=
  match ctxt with
  | nil => n
  | cons b ctxt => plug snoc (snoc n b) ctxt
  end.
