Require Import utils.Utils.

Inductive Num (A : Type) :=
| Ob : Num A
| snoc (n : Num A)(a : A) : Num A.

Arguments Ob {A}.
Arguments snoc {A} n a.

Fixpoint plug {A} (n: Num A)(ctxt: list A): Num A :=
  match ctxt with
  | nil => n
  | cons b ctxt => plug (snoc n b) ctxt
  end.

Fixpoint length {A}(n : Num A): nat :=
  match n with
  | Ob => O
  | snoc n _ => S (length n)
  end.

Definition mapi {A B} (f: nat -> A -> B)(n: Num A): Num B :=
  let aux := fix rec i n :=
               match n with
               | Ob => Ob
               | snoc n a => snoc (rec (S i) n) (f i a)
               end
  in
  aux 0 n.

Lemma mapi_length : forall {A B} (f: nat -> A -> B)(n: Num A), length (mapi f n) = length n.
Admitted.

Fixpoint foldM {M} (m : Monoid M)(n: Num M): M :=
  match n with
  | Ob => m.(monoid_unit)
  | snoc n b => m.(monoid_plus) (foldM m n) b
  end.

Definition foldMap {A M}(m : Monoid M)(f: nat -> A -> M) (n: Num A): M := foldM m (mapi f n).

Definition foldi {A B} (f : nat -> B -> A -> B)(b: B)(n: Num A): B := foldMap Monoid_endo (fun n a b => f n b a) n b.

Definition Num_lift {A} (P : nat -> A -> Prop)(n: Num A): Prop :=
  foldMap Monoid_Prop P n.

Fixpoint app {A} (m n : Num A): Num A :=
  match n with
  | Ob => m
  | snoc n a => snoc (app m n) a
  end.
