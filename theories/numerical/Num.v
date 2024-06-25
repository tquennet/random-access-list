Require Import utils.Utils Lists.List.

(********************************************************************************)
(** * Generic representation of dense numerical systems

** Constructor:

- [Num A] == the type of dense numerical systems of base [A]

** Iterators:

- [mapi f i n] == applies [f] across the numerical representation [n]
                  starting from a coefficient weighted [i]
- [foldM m n] == fold the elements of the monoid [m] over the
                 numerical representation [n]
- [foldMap m f i n] == combination of [mapi] and [foldM]

** Predicates:

- [Num_lift P i n] == asserts that [P] holds for every digit of the
                      numerical representation [n] starting from a
                      coefficient weighted [i]
*)
(********************************************************************************)

Inductive Num (A : Type) :=
| Ob : Num A
| snoc (n : Num A)(a : A) : Num A.

Definition t := Num.

Arguments Ob {A}.
Arguments snoc {A} n a.

Fixpoint gplug {A} (snoc : Num A -> A -> Num A) (n: Num A)(ctxt: list A): Num A :=
  match ctxt with
  | nil => n
  | cons b ctxt => gplug snoc (snoc n b) ctxt
  end.
Definition plug {A} : Num A -> list A -> Num A := gplug snoc.
Notation rev := (plug Ob).

Fixpoint length {A}(n : Num A): nat :=
  match n with
  | Ob => O
  | snoc n _ => S (length n)
  end.

Lemma length_0_iff_Ob {A} : forall (n : Num A), length n = O <-> n = Ob.
Proof.
	intro n.
	{	split; intro H.
	+	destruct n; [reflexivity|discriminate].
	+	rewrite H; reflexivity.
	}
Qed.
Section mapi.

Context {A B : Type} (f: nat -> A -> B).

Fixpoint mapi (i : nat) (n: Num A) : Num B :=
  match n with
  | Ob => Ob
  | snoc n a => snoc (mapi (S i) n) (f i a)
  end.

Lemma mapi_length : forall (i : nat) (n: Num A), length (mapi i n) = length n.
Proof.
	intros i n.
	revert i.
	{	induction n as [|tn HR bn]; intro k; simpl.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	}
Qed.

End mapi.

Section map.

Context {A B : Type} (f: A -> B).

Let f' : nat -> A -> B := (fun _ => f).

Definition map (n : Num A) : Num B := mapi f' O n.

Lemma map_snoc : forall n b, map (snoc n b) = snoc (map n) (f b).
Proof.
	intros n b.
	unfold map.
	cbn [mapi].
	enough (H : forall k, mapi f' (S k) n = mapi f' k n) by (rewrite H; reflexivity).
	{	induction n as [|tn HR bn]; intro k; simpl.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	}
Qed.

End map.

Fixpoint foldM {M} (m : Monoid M)(n: Num M): M :=
  match n with
  | Ob => m.(monoid_unit)
  | snoc n b => m.(monoid_plus) (foldM m n) b
  end.

Definition foldMap {A M}(Mon : Monoid M)(f: nat -> A -> M) (i : nat) (n: Num A): M :=
	foldM Mon (mapi f i n).

Section fold.

Context {A B : Type} (f : B -> A -> B).
Let f' := (fun (_ : nat) a b => f b a).

Definition foldl (b: B) (n: Num A) := foldMap Monoid_endol f' 0 n b.
Definition foldr (b: B) (n: Num A) := foldMap Monoid_endor f' 0 n b.

Lemma foldr_snoc : forall b bn tn, foldr b (snoc tn bn) = f (foldr b tn) bn.
Proof.
	intros b bn tn.
	unfold foldr, foldMap.
	simpl.
	enough (H : forall k, mapi f' (S k) tn = mapi f' k tn) by (rewrite H; reflexivity).
	{	induction tn as [|tn HR b0]; intro k; simpl.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	}
Qed.

End fold.

Definition foldir  {A B : Type} (f : nat -> B -> A -> B) (i : nat) (b: B)(n: Num A): B :=
  foldMap Monoid_endor (fun n a b => f n b a) i n b.


Definition Num_lift {A} (P : nat -> A -> Prop) (i : nat) (n: Num A): Prop :=
  foldMap Monoid_Prop P i n.

Fixpoint app {A} (m n : Num A): Num A :=
  match n with
  | Ob => m
  | snoc n a => snoc (app m n) a
  end.

Section to_list.

Context {A : Type}.

Definition to_list : Num A -> list A := foldr (fun l x => x :: l) nil.

Lemma to_list_snoc : forall l b, to_list (snoc l b) = b :: to_list l.
Proof.
	intros l b.
	unfold to_list.
	rewrite foldr_snoc.
	reflexivity.
Qed.

Lemma to_list_plug : forall (l : Num A) dl, to_list (plug l dl) = rev_append dl (to_list l).
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intro l; simpl.
	+	reflexivity.
	+	cbn [plug gplug].
		rewrite <- to_list_snoc.
		apply HR.
	}
Qed.
Lemma to_list_rev : forall (l : list A), to_list (rev l) = List.rev l.
Proof.
	intro l.
	rewrite to_list_plug, rev_append_rev, app_nil_r.
	reflexivity.
Qed.
Lemma to_list_app : forall (l r : Num A), to_list (app l r) = to_list r ++ to_list l.
Proof.
	intros l r.
	revert l.
	{	induction r as [|tr HR br]; intro l.
	+	reflexivity.
	+	cbn [app].
		rewrite !to_list_snoc, <- app_comm_cons, HR.
		reflexivity.
	}
Qed.


Lemma to_list_inj : forall l r, to_list l = to_list r -> l = r.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; intros r H; destruct r as [|tr br].
	+	reflexivity.
	+	discriminate.
	+	discriminate.
	+	rewrite !to_list_snoc in H.
		inversion H.
		f_equal.
		apply HR.
		assumption.
	}
Qed.

Lemma plug_snoc : forall (dm : list A) m b, plug m (dm ++ (cons b nil)) = snoc (plug m dm) b.
Proof.
	intro dm.
	{	induction dm as [|bm tm HR]; intros m b; simpl.
	+	reflexivity.
	+	cbn [rev gplug].
		rewrite <- HR.
		reflexivity.
	}
Qed.

Lemma rev_snoc : forall (dm : list A) b, rev (dm ++ (cons b nil)) = snoc (rev dm) b.
Proof.
	intros dm b.
	apply plug_snoc.
Qed.

End to_list.
