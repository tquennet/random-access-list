Require Import utils.Utils Lists.List.

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

Section to_list.

Context {A : Type}.

Definition to_list : Num A -> list A := foldr (fun l x => x :: l) nil.

Lemma to_list_snoc : forall l b, to_list (snoc l b) = b :: to_list l.
Proof.
	intros l b.
	unfold to_list.
	rewrite fold_snoc.
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
End to_list.

(*
Section app.

Context {A : Type}.

Lemma app_Ob_l : forall (n : Num A), app Ob n = n.
Proof.
	intros n.
	{	induction n as [|tn HR bn]; simpl.
	+	reflexivity.
	+	rewrite HR.
		reflexivity.
	}
Qed.


Lemma plug_app : forall (n m : Num A) dn, plug (app n m) dn = app n (plug m dn).
Proof.
	intros n m dn.
	revert n m.
	{	induction dn as [|bn tn HR]; intros n m; simpl.
	+	reflexivity.
	+	cbn [plug Num.plug rev].
		apply (HR n (snoc m bn)).
	}
Qed.

Lemma plug_plug_app : forall (n : Num A) dn dm, plug (plug n dn) dm = plug n (dn ++ dm).
Proof.
	intros n dn dm.
	revert n dn.
	{	induction dm as [|bm tm HR]; simpl; intros n dn.
	+	rewrite app_nil_r.
		reflexivity.
	+	cbn [plug gplug].
		rewrite (HR .
	}
Qed.
Lemma rev_app : forall (dn dm : list A), app (rev dn) (rev dm) = rev (dn ++ dm).
Proof.
	intros dn.
	{	induction dn as [|bn tn HR]; intro dm; simpl.
	+	rewrite app_Ob_l.
		reflexivity.
	+	cbn [rev gplug].
		rewrite <- plug_app.
		simpl.
	}
Qed.

End app.*)
