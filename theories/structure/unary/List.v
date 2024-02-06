Require Import NumRep.numerical.unary.Nat.

Open Scope unary_nat_scope.
Declare Scope unary_list_scope.
Open Scope unary_list_scope.

Inductive List (A : Type) : Type :=
| Nil : List A
| Cons : A -> List A -> List A.
	
Notation "[]" := (Nil _) : unary_list_scope.
Notation "h :: t" := (Cons _ h t) : unary_list_scope.
Notation "[ a ]" := (a :: Nil _) : unary_nat_scope.
	
Fixpoint length {A : Type} (l : List A) : Nat :=
	match l with
	| [] => 0
	| _ :: t => Su (length t)
	end.

Reserved Notation "# l" (at level 25, no associativity).
Reserved Notation "l @ r" (at level 60, right associativity).
Notation "# l" := (length l) : unary_list_scope.

Section List.
	
	Context {A : Type}.

	Notation List := (List A).

	Definition tail (l : List) :=
		match l with
		| [] => []
		| _ :: t => t
		end.
	
	Fixpoint append left right : List :=
	match left with
	| [] => right
	| x :: tleft => x :: (append tleft right)
	end.

	Notation "l @ r" := (append l r) : unary_list_scope.

	Lemma append_trans : forall l1 l2 l3 : List,
		(l1 @ l2) @ l3 = l1 @ (l2 @ l3).
	Proof.
		intros l1 l2 l3.
		{	induction l1 as [| a t1 H].
		+	reflexivity.
		+	simpl.
			rewrite H.
			reflexivity.
		}
	Qed.

	Fixpoint rev_append l r : List :=
	match l with
	| [] => r
	| x :: t => rev_append t (x :: r)
	end.

	Definition rev l := rev_append l [].

	Lemma rev_append_append_r : forall l r : List,
		rev_append l r = (rev_append l []) @ r.
	Proof.
		intro l.
		{	induction l as [| x t H].
		+	reflexivity.
		+	intro r.
			simpl.
			rewrite (H (x :: r)), (H [x]).
			rewrite append_trans.
			reflexivity.
		}
	Qed.

	Lemma rev_append_append_l : forall l1 l2 l3 : List,
		rev_append (l1 @ l2) l3 = rev_append l2 (rev_append l1 l3).
	Proof.
		intros l1.
		{	induction l1 as [| x t H].
		+	reflexivity.
		+	simpl.
			intros l2 l3.
			rewrite H.
			reflexivity.
		}
	Qed.

	Lemma rev_inv : forall l : List, rev (rev l) = l.
	Proof.
		intro l.
		{	induction l as [| x t H].
		+	reflexivity.
		+	compute; fold rev_append; unfold rev in H.
			rewrite (rev_append_append_r t).
			rewrite (rev_append_append_l).
			rewrite H.
			reflexivity.
		}
	Qed.

	Lemma append_l_r_eq_rev_append_rev_l_r : forall l r : List,
		l @ r = rev_append (rev l) r.
	Proof.
		intros l r.
		rewrite rev_append_append_r.
		replace (rev_append (rev l) []) with (rev (rev l)) by reflexivity.
		rewrite rev_inv.
		reflexivity.
	Qed.

End List.

Notation "l @ r" := (append l r) : unary_list_scope.