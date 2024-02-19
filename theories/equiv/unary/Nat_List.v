Require Import NumRep.numerical.unary.Nat NumRep.structure.unary.List.
Require Import Relations.Relation_Definitions.
Require Import Relations.Relations.

Open Scope unary_nat_scope.
Open Scope unary_list_scope.
Declare Scope unary_equiv_scope.
Open Scope unary_equiv_scope.

Section Nat_List.

	Context {A : Type}.

	Generalizable Variables l r.

	Notation List := (List A).

	Definition list_equiv : equivalence List `(#l = #r) :=
		inverse_image_of_eq _ _ length.
	
	Theorem length_0 : forall (l : List), #l = 0 <-> l = [].
	Proof.
		{	split; intro H.
		+	destruct l; (reflexivity || discriminate).
		+	rewrite H; reflexivity.
		}
	Qed.

	Theorem length_cons_succ : forall (l : List) (x : A),
		Su (#l) = # (x :: l).
	Proof.
		intros l x.
		reflexivity.
	Qed.

	Theorem length_tail_pre : forall (l : List),
		pre (#l) = #(tail l).
	Proof.
		intros l.
		{	destruct l.
		+	reflexivity.
		+	simpl.
			reflexivity.
		}
	Qed.

	Theorem length_sum_append_stack : forall (l r : List),
		(#l) +s (#r) = # (l @ r).
	Proof.
		intros l r.
		{	induction l as [|x t H].
		+	reflexivity.
		+	simpl in *.
			rewrite H.
			reflexivity.
		}
	Qed.

	Theorem length_sum_append_tail : forall (l r : List),
		(#l) +t (#r) = # (rev_append l r).
	Proof.
		intros l.
		{	induction l as [|x t H]; intro r.
		+	reflexivity.
		+	simpl.
			rewrite <- H.
			reflexivity.
		}
	Qed.

End Nat_List.