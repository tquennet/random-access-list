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

	Theorem length_cons_succ : forall (l : List) (n : Nat) (x : A),
		n = length l <-> Su n = @length A (x :: l).
	Proof.
		{	split.
		+	intro H; simpl.
			rewrite H; reflexivity.
		+	intro H; simpl in *.
			inversion H; reflexivity.
		}
	Qed.

	Theorem length_tail_pre : forall (l : List) (n : Nat),
		n = length l -> pre n = length (tail l).
	Proof.
		intros l n H.
		{	destruct l; simpl in *; rewrite H.
		+	reflexivity.
		+	rewrite pre_su_n_eq_n.
			reflexivity.
		}
	Qed.

	Theorem tail_pre_length : forall (l : List) (n : Nat)
		(CL : l <> []) (CN : n <> 0),
		length (tail l) = pre n -> n = length l.
	Proof.
		intros l n CL CN H.
		destruct l; destruct n; try contradiction.
		+	simpl in *.
			rewrite H; reflexivity.
	Qed.

	Theorem length_sum_append : forall (l r : List) (n m : Nat),
		n = length l -> m = length r -> n + m = length (append l r).
	Proof.
		intros l r.
		{	induction l; intros n m Hll Hlr.
		+	simpl; rewrite Hlr, Hll.
			reflexivity.
		+	simpl in *.
			rewrite Hll, add_su_n_m_eq_su_add.
			f_equal.
			apply (f_equal pre) in Hll; rewrite pre_su_n_eq_n in Hll.
			specialize (IHl (pre n) m).
			pose (H := IHl Hll Hlr).
			rewrite <- H, Hll.
			reflexivity.
		}
	Qed.

End Nat_List.