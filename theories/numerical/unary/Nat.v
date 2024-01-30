
Declare Scope unary_nat_scope.
Open Scope unary_nat_scope.

Inductive Nat :=
	| Ze : Nat
	| Su : Nat -> Nat.
	
Notation "0" := Ze : unary_nat_scope.

Lemma O_Su : forall (n : Nat), 0 <> Su n.
Proof.
	discriminate.
Qed.

Definition pre (n : Nat) :=
	match n with
	| 0 => 0
	| Su m => m
	end.

Lemma pre_su_n_eq_n : forall n : Nat, pre (Su n) = n.
Proof.
	reflexivity.
Qed.

Module add_tail.

	Fixpoint add n m :=
		match n with
		| 0 => m
		| Su n => add n (Su m)	
		end.


	Lemma add_sun_m_eq_add_n_sum : forall (n m : Nat), add (Su n) m = add n (Su m).
	Proof.
		reflexivity.
	Qed.

	Lemma add_su_n_m_eq_su_add : forall (n m : Nat), add (Su n) m = Su (add n m).
	Proof.
		intros n.
		induction n.
		reflexivity.
		intros m.
		rewrite add_sun_m_eq_add_n_sum.
		rewrite (IHn (Su m)).
		reflexivity.
	Qed.
		
End add_tail.

Module add_stack.
	
	Fixpoint add n m :=
		match n with
		| 0 => m
		| Su n => Su (add n  m)
		end.
	
	Lemma add_su_n_m_eq_su_add : forall (n m : Nat), add (Su n) m = Su (add n m).
	Proof.
		reflexivity.
	Qed.

End add_stack.


Theorem add_tail_eq_stack : forall (n m : Nat), add_tail.add n m = add_stack.add n m.
Proof.
	intros n m.
	induction n.
	reflexivity.
	rewrite (add_tail.add_su_n_m_eq_su_add n m); rewrite (add_stack.add_su_n_m_eq_su_add).
	rewrite IHn.
	reflexivity.
Qed.

Include add_tail.

Notation "n + m" := (add n m) : unary_nat_scope.
