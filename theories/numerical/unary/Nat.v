
(********************************************************************************)
(*	Notations are defined in unary_nat_scope.									*)
(*	Nat Type == the type of natural numbers.									*)
(*	**	Constructors:															*)
(*	Ze, 0 == the number 0.														*)
(*	 Su n == the successor of n.												*)
(*	**	Binary operators:														*)
(*		  add_tail n m, n +t m == tail recursive addition.						*)
(*	add_stack n m == a, n +s m == stack based addition.							*)
(*	** Lemmes:																	*)
(*	add_tail_su_n_m_eq_su_add == forall n m : Nat, (Su n) +t m = Su (n +t m)	*)
(*			add_tail_eq_stack == forall n m : Nat, n +t m = n +s m				*)
(********************************************************************************)

Declare Scope unary_nat_scope.
Open Scope unary_nat_scope.

Reserved Notation "n '+t' m" (at level 50, left associativity).
Reserved Notation "n '+s' m" (at level 50, left associativity).

Inductive Nat :=
	| Ze : Nat
	| Su : Nat -> Nat.
	
Notation "0" := Ze : unary_nat_scope.

Definition pre (n : Nat) :=
	match n with
	| 0 => 0
	| Su m => m
	end.

Fixpoint add_tail n m :=
	match n with
	| 0 => m
	| Su n => add_tail n (Su m)	
	end.

Notation "n '+t' m" := (add_tail n m) : unary_nat_scope.

Lemma add_tail_su_n_m_eq_su_add : forall (n m : Nat),
	(Su n) +t m = Su (n +t m).
Proof.
	intros n.
	{	induction n as [| x H].
	+	reflexivity.
	+	intros m.
		simpl in *.
		rewrite (H (Su m)).
		reflexivity.
	}
Qed.
	
Fixpoint add_stack n m :=
	match n with
	| 0 => m
	| Su n => Su (add_stack n  m)
	end.

Notation "n '+s' m" := (add_stack n m) : unary_nat_scope.

Lemma add_tail_eq_stack : forall (n m : Nat), n +t m = n +s m.
Proof.
	intros n m.
	{	induction n.
	+	reflexivity.
	+	rewrite (add_tail_su_n_m_eq_su_add n m).
		rewrite IHn.
		reflexivity.
	}
Qed.

