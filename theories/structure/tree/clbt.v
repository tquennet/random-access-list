Require Import Program Arith.

Section CLBT.

	Context {A : Type}.

	Inductive CLBT : nat -> Type :=
	| Leaf : A -> CLBT 0
	| Node : forall n : nat, CLBT n -> CLBT n -> CLBT (S n).

	(*Inductive CLBTree : Type :=
	| Leaf : A -> CLBTree
	| Node : CLBTree -> CLBTree -> CLBTree.

	Inductive valid_CLBTree : nat -> CLBTree -> Prop : Type :=
	| valid_Leaf : forall a : A, valid_CLBTree 0 (Leaf a)
	| valid_Node : forall (n : nat) (l r : CLBTree),
		valid_CLBTree n l -> valid_CLBTree n r ->
		valid_CLBTree (S n) (Node l r).

	Definition VCLBT n := {t : CLBTree | valid_CLBTree n t}.*)

	Definition CLBT_size {n : nat} (t : CLBT n) := 2 ^ n.

	Program Definition singleton (a : A) : CLBT 0 := Leaf a.

	Program Fixpoint CLBT_merge {n : nat} (l r : CLBT n) :
		CLBT (S n) := Node n l r.

	Fixpoint CLBT_head {n : nat} (l : CLBT n) : A :=
	match l with
	| Leaf a => a
	| Node _ _ r => CLBT_head r
	end.

	Definition CLBT_break {n : nat} (clbt : CLBT (S n))
			: (CLBT n * CLBT n).
		inversion clbt as [|m l r].
		exact (l, r).
	Defined.

	Local Lemma n_sub_m_lt_m : forall m n, n < 2 * m -> n - m < m.
	Proof.
		intros m n H.
		{	induction m as [| m HR].
		+	apply Nat.nlt_0_r in H.
			contradiction.
		+	rewrite Nat.lt_succ_r.
			rewrite Nat.le_sub_le_add_r.
			rewrite <- Nat.lt_succ_r, <- Nat.add_succ_l.
			{	assert (HD : 2 * S m = S m + S m).
			+	unfold mult.
				rewrite Nat.add_0_r.
				reflexivity.
			+	rewrite <- HD.
				assumption.
			}
		}
	Qed.

	Section CLBT_lookup.

		Program Fixpoint CLBT_lookup (d : nat) (n : nat | n < 2 ^ d)
			(clbt : CLBT d) {measure d} : A :=
		match clbt with
		| Leaf a => a
		| Node m l r => let half := 2 ^ (pred d) in
			match n <? half with
			| true => CLBT_lookup m n l
			| false => CLBT_lookup m (n - half) r
			end
		end.
		Obligation 1.
		Proof.
			rename Heq_anonymous into Hlt.
			simpl in Hlt.
			apply eq_sym in Hlt.
			rewrite Nat.ltb_lt in Hlt.
			exact Hlt.
		Qed.
		Obligation 3.
		Proof.
			simpl.
			apply n_sub_m_lt_m.
			assumption.			
		Qed.
		

	End CLBT_lookup.

	Section CLBT_update.

		Program Fixpoint CLBT_update (d : nat) (n : nat | n < 2 ^ d)
			(clbt : CLBT d) (a : A) {measure d} : CLBT d :=
		match clbt with
		| Leaf _ => Leaf a
		| Node m l r => let half := 2 ^ (pred d) in
			match n <? half with
			| true => Node m (CLBT_update m n l a) r
			| false => Node m l (CLBT_update m (n - half) r a)
			end
		end.
		Obligation 1.
		Proof.
			rename Heq_anonymous into Hlt.
			simpl in Hlt.
			apply eq_sym in Hlt.
			rewrite Nat.ltb_lt in Hlt.
			exact Hlt.
		Qed.
		Obligation 3.
		Proof.
			simpl.
			apply n_sub_m_lt_m.
			assumption.	
		Qed.

	End CLBT_update.

End CLBT.