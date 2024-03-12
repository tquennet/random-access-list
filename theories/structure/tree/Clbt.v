Require Import Program Arith Lists.List.
Require Import NumRep.numerical.binary.BinNat.
Import ListNotations.

Section CLBT.

Context {A : Type}.

Inductive CLBT : Type :=
	| Leaf : A -> CLBT
	| Node : CLBT -> CLBT -> CLBT.

Inductive valid_CLBT : nat -> CLBT -> Prop :=
	| valid_Leaf : forall a : A, valid_CLBT 0 (Leaf a)
	| valid_Node : forall {n : nat} (l r : CLBT),
		valid_CLBT n l -> valid_CLBT n r ->
		valid_CLBT (S n) (Node l r).

Definition singleton (a : A) : CLBT := Leaf a.
Lemma singleton_valid : forall a : A, valid_CLBT 0 (singleton a).
Proof.
	intro a.
	apply valid_Leaf.
Qed.

Definition CLBT_merge (l r : CLBT) : CLBT := Node l r.
Lemma CLBT_merge_valid : forall {n : nat} (l r : CLBT),
	valid_CLBT n l -> valid_CLBT n r -> valid_CLBT (S n) (CLBT_merge l r).
Proof.
	intros n l r Hl Hr.
	apply valid_Node; assumption.
Qed.

Fixpoint CLBT_head (t : CLBT) : A :=
	match t with
	| Leaf a => a
	| Node _ r => CLBT_head r
	end.

Definition CLBT_right (t : CLBT) : CLBT :=
	match t with
	| Node l r => r
	| _ => t
	end.

Lemma CLBT_right_valid : forall {n : nat} (t : CLBT),
	valid_CLBT (S n) t -> valid_CLBT n (CLBT_right t).
Proof.
	intros n t H.
	inversion_clear H.
	assumption.
Qed.

Definition CLBT_left (t : CLBT) : CLBT :=
	match t with
	| Node l r => l
	| _ => t
	end.

Lemma CLBT_left_valid : forall {n : nat} (t : CLBT),
	valid_CLBT (S n) t -> valid_CLBT n (CLBT_left t).
Proof.
	intros n t H.
	inversion_clear H.
	assumption.
Qed.

Fixpoint CLBT_lookup (t : CLBT) (n : list Bit) : A :=
	match t with
	| Leaf a => a
	| Node l r =>
		match n with
		| [] => CLBT_lookup r []
		| 0 :: tn => CLBT_lookup r tn
		| 1 :: tn => CLBT_lookup l tn
		end
	end.

Fixpoint CLBT_update (t : CLBT) (n : list Bit) (a : A) : CLBT :=
	match t with
	| Leaf a => Leaf a
	| Node l r =>
		match n with
		| [] => Node l (CLBT_update r [] a)
		| 0 :: tn => Node l (CLBT_update r tn a)
		| 1 :: tn => Node r (CLBT_update l tn a)
		end
	end.

Lemma CLBT_update_valid : forall (t : CLBT) (n : list Bit) (a : A),
	valid_CLBT (length n) t -> valid_CLBT (length n) (CLBT_update t n a).
Proof.
	intro t.
	{	induction t as [b | l HR1 r HR2]; intros n a H.
	+	inversion_clear H.
		apply valid_Leaf.
	+	{	destruct n as [|bit t]; inversion_clear H.
		+	{	destruct bit.
			+	{	apply valid_Node.
				+	assumption.
				+	apply HR2.
					assumption.
				}
			+	{	apply valid_Node.
				+	assumption.
				+	apply HR1.
					assumption.
				}
			}
		}
	}
Qed.

End CLBT.