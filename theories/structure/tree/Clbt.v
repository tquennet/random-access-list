Require Import Program Arith Lists.List.
Require Import NumRep.numerical.binary.BinNat.
Import ListNotations.

Open Scope type_scope.

Section CLBT.

Context {A : Type}.

Inductive CLBT :=
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

Definition CLBT_left (t : CLBT) :=
	match t with
	| Leaf _ => t
	| Node l _ => l
	end.
Definition CLBT_right (t : CLBT) :=
	match t with
	| Leaf _ => t
	| Node _ r => r
	end.

Lemma CLBT_left_valid : forall {n : nat} (t : CLBT),
	valid_CLBT (S n) t -> valid_CLBT n (CLBT_left t).
Proof.
	intros n t H.
	inversion_clear H.
	assumption.
Qed.

Lemma CLBT_right_valid : forall {n : nat} (t : CLBT),
	valid_CLBT (S n) t -> valid_CLBT n (CLBT_right t).
Proof.
	intros n t H.
	inversion_clear H.
	assumption.
Qed.

Section DCLBT.

Inductive DCLBT :=
	| DCLBT_Root : DCLBT
	| DCLBT_Left : DCLBT -> CLBT -> DCLBT
	| DCLBT_Right : CLBT -> DCLBT -> DCLBT.

Inductive valid_DCLBT : nat -> DCLBT -> Prop :=
	| valid_DCLBT_Root : forall (n : nat), valid_DCLBT n DCLBT_Root
	| valid_DCLBT_Left : forall (n : nat) (dt : DCLBT) (t : CLBT),
		valid_DCLBT (S n) dt -> valid_CLBT n t ->
		valid_DCLBT n (DCLBT_Left dt t)
	| valid_DCLBT_Right : forall (n : nat) (dt : DCLBT) (t : CLBT),
		valid_CLBT n t -> valid_DCLBT (S n) dt ->
		valid_DCLBT n (DCLBT_Right t dt).

Definition CLBT_zip := CLBT * DCLBT.
Definition CLBT_make_zip t : CLBT_zip := (t, DCLBT_Root).

Definition valid_CLBT_zip (n : nat) '(t, dt) :=
	valid_CLBT n t /\ valid_DCLBT n dt.

Fixpoint DCLBT_trace dt :=
	match dt with
	| DCLBT_Root => []
	| DCLBT_Left dt _ => 1 :: (DCLBT_trace dt)
	| DCLBT_Right _ dt => 0 :: (DCLBT_trace dt)
	end.

Definition CLBT_down_left '(t, dt) :=
	match t with
	| Leaf _ => (t, dt)
	| Node l r => (l, DCLBT_Left dt r)
	end.

Lemma CLBT_down_left_valid : forall (zip : CLBT_zip) {n : nat},
	valid_CLBT_zip (S n) zip -> valid_CLBT_zip n (CLBT_down_left zip).
Proof.
	intros zip n H.
	destruct zip as [t dt].
	destruct H as [Ht Hdt].
	inversion_clear Ht.
	{	split.
	+	assumption.
	+	apply valid_DCLBT_Left; assumption.
	}
Qed.

Definition CLBT_down_right '(t, dt) :=
	match t with
	| Leaf _ => (t, dt)
	| Node l r => (r, DCLBT_Right l dt)
	end.

Lemma CLBT_down_right_valid : forall (zip : CLBT_zip) {n : nat},
	valid_CLBT_zip (S n) zip -> valid_CLBT_zip n (CLBT_down_right zip).
Proof.
	intros zip n H.
	destruct zip as [t dt].
	destruct H as [Ht Hdt].
	inversion_clear Ht.
	{	split.
	+	assumption.
	+	apply valid_DCLBT_Right; assumption.
	}
Qed.

Definition CLBT_up '(t, dt) :=
	match dt with
	| DCLBT_Root => (t, dt)
	| DCLBT_Left dt r => (Node t r, dt)
	| DCLBT_Right l dt => (Node l t, dt)
	end.

Fixpoint CLBT_plug t dt : CLBT :=
	match dt with
	| DCLBT_Root => t
	| DCLBT_Left dt r => CLBT_plug (Node t r) dt
	| DCLBT_Right l dt => CLBT_plug (Node l t) dt
	end.

Fixpoint CLBT_open zip dbn :=
	match dbn with
	| [] => zip
	| 0 :: tdbn => CLBT_open (CLBT_down_right zip) tdbn
	| 1 :: tdbn => CLBT_open (CLBT_down_left zip) tdbn
	end.

End DCLBT.

End CLBT.
