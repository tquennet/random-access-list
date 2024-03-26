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

Inductive valid_DCLBT : nat -> nat -> DCLBT -> Prop :=
	| valid_DCLBT_Root : forall (n : nat), valid_DCLBT n n DCLBT_Root
	| valid_DCLBT_Left : forall (d n : nat) (dt : DCLBT) (t : CLBT),
		valid_DCLBT d (S n) dt -> valid_CLBT n t ->
		valid_DCLBT d n (DCLBT_Left dt t)
	| valid_DCLBT_Right : forall (d n : nat) (dt : DCLBT) (t : CLBT),
		valid_CLBT n t -> valid_DCLBT d (S n) dt ->
		valid_DCLBT d n (DCLBT_Right t dt).

Definition CLBT_zip := CLBT * DCLBT.
Definition CLBT_make_zip t : CLBT_zip := (t, DCLBT_Root).

Definition valid_CLBT_zip (d n : nat) '(t, dt) :=
	valid_CLBT n t /\ valid_DCLBT d n dt.

Lemma CLBT_make_zip_valid : forall t n,
		valid_CLBT n t -> valid_CLBT_zip n n (CLBT_make_zip t).
Proof.
	intros t n H.
	split; [assumption| apply valid_DCLBT_Root].
Qed.


Fixpoint DCLBT_trace dt :=
	match dt with
	| DCLBT_Root => []
	| DCLBT_Left dt _ => 0 :: (DCLBT_trace dt)
	| DCLBT_Right _ dt => 1 :: (DCLBT_trace dt)
	end.

Definition CLBT_down_left '(t, dt) :=
	match t with
	| Leaf _ => (t, dt)
	| Node l r => (l, DCLBT_Left dt r)
	end.

Lemma CLBT_down_left_valid : forall (zip : CLBT_zip) {d n : nat},
	valid_CLBT_zip d (S n) zip -> valid_CLBT_zip d n (CLBT_down_left zip).
Proof.
	intros zip d n H.
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

Lemma CLBT_down_right_valid : forall (zip : CLBT_zip) {d n : nat},
	valid_CLBT_zip d (S n) zip -> valid_CLBT_zip d n (CLBT_down_right zip).
Proof.
	intros zip d n H.
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

Lemma CLBT_plug_valid : forall dt t n d,
		valid_CLBT d t -> valid_DCLBT n d dt ->
		valid_CLBT n (CLBT_plug t dt).
Proof.
	intro dt.
	{	induction dt as [| dt HR r | l dt HR]; intros t n d Ht Hdt;
			inversion_clear Hdt; simpl in *.
	+	assumption.
	+	apply (HR _ _ (S d)); [|assumption].
		apply valid_Node; assumption.
	+	apply (HR _ _ (S d)); [|assumption].
		apply valid_Node; assumption.
	}
Qed.

Fixpoint CLBT_open zip dn :=
	match dn with
	| [] => zip
	| 0 :: tdn => CLBT_open (CLBT_down_left zip) tdn
	| 1 :: tdn => CLBT_open (CLBT_down_right zip) tdn
	end.

Lemma CLBT_open_valid : forall dn zip d,
		valid_CLBT_zip d (length dn) zip ->
		valid_CLBT_zip d 0 (CLBT_open zip dn).
Proof.
	intro dn.
	{	induction dn as [|b tdn HR]; intros zip d H; [|destruct b]; simpl.
	+	assumption.
	+	apply HR.
		apply CLBT_down_left_valid.
		assumption.
	+	apply HR.
		apply CLBT_down_right_valid.
		assumption.
	}
Qed.

Lemma CLBT_open_trace : forall dn d n zip,
		valid_CLBT_zip d n zip ->
		(length dn) <= n ->
		DCLBT_trace (snd (CLBT_open zip dn)) = rev_append dn (DCLBT_trace (snd zip)).
Proof.
	intro dn.
	{	induction dn as [|b tn HR]; intros d n zip Hz Hdn; [|destruct b]; simpl in *.
	+	reflexivity.
	+	destruct n; [apply Nat.nle_succ_0 in Hdn; contradiction|].
		apply CLBT_down_left_valid in Hz as He.
		apply HR in He; [|apply le_S_n; assumption].
		rewrite He.
		unfold CLBT_down_right.
		destruct zip as [t dt], Hz as [Ht Hdt].
		inversion_clear Ht.
		reflexivity.
	+	destruct n; [apply Nat.nle_succ_0 in Hdn; contradiction|].
		apply CLBT_down_right_valid in Hz as He.
		apply HR in He; [|apply le_S_n; assumption].
		rewrite He.
		unfold CLBT_down_right.
		destruct zip as [t dt], Hz as [Ht Hdt].
		inversion_clear Ht.
		reflexivity.
	}
Qed.

End DCLBT.

End CLBT.
