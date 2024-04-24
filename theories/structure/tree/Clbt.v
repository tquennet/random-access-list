Require Import Program Arith Lists.List.
Require Import NumRep.numerical.binary.BinNat.
Import ListNotations.

Open Scope type_scope.

Section CLBT.

Context {A : Type}.

Inductive t :=
	| Leaf : A -> t
	| Node : t -> t -> t.

Inductive is_valid : nat -> t -> Prop :=
	| valid_Leaf : forall a : A, is_valid 0 (Leaf a)
	| valid_Node : forall {n : nat} (l r : t),
		is_valid n l -> is_valid n r ->
		is_valid (S n) (Node l r).

Definition singleton (a : A) : t := Leaf a.
Lemma singleton_valid : forall a : A, is_valid 0 (singleton a).
Proof.
	intro a.
	apply valid_Leaf.
Qed.

Fixpoint size t : nat :=
	match t with
	| Leaf _ => 1
	| Node l r => size l + size r
	end.

Lemma valid_size : forall n t, is_valid n t -> size t = 2 ^ n.
Proof.
	intros n t H.
	{	induction H as [|n l r _ HRl _ HRr].
	+	reflexivity.
	+	simpl.
		rewrite HRl, HRr, <- plus_n_O.
		reflexivity.
	}
Qed.

Definition merge (l r : t) : t := Node l r.
Lemma merge_valid : forall {n : nat} (l r : t),
	is_valid n l -> is_valid n r -> is_valid (S n) (merge l r).
Proof.
	intros n l r Hl Hr.
	apply valid_Node; assumption.
Qed.

Fixpoint head t : A :=
	match t with
	| Leaf a => a
	| Node _ r => head r
	end.

Definition left t :=
	match t with
	| Leaf _ => t
	| Node l _ => l
	end.
Definition right t :=
	match t with
	| Leaf _ => t
	| Node _ r => r
	end.

Lemma left_valid : forall {n : nat} t,
	is_valid (S n) t -> is_valid n (left t).
Proof.
	intros n t H.
	inversion_clear H.
	assumption.
Qed.

Lemma right_valid : forall {n : nat} t,
	is_valid (S n) t -> is_valid n (right t).
Proof.
	intros n t H.
	inversion_clear H.
	assumption.
Qed.

Fixpoint update t dn a :=
	match t, dn with
	| Leaf _, [] => Leaf a
	| Node l r, 0 :: tdn => Node l (update r tdn a)
	| Node l r, 1 :: tdn => Node (update l tdn a) r
	| _, _ => t
	end.

Fixpoint lookup t dn :=
	match t, dn with
	| Leaf a, _ => a
	| _, [] => head t
	| Node l r, 0 :: tdn => lookup r tdn
	| Node l r, 1 :: tdn => lookup l tdn
	end.

Lemma update_valid : forall n t a,
		is_valid (length n) t ->
		is_valid (length n) (update t n a).
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn]; simpl;
			intros t a Ht; inversion_clear Ht; simpl.
	+	apply valid_Leaf.
	+	apply (HR _ a) in H0.
		apply valid_Node; assumption.
	+	apply (HR _ a) in H.
		apply valid_Node; assumption.
	}
Qed.

Lemma lookup_update_eq : forall n t a,
		is_valid (length n) t ->
		lookup (update t n a) n = a.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn]; simpl;
			intros t a Ht; inversion_clear Ht; simpl.
	+	reflexivity.
	+	apply HR.
		assumption.
	+	apply HR.
		assumption.
	}
Qed.
Lemma lookup_update_neq : forall n m t a,
		(length n) = (length m) -> n <> m ->
		is_valid (length n) t ->
		lookup (update t n a) m = lookup t m.
Proof.
	intro n.
	{	induction n as [|bn tn HR]; [|destruct bn];	intros m t a Hlen Hneq Ht;
			(destruct m as [|bm tm]; [|destruct bm]); simpl;
			inversion_clear Ht; simpl in *.
	+	contradiction.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	apply eq_add_S in Hlen.
		assert (tn <> tm) by (intro Ha; rewrite Ha in Hneq; apply Hneq; reflexivity).
		apply HR; assumption.
	+	reflexivity.
	+	reflexivity.
	+	reflexivity.
	+	apply eq_add_S in Hlen.
		assert (tn <> tm) by (intro Ha; rewrite Ha in Hneq; apply Hneq; reflexivity).
		apply HR; assumption.
	}
Qed.

Inductive dt :=
	| DRoot : dt
	| DLeft : dt -> t -> dt
	| DRight : t -> dt -> dt.

Inductive is_valid_d : nat -> nat -> dt -> Prop :=
	| valid_DRoot : forall (n : nat), is_valid_d n n DRoot
	| valid_DLeft : forall (d n : nat) dt t,
		is_valid_d d (S n) dt -> is_valid n t ->
		is_valid_d d n (DLeft dt t)
	| valid_DRight : forall (d n : nat) dt t,
		is_valid n t -> is_valid_d d (S n) dt ->
		is_valid_d d n (DRight t dt).

Definition zip := t * dt.
Definition make_zip t : zip := (t, DRoot).

Definition is_valid_zip (d n : nat) zip :=
	is_valid n (fst zip) /\ is_valid_d d n (snd zip).

Lemma make_zip_valid : forall t n,
		is_valid n t -> is_valid_zip n n (make_zip t).
Proof.
	intros t n H.
	split; [assumption| apply valid_DRoot].
Qed.


Fixpoint dtrace dt :=
	match dt with
	| DRoot => []
	| DLeft dt _ => 0 :: (dtrace dt)
	| DRight _ dt => 1 :: (dtrace dt)
	end.

Definition down_left '(t, dt) :=
	match t with
	| Leaf _ => (t, dt)
	| Node l r => (l, DLeft dt r)
	end.

Lemma down_left_valid : forall zip {d n : nat},
	is_valid_zip d (S n) zip -> is_valid_zip d n (down_left zip).
Proof.
	intros zip d n H.
	destruct zip as [t dt].
	destruct H as [Ht Hdt]; simpl in *.
	inversion_clear Ht.
	{	split.
	+	assumption.
	+	apply valid_DLeft; assumption.
	}
Qed.

Definition down_right '(t, dt) :=
	match t with
	| Leaf _ => (t, dt)
	| Node l r => (r, DRight l dt)
	end.

Lemma down_right_valid : forall zip {d n : nat},
	is_valid_zip d (S n) zip -> is_valid_zip d n (down_right zip).
Proof.
	intros zip d n H.
	destruct zip as [t dt].
	destruct H as [Ht Hdt]; simpl in *.
	inversion_clear Ht.
	{	split.
	+	assumption.
	+	apply valid_DRight; assumption.
	}
Qed.

Definition up '(t, dt) :=
	match dt with
	| DRoot => (t, dt)
	| DLeft dt r => (Node t r, dt)
	| DRight l dt => (Node l t, dt)
	end.

Fixpoint plug t dt :=
	match dt with
	| DRoot => t
	| DLeft dt r => plug (Node t r) dt
	| DRight l dt => plug (Node l t) dt
	end.

Lemma plug_valid : forall dt t n d,
		is_valid d t -> is_valid_d n d dt ->
		is_valid n (plug t dt).
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

Fixpoint open zip dn :=
	match dn with
	| [] => zip
	| 0 :: tdn => open (down_left zip) tdn
	| 1 :: tdn => open (down_right zip) tdn
	end.

Lemma open_valid : forall dn zip d,
		is_valid_zip d (length dn) zip ->
		is_valid_zip d 0 (open zip dn).
Proof.
	intro dn.
	{	induction dn as [|b tdn HR]; intros zip d H; [|destruct b]; simpl.
	+	assumption.
	+	apply HR.
		apply down_left_valid.
		assumption.
	+	apply HR.
		apply down_right_valid.
		assumption.
	}
Qed.

Lemma open_trace : forall dn d n zip,
		is_valid_zip d n zip -> (length dn) <= n ->
		dtrace (snd (open zip dn)) = rev_append dn (dtrace (snd zip)).
Proof.
	intro dn.
	{	induction dn as [|b tn HR]; intros d n zip Hz Hdn; [|destruct b]; simpl in *.
	+	reflexivity.
	+	destruct n; [apply Nat.nle_succ_0 in Hdn; contradiction|].
		apply down_left_valid in Hz as He.
		apply HR in He; [|apply le_S_n; assumption].
		rewrite He.
		unfold down_right.
		destruct zip as [t dt], Hz as [Ht Hdt]; simpl in *.
		inversion_clear Ht.
		reflexivity.
	+	destruct n; [apply Nat.nle_succ_0 in Hdn; contradiction|].
		apply down_right_valid in Hz as He.
		apply HR in He; [|apply le_S_n; assumption].
		rewrite He.
		unfold down_right.
		destruct zip as [t dt], Hz as [Ht Hdt]; simpl in *.
		inversion_clear Ht.
		reflexivity.
	}
Qed.

End CLBT.
