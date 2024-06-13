Require Import Program Arith Lists.List.
Require Import NumRep.utils.Utils.
Require Import NumRep.numerical.binary.BinNat.
Import ListNotations.

Open Scope type_scope.

(********************************************************************************)
(** * Complete leaf binary tree

** Constructors:

- [t] == the type of leaf binary tree
- [singleton a] == the tree made of a single element [a]
- [create a h] == the tree of [2^h] copies of [a]

** Predicates:

- [is_valid h t] <=> the tree [t] is complete of height [h]

All the constructors exposed in this module produce valid binary trees
while operations preserve validity.

** Operations:

- [card t] == number of elements (ie., leafs) in [t]
- [merge l r] == merge two valid trees [l] and [r] of height [h] into
  a valid tree of height [h+1]
- [lookup t dn] == lookup the [dn]-th leaf (counted from left to right)
  of [t], with [dn] in MSB-first form
- [update t dn a] == update the [dn]-th element of [t] with [a]

*)
(********************************************************************************)


Section CLBT.

Context {A : Type}.

Inductive t :=
	| Leaf : A -> t
	| Node : t -> t -> t.

(** [is_valid] *)

Inductive is_valid : nat -> t -> Prop :=
	| valid_Leaf : forall a : A, is_valid 0 (Leaf a)
	| valid_Node : forall {n : nat} (l r : t),
		is_valid n l -> is_valid n r ->
		is_valid (S n) (Node l r).

(** [card] *)

Fixpoint card t : nat :=
	match t with
	| Leaf _ => 1
	| Node l r => card l + card r
	end.

Lemma valid_card : forall n t, is_valid n t -> card t = 2 ^ n.
Proof.
	intros n t H.
	{	induction H as [|n l r _ HRl _ HRr].
	+	reflexivity.
	+	simpl.
		rewrite HRl, HRr, <- plus_n_O.
		reflexivity.
	}
Qed.

(** [create] *)

Fixpoint create (a : A)(h: nat) : t := 
  match h with
  | O => Leaf a
  | S n => let t := create a n in Node t t
  end.

Lemma create_valid : forall a h, is_valid h (create a h).
Proof.
	intro a. induction h as [|h IH].
	- apply valid_Leaf.
        - constructor; auto.
Qed.

(** [singleton] *)

Definition singleton (a : A) : t := create a 0.

Lemma singleton_valid : forall a : A, is_valid 0 (singleton a).
Proof. intro; apply create_valid. Qed.

(** [merge l r] *)

Definition merge (l r : t) : t := Node l r.
Lemma merge_valid : forall {n : nat} (l r : t),
	is_valid n l -> is_valid n r -> is_valid (S n) (merge l r).
Proof.
	intros n l r Hl Hr.
	apply valid_Node; assumption.
Qed.

(** [lookup] *)

Fixpoint lookup t dn :=
	match t, dn with
	| Leaf a, [] => Some a
	| Node l _, 0 :: tdn => lookup l tdn
	| Node _ r, 1 :: tdn => lookup r tdn
        | _, _ => (* Impossible *) None
	end.

(* XXX: DELETE
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
*)

(** [update] *)


Fixpoint update t dn a :=
	match t, dn with
	| Leaf _, [] => Some (Leaf a)
	| Node l r, 0 :: tdn => option_map (fun r => Node l r) (update r tdn a)
	| Node l r, 1 :: tdn => option_map (fun l => Node l r) (update l tdn a)
	| _, _ => None
	end.


Lemma update_valid : forall n t a,
		is_valid (length n) t ->
		option_lift (fun t => is_valid (length n) t) (update t n a).
Admitted.
(*
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
*)

(** Equational theory [update]/[lookup] *)

Lemma lookup_update_eq : forall n t a,
		is_valid (length n) t ->
		option_bind (update t n a) (fun t => lookup t n) = Some a.
Admitted.
(*
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
*)

Lemma lookup_update_neq : forall n m t a,
		length n = length m -> n <> m ->
		is_valid (length n) t ->
		option_bind (update t n a) (fun t => lookup t m) = lookup t m.
Admitted.
(*
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
*)

(* XXX: delete 
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
	| DLeft dt _ => 1 :: (dtrace dt)
	| DRight _ dt => 0 :: (dtrace dt)
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
*)
(* XXX: delete?
Fixpoint open zip dn :=
	match dn with
	| [] => zip
	| 0 :: tdn => open (down_right zip) tdn
	| 1 :: tdn => open (down_left zip) tdn
	end.

Lemma open_lookup : forall t dn,
		is_valid (length dn) t ->
		fst (open (make_zip t) dn) = Leaf (lookup t dn).
Proof.
	enough (H : forall t dt dn, is_valid (length dn) t ->
						   fst (open (t, dt) dn) = Leaf (lookup t dn))
		by (intros t dn; apply H).
	intro t.
	{	induction t as [t|l HRl r HRr]; intros dt dn H.
	+	inversion H as [t' Hl Ht'|].
		apply eq_sym, length_zero_iff_nil in Hl.
		rewrite Hl.
		reflexivity.
	+	destruct dn as [|bn tn]; inversion_clear H.
		destruct bn; [apply HRr|apply HRl]; assumption.
	}
Qed.

Lemma open_valid : forall dn zip d,
		is_valid_zip d (length dn) zip ->
		is_valid_zip d 0 (open zip dn).
Proof.
	intro dn.
	{	induction dn as [|b tdn HR]; intros zip d H; [|destruct b]; simpl.
	+	assumption.
	+	apply HR.
		apply down_right_valid.
		assumption.
	+	apply HR.
		apply down_left_valid.
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
		apply down_right_valid in Hz as He.
		apply HR in He; [|apply le_S_n; assumption].
		rewrite He.
		unfold down_right.
		destruct zip as [t dt], Hz as [Ht Hdt]; simpl in *.
		inversion_clear Ht.
		reflexivity.
	+	destruct n; [apply Nat.nle_succ_0 in Hdn; contradiction|].
		apply down_left_valid in Hz as He.
		apply HR in He; [|apply le_S_n; assumption].
		rewrite He.
		unfold down_right.
		destruct zip as [t dt], Hz as [Ht Hdt]; simpl in *.
		inversion_clear Ht.
		reflexivity.
	}
Qed.
*)
End CLBT.
