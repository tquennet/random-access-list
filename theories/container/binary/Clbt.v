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

Hint Constructors is_valid : core.

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
Proof. intros ? h; induction h; simpl; auto. Qed.

(** [singleton] *)

Definition singleton (a : A) : t := create a 0.

Lemma singleton_valid : forall a, is_valid 0 (singleton a).
Proof. auto using create_valid. Qed.

(** [merge l r] *)

Definition merge (l r : t) : t := Node l r.
Lemma merge_valid : forall {n : nat} (l r : t),
	is_valid n l -> is_valid n r -> is_valid (S n) (merge l r).
Proof. intros *; auto using valid_Node. Qed.

(** [lookup] *)

Fixpoint lookup t dn :=
	match t, dn with
	| Leaf a, [] => Some a
	| Node l _, 0 :: tdn => lookup l tdn
	| Node _ r, 1 :: tdn => lookup r tdn
        | _, _ => (* Impossible *) None
	end.

(** [update] *)


Fixpoint update t dn a :=
	match t, dn with
	| Leaf _, [] => Some (Leaf a)
	| Node l r, 0 :: tdn => option_map (fun l => Node l r) (update l tdn a)
	| Node l r, 1 :: tdn => option_map (fun r => Node l r) (update r tdn a)
	| _, _ => None
	end.

Definition is_valid_idx (n: list Bit) t: Prop :=
  is_valid (length n) t.

Hint Unfold is_valid_idx : core.

Lemma update_valid : forall n t a,
		is_valid_idx n t ->
		option_lift (fun t => is_valid_idx n t) (update t n a).
Admitted.
(*	intro n.
        {
	  induction n as [|[ | ] tn IH];
            intros t a Ht;
            inversion_clear Ht as [|? l r Hl Hr];
            simpl.
          1: apply valid_Leaf.
          all:
	    rewrite lift_map; simpl;
            eapply lift_conseq
              with (P := is_valid_idx tn); auto;
            intros; eauto using valid_Node.
        }
Qed.*)

Lemma update_total: forall n t a,
    is_valid_idx n t ->
    exists t', update t n a = Some t'.
Proof.
  intro n.
  {
    induction n as [| [|] tn IH];
      intros t a Ht;
      inversion_clear Ht as [|? l r Hl Hr];
      simpl; eauto.
    all: edestruct IH as [? ->]; eauto;
      simpl; eauto.
  }
Qed.

(** Equational theory [update]/[lookup] *)

Lemma lookup_update_eq : forall n t a,
		is_valid_idx n t ->
		option_bind (update t n a) (fun t => lookup t n) = Some a.
Proof.
	intro n.
	induction n as [|[|] tn IH];
		intros t a Ht;
    	inversion_clear Ht as [|? l r Hl Hr];
    	simpl; auto.
	all: rewrite bind_map; eauto.
Qed.

Lemma lookup_update_neq : forall n m t a,
		length n = length m -> n <> m ->
		is_valid_idx n t ->
		option_bind (update t n a) (fun t => lookup t m) = lookup t m.
Proof.
	intro n.
	{
          induction n as [|[|] tn IH];
            intros [|[|] tm] t a Hlen Hneq Ht;
            inversion_clear Ht;
            simpl in *;
            try tauto;
            rewrite bind_map; simpl;
            try solve [
                rewrite bind_fail; auto
              | eapply IH; auto;
                congruence 
              | edestruct update_total as [? ->]; auto ].
	}
Qed.

End CLBT.
