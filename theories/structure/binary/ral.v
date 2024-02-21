Require Import Program Arith.
Require Import NumRep.structure.tree.clbt.
Require Import Lists.List.
Import ListNotations.

Declare Scope RAL_scope.
Open Scope RAL_scope.

Section RAL.

	Context {A : Type}.

	Notation CLBT := (@CLBT A).

	Inductive RAL : nat -> Type :=
	| RAL_Empty : forall {n : nat}, RAL n
	| RAL_cons1 : forall {n : nat}, CLBT n -> RAL (S n) -> RAL n
	| RAL_cons2 : forall {n : nat}, RAL (S n) -> RAL n.

	Notation "[]" := RAL_Empty : RAL_scope.
	Notation "[ clbt ]" := (RAL_cons1 clbt RAL_Empty).
	Notation "clbt :: t" := (RAL_cons1 clbt t).
	Notation ":: t" := (RAL_cons2 t) (at level 60) : RAL_scope.

	Definition VRAL := RAL 0.

	Definition empty : VRAL := RAL_Empty.
	Definition is_empty (l : VRAL) :=
		match l with
		| [] => true
		| _ => false
		end.

	Fixpoint st_length {n : nat} (l : RAL n) :=
		match l with
		| [] => 0
		| ::t => S (st_length t)
		| _ :: t => S (st_length t)
	end.

	Section RAL_cons.
	
		(* {struct l} causes coq typechecker error *)
		Local Program Fixpoint RAL_cons_aux {n : nat} (clbt : CLBT n)
			(l : RAL n) {measure (st_length l)} : RAL n :=
			match l with
			| [] => [ clbt ]
			| ::t => RAL_cons1 clbt t
			| e :: t => @RAL_cons2 n
				(RAL_cons_aux (@CLBT_merge A n e clbt) t)
			end.
		Obligation 6.
		Proof.
			simpl.
			rewrite <- Heq_l.
			apply Nat.lt_succ_diag_r.
		Qed.

		Definition RAL_cons (a : A) (l : VRAL) : VRAL :=
			RAL_cons_aux (singleton a) l.
	
	End RAL_cons.

	Fixpoint RAL_head {n : nat} (l : RAL n) : option A :=
		match l with
		| [] => None
		| :: t => RAL_head t
		| clbt :: _ => Some (CLBT_head clbt)
		end.

	Section RAL_tail.

		Local Program Fixpoint uncons {n : nat}	(l : RAL n)
				{measure (st_length l)}
				: (option (CLBT n) * RAL n) :=
			match l with
			| [] => (None, [])
			| clbt :: t => (Some clbt, :: t)
			| :: t => let (clbt, t) := uncons t in
				match clbt with
				| None => (None, :: t)
				| Some clbt => let (tl, tr) := CLBT_break clbt in
					(Some tr, tl :: t)
				end
			end.
		Obligation 1.
		Proof.
			rewrite <- Heq_l.
			apply Nat.lt_succ_diag_r.
		Qed.

		Program Fixpoint RAL_tail (l : VRAL) : VRAL :=
			let (_, ral) := uncons l in ral.
	
	End RAL_tail.

	Section RAL_lookup.

		Program Fixpoint RAL_lookup (n : nat) (d : nat)
				(l : RAL d) {measure (st_length l)}
				: option A :=
			match l with
			| [] => None
			| :: t => RAL_lookup n (S d) t
			| clbt :: t => let size := 2 ^ d in
				match n <? size with
				| true => Some (CLBT_lookup d n clbt)
				| false => RAL_lookup (n - size) (S d) t
				end
			end.
		Obligation 2.
		Proof.
			simpl.
			rewrite <- Heq_l.
			apply Nat.lt_succ_diag_r.
		Qed.
		Obligation 3.
		Proof.
			rename Heq_anonymous into Hlt.
			apply eq_sym in Hlt.
			rewrite Nat.ltb_lt in Hlt.
			exact Hlt.
		Qed.
		Obligation 6.
		Proof.
			simpl.
			rewrite <- Heq_l.
			apply Nat.lt_succ_diag_r.
		Qed.
	
	End RAL_lookup.

	Section RAL_update.

		Program Fixpoint RAL_update (n : nat) (d : nat)
				(l : RAL d) (a : A) {measure (st_length l)}
				: RAL d :=
			match l with
			| [] => []
			| :: t => :: RAL_update n (S d) t a
			| clbt :: t => let size := 2 ^ d in
				match n <? size with
				| true => (CLBT_update d n clbt a) :: t
				| false => clbt :: RAL_update (n - size) (S d) t a
				end
			end.

		Obligation 2.
		Proof.
			simpl.
			rewrite <- Heq_l.
			apply Nat.lt_succ_diag_r.
		Qed.
		Obligation 4.
		Proof.
			rename Heq_anonymous into Hlt.
			apply eq_sym in Hlt.
			rewrite Nat.ltb_lt in Hlt.
			exact Hlt.
		Qed.
		Obligation 9.
		Proof.
			simpl.
			rewrite <- Heq_l.
			apply Nat.lt_succ_diag_r.
		Qed.

	End RAL_update.

End RAL.