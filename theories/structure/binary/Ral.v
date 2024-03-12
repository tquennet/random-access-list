Require Import Arith Lists.List FunInd.
Require Import NumRep.utils.Utils.
Require Import NumRep.structure.tree.Clbt.
Require Import NumRep.numerical.binary.BinNat.

Import ListNotations.
Open Scope bin_nat_scope.

Section RAL.

Context {A : Type}.

Notation CLBT := (@CLBT A).

Variant RAL_BIT :=
	| RAL_Zero : RAL_BIT
	| RAL_One : CLBT -> RAL_BIT.

Definition RAL := list RAL_BIT.

Inductive valid_RAL : nat -> RAL -> Prop := 
	| valid_RAL_Nil : forall {n : nat}, valid_RAL n []
	| valid_RAL_Zero : forall {n : nat} (ral : RAL),
		valid_RAL (S n) ral -> valid_RAL n (RAL_Zero :: ral)
	| valid_RAL_One : forall {n : nat} (ral : RAL) (clbt : CLBT),
		valid_CLBT n clbt -> valid_RAL (S n) ral
		-> valid_RAL n (RAL_One clbt :: ral).

Definition empty : RAL := [].
Definition is_empty (l : RAL) :=
	match l with
	| [] => true
	| _ => false
	end.

Local Definition RAL_ends_One := ends_pred (fun b => exists c, b = RAL_One c).

Local Lemma RAL_ends_One_Zero : ~RAL_ends_One [RAL_Zero].
Proof.
	intro H.
	inversion_clear H.
	destruct H0.
	discriminate.
Qed.

Local Lemma RAL_ends_cons : forall (l : RAL) (bit : RAL_BIT),
	RAL_ends_One (bit :: l) -> RAL_ends_One l.
Proof.
	intros l bit H.
	{	destruct l.
	+	apply OP_None.
	+	exact H.
	}
Qed.

Section RAL_cons.

Local Fixpoint RAL_cons_aux (clbt : CLBT) (l : RAL) : RAL :=
	match l with
	| [] => [RAL_One clbt]
	| RAL_Zero :: t => RAL_One clbt :: t
	| RAL_One e :: t => RAL_Zero :: RAL_cons_aux (Node e clbt) t
	end.

Functional Scheme RAL_cons_aux_ind := Induction for RAL_cons_aux Sort Prop.

Lemma RAL_cons_aux_valid : forall  (l : RAL) (clbt : CLBT) {n : nat},
	valid_RAL n l -> valid_CLBT n clbt -> 
	valid_RAL n (RAL_cons_aux clbt l).
Proof.
	intros clbt l.
	{	functional induction (RAL_cons_aux l clbt); intros n Hl Hclbt.
	+ apply valid_RAL_One, valid_RAL_Nil.
		assumption.
	+	inversion_clear Hl.
		apply valid_RAL_One; assumption.
	+ inversion_clear Hl.
		apply valid_RAL_Zero.
		apply IHr; [assumption|].
		apply valid_Node; assumption.
	}
Qed.

Definition RAL_cons (a : A) (l : RAL) := RAL_cons_aux (singleton a) l.

Lemma RAL_cons_valid : forall (a : A) (l : RAL),
	valid_RAL 0 l -> valid_RAL 0 (RAL_cons a l).
Proof.
	intros a l H.
	{	apply RAL_cons_aux_valid.
	+	exact H.
	+	apply singleton_valid.
	}
Qed.

Local Lemma RAL_cons_aux_non_empty : forall (l : RAL) (clbt : CLBT),
	exists b tl, b :: tl = RAL_cons_aux clbt l.
Proof.
	intros l clbt.
	{	destruct l as [|b tl]; [|destruct b].
	+	exists (RAL_One clbt), []; reflexivity.
	+	exists (RAL_One clbt), tl; reflexivity.
	+	exists RAL_Zero, (RAL_cons_aux (Node c clbt) tl).
		reflexivity.
	}
Qed.

Local Lemma RAL_cons_aux_ends : forall (l : RAL) (clbt : CLBT),
	 RAL_ends_One l -> RAL_ends_One (RAL_cons_aux clbt l).
Proof.
	intros l clbt.
	{	functional induction (RAL_cons_aux clbt l); intro H.
		+	apply OP_Some.
			exists clbt; reflexivity.
		+	{	destruct t.
			+ apply OP_Some.
				exists clbt; reflexivity.
			+	unfold RAL_cons.
				exact H.
			}
		+	decompose record (RAL_cons_aux_non_empty t (Node e0 clbt)).
			apply RAL_ends_cons in H.
			apply IHr in H.
			rewrite <- H1 in*.
			exact H.
		}
Qed.

Local Lemma RAL_cons_ends : forall (l : RAL) (a : A),
	RAL_ends_One l -> RAL_ends_One (RAL_cons a l).
Proof.
	intros l a H.
	apply RAL_cons_aux_ends.
	assumption.
Qed.
End RAL_cons.

Inductive CRAL : RAL -> Prop :=
	| CRAL_Empty : CRAL empty
	| CRAL_Cons : forall (l : RAL) (a : A),
		CRAL l -> CRAL (RAL_cons a l).

Lemma CRAL_ends : forall (l : RAL),
	CRAL l -> RAL_ends_One l.
Proof.
	intros n H.
	{	induction H as [| n HCBN HR].
	+ apply OP_None.
	+ apply RAL_cons_ends.
		assumption.
	}
Qed.

Fixpoint size (l : RAL) :=
	match l with
	| [] => nil
	| RAL_Zero :: t => 0 :: (size t)
	| RAL_One _ :: t => 1 :: (size t)
	end.

Fixpoint RAL_head (l : RAL) : option A :=
match l with
| [] => None
| RAL_Zero :: t => RAL_head t
| RAL_One clbt :: _ => Some (CLBT_head clbt)
end.

Section RAL_tail.

Local Fixpoint uncons (l : RAL) : option (CLBT) * RAL :=
	match l with
	| [] => (None, [])		(* unreachable if valid_RAL (S n) l *)
	| [RAL_One clbt] => (Some clbt, [])
	| RAL_One clbt :: t => (Some clbt, RAL_Zero :: t)
	| RAL_Zero :: t => let (clbt, r) := uncons t in
		match clbt with
		| None => (None, RAL_Zero :: r)
		| Some clbt => (Some (CLBT_right clbt), RAL_One (CLBT_left clbt) :: r)
		end
	end.
	
Functional Scheme uncons_ind := Induction for uncons Sort Prop.

Local Lemma uncons_valid_lhs : forall (l : RAL) {n : nat},
	valid_RAL n l -> option_predicate (valid_CLBT n) (fst (uncons l)).
Proof.
	intro l.
	{	functional induction (uncons l); intros n Hl.
	+ apply OP_None.
	+	apply OP_Some.
		apply CLBT_right_valid.
		inversion_clear Hl.
		apply IHp in H.
		rewrite e1 in H.
		inversion_clear H.
		assumption.
	+	apply OP_None.
	+	apply OP_Some.
		inversion_clear Hl.
		assumption.
	+	apply OP_Some.
		inversion_clear Hl.
		assumption.
	}
Qed.

Local Lemma uncons_valid_rhs : forall (l : RAL) {n : nat},
	valid_RAL n l -> valid_RAL n (snd (uncons l)).
Proof.
	intro l.
	{	functional induction (uncons l); intros n Hl; inversion_clear Hl.
	+	apply valid_RAL_Nil.
	+	apply uncons_valid_lhs in H as Hc.
		apply IHp in H.
		rewrite e1 in Hc, H.
		inversion_clear Hc.
		apply CLBT_left_valid in H0.
		apply valid_RAL_One; assumption.
	+ apply valid_RAL_Zero.
		apply IHp in H.
		rewrite e1 in H.
		assumption.
	+ apply valid_RAL_Nil.
	+ apply valid_RAL_Zero.
		assumption.
	}
Qed.

Definition RAL_tail (l : RAL) : RAL := snd (uncons l).

Lemma RAL_tail_valid : forall (l : RAL),
	valid_RAL 0 l -> valid_RAL 0 (RAL_tail l).
Proof.
	intros l H.
	apply uncons_valid_rhs.
	assumption.
Qed.

Lemma RAL_cons_uncons : forall (l : RAL) (clbt : CLBT),
	CRAL l -> uncons (RAL_cons_aux clbt l) = (Some clbt, l).
Proof.
	intros l clbt Hcl.
	apply CRAL_ends in Hcl.
	{	functional induction (RAL_cons_aux clbt l); intros .
	+	reflexivity.
	+	destruct t; [apply RAL_ends_One_Zero in Hcl; contradiction|].
		reflexivity.
	+	simpl.
		apply RAL_ends_cons in Hcl.
		apply IHr in Hcl.
		rewrite Hcl.
		reflexivity.
	}
Qed.

Lemma RAL_cons_tail : forall (l : RAL) (a : A),
	CRAL l -> RAL_tail (RAL_cons a l) = l.
Proof.
	intros l a H.
	pose proof (HR := RAL_cons_uncons _ (singleton a) H).	
	unfold RAL_tail, RAL_cons.
	rewrite HR.
	reflexivity.
Qed.

End RAL_tail.

(*	modifiés dans la branche binary-discard

Section RAL_lookup.

Local Fixpoint RAL_lookup_aux (l : RAL) (n : BinNat) (pos : list Bit) : option A :=
	match l, n with
	| [], _ => None
	| RAL_One clbt :: _, [] => Some (CLBT_lookup clbt pos)
	| RAL_Zero :: tl, [] => RAL_lookup_aux tl [] (0 :: pos)
	| RAL_Zero :: tl, b :: tn => RAL_lookup_aux tl tn (b :: pos)
	| RAL_One _ :: tl, 1 :: tn => RAL_lookup_aux tl tn (0 :: pos)
	| RAL_One _ :: tl, 0 :: tn => RAL_lookup_borrow tl tn (1 :: pos)
	end
with RAL_lookup_borrow (l : RAL) (n : BinNat) (pos : list Bit) : option A :=
	match l, n with
	| RAL_One clbt :: _, [] => Some (CLBT_lookup clbt pos)
	| RAL_Zero :: tl, [] => RAL_lookup_borrow tl [] (1 :: pos)
	| [], _ => None
	| RAL_One clbt :: _, [1] => Some (CLBT_lookup clbt pos)
	| RAL_Zero :: tl, 1 :: tn => RAL_lookup_aux tl tn (0 :: pos)
	| RAL_One _ :: tl, 1 :: tn | RAL_Zero :: tl, 0 :: tn
		=> RAL_lookup_borrow tl tn (1 :: pos)
	| RAL_One _ :: tl, 0 :: tn => RAL_lookup_borrow tl tn (0 :: pos)
	end.

Definition RAL_lookup l n := RAL_lookup_aux l n [].

End RAL_lookup.

Section RAL_update.

Fixpoint RAL_update_aux (l : RAL) (n : BinNat) (pos : list Bit) (a : A) : RAL :=
	match l, n with
	| [], _ => []
	| RAL_One clbt :: tl, [] => RAL_One (CLBT_update clbt pos a) :: tl
	| RAL_Zero :: tl, [] => RAL_Zero :: RAL_update_aux tl [] (0 :: pos) a
	| RAL_Zero :: tl, b :: tn => RAL_Zero :: RAL_update_aux tl tn (b :: pos) a
	| (RAL_One _ as bit) :: tl, 1 :: tn => bit :: RAL_update_aux tl tn (0 :: pos) a
	| (RAL_One _ as bit) :: tl, 0 :: tn => bit :: RAL_updateBorrow tl tn (1 :: pos) a
	end
with RAL_updateBorrow (l : RAL) (n : BinNat) (pos : list Bit) (a : A) : RAL :=
	match l, n with
	| RAL_One clbt :: tl, [] => RAL_One (CLBT_update clbt pos a) :: tl
	| RAL_Zero :: tl, [] => RAL_Zero :: RAL_updateBorrow tl [] (1 :: pos) a
	| [], _ => []
	| RAL_One clbt :: tl, [1] => RAL_One (CLBT_update clbt pos a) :: tl
	| RAL_Zero :: tl, 1 :: tn => RAL_Zero :: RAL_update_aux tl tn (0 :: pos) a
	| (RAL_One _ as bit) :: tl, 1 :: tn | (RAL_Zero as bit) :: tl, 0 :: tn
		=> bit :: RAL_updateBorrow tl tn (1 :: pos) a
	| (RAL_One _ as bit) :: tl, 0 :: tn
		=> bit :: RAL_updateBorrow tl tn (0 :: pos) a
	end.

Definition RAL_update l n a := RAL_update_aux l n [] a.

Lemma RAL_update_aux_valid : forall (l : RAL) (n : BinNat)
		(pos : list Bit) (a : A),
	valid_RAL (length pos) l ->
	valid_RAL (length pos) (RAL_update_aux l n pos a)
	/\ valid_RAL (length pos) (RAL_updateBorrow l n pos a).
Proof.
	intro l.
	{	induction l as [|bit t HR]; intros n pos a Hl.
	+	split; inversion_clear Hl; apply valid_RAL_Nil.
	+	{	split.
		+	{	destruct bit as [| clbt], n as [|b tn];
				inversion_clear Hl; simpl.
			+	apply valid_RAL_Zero.
				apply (HR [] (0 :: pos)).
				assumption.
			+	apply valid_RAL_Zero.
				apply (HR tn (b :: pos)).
				assumption.
			+	apply valid_RAL_Top.
				apply CLBT_update_valid.
				assumption.
			+	pose (Hclbt := CLBT_update_valid _ _ a H).
				{	destruct t.
				+	apply valid_RAL_Top.
					assumption.
				+	apply valid_RAL_One; assumption.
				}
			+	destruct b; apply valid_RAL_Top; assumption.
			+	{	destruct b; apply valid_RAL_One.
				+	assumption.
				+	apply (HR tn (1 :: pos)).
					assumption.
				+	assumption.
				+	apply (HR tn (0 :: pos)).
					assumption.
				}
			}
		+	{	destruct bit as [| clbt], n as [|b tn];
				inversion_clear Hl; simpl.
			+	apply valid_RAL_Zero.
				apply (HR [] (1 :: pos)).
				assumption.
			+	{	destruct b; apply valid_RAL_Zero.
				+	apply (HR tn (1 :: pos)).
					assumption.
				+	apply (HR tn (0 :: pos)).
					assumption.
				}
			+	apply valid_RAL_Top.
				apply CLBT_update_valid.
				assumption.
			+	pose (Hclbt := CLBT_update_valid _ _ a H).
				{	destruct t.
				+	apply valid_RAL_Top.
					assumption.
				+	apply valid_RAL_One; assumption.
				}
			+	{	destruct b.
				+	apply valid_RAL_Top.
					assumption.
				+	{	destruct tn; apply valid_RAL_Top.
					+	apply CLBT_update_valid.
						assumption.
					+	assumption.
					}
				}
			+	{	destruct b.
				+	{	apply valid_RAL_One.
					+	assumption.
					+	apply (HR tn (0 :: pos)).
						assumption.
					}
				+	{	destruct tn; apply valid_RAL_One.
					+	apply CLBT_update_valid.
						assumption.
					+	assumption.
					+	assumption.
					+	apply (HR (b :: tn) (1 :: pos)).
						assumption.
					}
				}
			}
		}
	}
Qed.

Lemma RAL_update_valid : forall (l : RAL) (n : BinNat) (a : A),
	valid_RAL 0 l -> valid_RAL 0 (RAL_update l n a).
Proof.
	intros l n a H.
	apply (RAL_update_aux_valid l n []).
	assumption.
Qed.

End RAL_update.
*)

End RAL.