Require Import Program Arith Lists.List.
Require Import NumRep.structure.tree.clbt.
Require Import NumRep.numerical.binary.BinNat.

Import ListNotations.

Section RAL.

Context {A : Type}.

Notation CLBT := (@CLBT A).

Variant RAL_BIT :=
	| RAL_Zero : RAL_BIT
	| RAL_One : CLBT -> RAL_BIT.

Definition RAL := list RAL_BIT.

Inductive valid_RAL : nat -> RAL -> Prop := 
	| valid_RAL_Nil : valid_RAL 0 []
	| valid_RAL_Top : forall {n : nat} (clbt : CLBT),
		valid_CLBT n clbt -> valid_RAL n [RAL_One clbt]
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

Fixpoint size (l : RAL) :=
	match l with
	| [] => nil
	| RAL_Zero :: t => 0 :: (size t)
	| RAL_One _ :: t => 1 :: (size t)
	end.

Section RAL_cons.

Let Fixpoint RAL_cons_aux (clbt : CLBT) (l : RAL) : RAL :=
	match l with
	| [] => [RAL_One clbt]
	| RAL_Zero :: t => RAL_One clbt :: t
	| RAL_One e :: t => RAL_Zero :: RAL_cons_aux (CLBT_merge e clbt) t
	end.

Lemma RAL_cons_aux_valid : forall  (l : RAL) (clbt : CLBT) {n : nat},
	valid_RAL n l ->valid_CLBT n clbt -> 
	valid_RAL n (RAL_cons_aux clbt l).
Proof.
	intros l.
	{	induction l as [| bit t HR]; intros clbt n Hl Hclbt.
	+	{	apply valid_RAL_Top.
			exact Hclbt.
		}
	+	{	destruct bit.
		+	{	destruct t; inversion_clear Hl.
			+	apply valid_RAL_Top.
				exact Hclbt.
			+	apply valid_RAL_One; assumption.
			}
		+	simpl.
			apply valid_RAL_Zero.
			{	inversion_clear Hl.
			+	apply valid_RAL_Top.
				apply CLBT_merge_valid; assumption.
			+	{	apply HR.
				+	assumption.
				+	apply CLBT_merge_valid; assumption.
				}
			}
		}
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
End RAL_cons.

Fixpoint RAL_head (l : RAL) : option A :=
match l with
| [] => None
| RAL_Zero :: t => RAL_head t
| RAL_One clbt :: _ => Some (CLBT_head clbt)
end.

Section RAL_tail.

Let Fixpoint uncons (l : RAL) : option (CLBT) * RAL :=
	match l with
	| [] => (None, [])		(* unreachable if valid_RAL (S n) l *)
	| [RAL_One clbt] => (Some clbt, [])
	| RAL_One clbt :: t => (Some clbt, RAL_Zero :: t)
	| RAL_Zero :: t => let (clbt, r) := uncons t in
		match clbt with
		| None => (None, RAL_Zero :: r)
		| Some clbt => let (tl, tr) := CLBT_break clbt in
			(Some tr, RAL_One tl :: r)
		end
	end.

Local Lemma uncons_valid_lhs : forall (l : RAL) {n : nat},
	valid_RAL n l -> valid_option_CLBT n (fst (uncons l)).
Proof.
	intro l.
	{	induction l as [|bit t HR]; intros n H.
	+	apply valid_CLBT_None.
	+	{	destruct bit; simpl.
		+	destruct (uncons t).
			{	destruct o.
			+	inversion_clear H.
				apply HR in H0.
				inversion_clear H0.
				apply CLBT_break_snd_valid in H.
				destruct (CLBT_break c) as [cl cr].
				apply valid_CLBT_Some.
				exact H.
			+	apply valid_CLBT_None.
			}
		+	destruct t;
				inversion_clear H;
				apply valid_CLBT_Some;
				assumption.
		}
	}
Qed.

Local Lemma uncons_valid_rhs : forall (l : RAL) {n : nat},
	valid_RAL n l ->
	valid_RAL n (snd (uncons l)) \/ exists clbt, l = [RAL_One clbt].
Proof.
	intro l.
	{	induction l as [|bit t HR]; intros n H.
	+	left.
		inversion_clear H.
		apply valid_RAL_Nil.
	+	{	destruct bit; simpl; inversion_clear H.
		+	left.
			specialize (HR (S n) H0).
			apply uncons_valid_lhs in H0.
			destruct (uncons t) eqn:Huncons.
			{	destruct o; inversion_clear H0.
			+	apply CLBT_break_fst_valid in H.
				destruct (CLBT_break _).
				{	destruct HR.
				+	apply valid_RAL_One; assumption.
				+	inversion H0 as [clbt H1].
					rewrite H1 in Huncons.
					inversion_clear Huncons.
					apply valid_RAL_Top.
					assumption.
				}
			+	apply valid_RAL_Zero.
				{	destruct HR.
				+	assumption.
				+	decompose record H.
					rewrite H0 in Huncons.
					discriminate.
				}
			}
		+	right.
			exists c.
			reflexivity.
		+	left.
			{	destruct t.
			+	inversion H1.
			+	apply valid_RAL_Zero.
				assumption.
			}
		}
	}
Qed.

Definition RAL_tail (l : RAL) : RAL :=
	let (_, ral) := uncons l in ral.

Lemma RAL_tail_valid : forall (l : RAL),
	valid_RAL 0 l -> valid_RAL 0 (RAL_tail l).
Proof.
	intros l H.
	apply uncons_valid_rhs in H.
	{	destruct H.
	+	assumption.
	+	inversion H as [c Hc].
		rewrite Hc.
		apply valid_RAL_Nil.
	}
Qed.

End RAL_tail.

Section RAL_lookup.

Let Fixpoint RAL_lookup_aux (l : RAL) (n : BinNat) (pos : list Bit) : option A :=
	match l with
	| [] => None
	| bit :: tl => match bit, n with
		| RAL_One clbt, [] => Some (CLBT_lookup clbt pos)
		| RAL_Zero, [] => RAL_lookup_aux tl [] (0 :: pos)
		| RAL_Zero, b :: tn => RAL_lookup_aux tl tn (b :: pos)
		| RAL_One clbt, 1 :: tn => RAL_lookup_aux tl tn (0 :: pos)
		| RAL_One _, 0 :: tn => RAL_lookupBorrow tl tn (1 :: pos)
		end
	end
with RAL_lookupBorrow (l : RAL) (n : BinNat) (pos : list Bit) : option A :=
	match l with
	| [] => None
	| bit :: tl => match bit, n with
		| RAL_One clbt, [] => Some (CLBT_lookup clbt pos)
		| RAL_Zero, [] => None (* Non reachable if n canonical *)
		| RAL_Zero, 0 :: tn => RAL_lookupBorrow tl tn (1 :: pos)
		| RAL_One _, 0 :: tn => RAL_lookupBorrow tl tn (0 :: pos)
		| RAL_Zero, 1 :: tn => RAL_lookup_aux tl tn (0 :: pos)
		| RAL_One clbt, [1] => Some (CLBT_lookup clbt pos)
		| RAL_One _, 1 :: tn => RAL_lookupBorrow tl tn (0 :: pos)
		end
	end.

Definition RAL_lookup l n := RAL_lookup_aux l n [].

End RAL_lookup.

Section RAL_update.

Fixpoint RAL_update_aux (l : RAL) (n : BinNat) (pos : list Bit) (a : A) : RAL :=
	match l with
	| [] => []
	| bit :: tl => match bit, n with
		| RAL_One clbt, [] => RAL_One (CLBT_update clbt pos a) :: tl
		| RAL_Zero, [] => bit :: RAL_update_aux tl [] (0 :: pos) a
		| RAL_Zero, b :: tn => bit :: RAL_update_aux tl tn (b :: pos) a
		| RAL_One _, 1 :: tn => bit :: RAL_update_aux tl tn (0 :: pos) a
		| RAL_One _, 0 :: tn => bit :: RAL_updateBorrow tl tn (1 :: pos) a
		end
	end
with RAL_updateBorrow (l : RAL) (n : BinNat) (pos : list Bit) (a : A) : RAL :=
	match l with
	| [] => []
	| bit :: tl => match bit, n with
		| RAL_One clbt, [] => RAL_One (CLBT_update clbt pos a) :: tl
		| RAL_Zero, [] => l (* Non reachable if n canonical *)
		| RAL_Zero, 0 :: tn => bit :: RAL_updateBorrow tl tn (1 :: pos) a
		| RAL_One _, 0 :: tn => bit :: RAL_updateBorrow tl tn (0 :: pos) a
		| RAL_Zero, 1 :: tn => bit :: RAL_update_aux tl tn (0 :: pos) a
		| RAL_One clbt, [1] => RAL_One (CLBT_update clbt pos a) :: tl
		| RAL_One _, 1 :: tn => bit :: RAL_updateBorrow tl tn (0 :: pos) a
		end
	end.

Definition RAL_update l n a := RAL_update_aux l n [] a.

Lemma RAL_update_aux_valid_Nil : forall (n : BinNat) (pos : list Bit) (a : A),
	valid_RAL (length pos) [] -> canonical_BinNat n ->
	valid_RAL (length pos) (RAL_update_aux [] n pos a).
Proof.
	intros n pos a H0 H1.
	inversion_clear H0.
	apply valid_RAL_Nil.
Qed.

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
					+	apply (HR (b :: tn) (0 :: pos)).
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

End RAL.