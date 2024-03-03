Require Import Program Arith Lists.List.
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
	| valid_RAL_Nil : valid_RAL 0 []
	| valid_RAL_Top : forall {n : nat} (clbt : CLBT),
		valid_CLBT n clbt -> valid_RAL n [RAL_One clbt]
	| valid_RAL_Zero : forall {n : nat} (ral : RAL),
		valid_RAL (S n) ral -> valid_RAL n (RAL_Zero :: ral)
	| valid_RAL_One : forall {n : nat} (ral : RAL) (clbt : CLBT),
		valid_CLBT n clbt -> valid_RAL (S n) ral
		-> valid_RAL n (RAL_One clbt :: ral).

Definition RAL_empty : RAL := [].
Definition RAL_is_empty (l : RAL) :=
	match l with
	| [] => true
	| _ => false
	end.

Local Definition RAL_safe_zero l :=
	match l with
	| [] => []
	| _ => RAL_Zero :: l
	end.

Section RAL_size.

	Fixpoint size (l : RAL) :=
		match l with
		| [] => nil
		| RAL_Zero :: t => 0 :: (size t)
		| RAL_One _ :: t => 1 :: (size t)
		end.

	Lemma RAL_size_valid : forall (l : RAL) {n : nat},
		valid_RAL n l -> valid_BinNat n (size l).
	Proof.
		intro l.
		{	induction l as [| bit t HR]; intros n H; inversion_clear H.
		+	apply valid_BinNat_Nil.
		+	apply valid_BinNat_Top.
		+	apply valid_BinNat_Cons.
			apply HR.
			assumption.
		+	apply valid_BinNat_Cons.
			apply HR.
			assumption.
		}
	Qed.


	Lemma RAL_size_non_zero : forall (l : RAL) {n : nat},
		valid_RAL (S n) l -> [] <? size l = true.
	Proof.
		intros l n H.
		destruct l as [| bit t]; inversion_clear H; reflexivity.
	Qed.

	Lemma RAL_size_non_zero_borrow : forall (l : RAL) {n : nat},
		valid_RAL (S n) l -> gt_dec_borrow (size l) [] = true.
	Proof.
		intros l n H.
		destruct l as [|bit t]; inversion_clear H; reflexivity.
	Qed.

End RAL_size.

Section RAL_cons.

Local Fixpoint RAL_cons_aux (clbt : CLBT) (l : RAL) : RAL :=
	match l with
	| [] => [RAL_One clbt]
	| RAL_Zero :: t => RAL_One clbt :: t
	| RAL_One e :: t => RAL_Zero :: RAL_cons_aux (CLBT_merge e clbt) t
	end.

Lemma RAL_cons_aux_valid : forall  (l : RAL) (clbt : CLBT) {n : nat},
	valid_RAL n l -> valid_CLBT n clbt -> 
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

Local Fixpoint uncons (l : RAL) : option (CLBT) * RAL :=
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
	valid_RAL (S n) l ->
	exists clbt, valid_CLBT (S n) clbt /\ Some clbt = fst (uncons l).
Proof.
	intro l.
	{	induction l as [|bit t HR]; intros n Hl; inversion_clear Hl.
	+	exists clbt.
		{	split.
		+	assumption.
		+	reflexivity.
		}
	+	apply HR in H.
		destruct H as [clbt].
		destruct H as [Hclbt Heq].
		destruct clbt as [| clbtl clbtr]; inversion_clear Hclbt.
		exists clbtr.
		{	split.
		+	assumption.
		+	simpl.
			destruct (uncons t).
			simpl in Heq.
			rewrite <- Heq.
			reflexivity.
		}
	+	exists clbt.
		{	split.
		+	assumption.
		+	simpl.
			destruct t; reflexivity.
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
			{	destruct HR.
			+	destruct H0 as [clbt H0], H0 as [Hclbt Heq].
				destruct (uncons t).
				simpl in Heq, H.
				rewrite <- Heq.
				destruct clbt as [|clbtl clbtr]; inversion_clear Hclbt.
				apply valid_RAL_One; assumption.
			+	destruct H as [clbtTop Hct].
				destruct H0 as [clbtLhs Hcl].
				destruct Hcl as [Hclbt Heq].
				rewrite Hct in *.
				simpl in *.
				inversion Heq as [He].
				rewrite <- He.
				destruct clbtLhs; inversion_clear Hclbt.
				apply valid_RAL_Top.
				assumption.
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

Lemma RAL_cons_tail_aux : forall (l : RAL) (clbt : CLBT) {n : nat},
	valid_RAL n l -> valid_CLBT n clbt ->
	uncons (RAL_cons_aux clbt l) = (Some clbt, l).
Proof.
	intros l.
	{	induction l as [| bit t HR]; try destruct bit;
			intros clbt n Hl Hclbt.
	+	reflexivity.
	+	{	destruct t; inversion_clear Hl.
		+	inversion_clear H.
		+	reflexivity.
		}
	+	simpl.
		{	destruct t; inversion_clear Hl.
		+	reflexivity.
		+	reflexivity.
		+	pose proof (Hmerge := CLBT_merge_valid _ _ H Hclbt).
			pose proof (Huncons := RAL_cons_aux_valid _ _ H0 Hmerge).
			apply uncons_valid_lhs in Huncons.
			specialize (HR _ _ H0 Hmerge).
			destruct Huncons as [c0 Huncons], Huncons as [Hc0 Hc0eq].
			destruct (uncons _).
			simpl in Hc0eq.
			rewrite <- Hc0eq.
			destruct c0 as [|c0l c0r]; inversion_clear Hc0.
			simpl.
			apply pair_equal_spec in HR; destruct HR as [Ho Hrt].
			rewrite <- Hc0eq in Ho.
			inversion_clear Ho.
			{	apply injective_projections; simpl.
			+	reflexivity.
			+	f_equal.
				assumption.
			}
		}
	}
Qed.

Lemma RAL_cons_tail : forall (l : RAL) (a : A),
	valid_RAL 0 l ->
	RAL_tail (RAL_cons a l) = l.
Proof.
	intros l a H.
	pose proof (HR := RAL_cons_tail_aux _ _ H (singleton_valid a)).
	unfold RAL_tail, RAL_cons.
	destruct (uncons _).
	apply pair_equal_spec in HR.
	destruct HR.
	assumption.
Qed.

End RAL_tail.

Section RAL_discard.

Local Definition DRAL := RAL.
Local Definition RAL_discard_zipper := @DCLBT A DRAL.

Local Definition RAL_discard_split (o : option (CLBT * RAL_discard_zipper * RAL)) (b : Bit) :=
	match o, b with
	| None, _ => None
	| Some (clbt, zipper, l), 0
		=> Some (DCLBT_rotate_left clbt zipper, RAL_safe_zero l)
	| Some (clbt, zipper, l), 1
		=> Some (DCLBT_rotate_right clbt zipper, RAL_One (CLBT_left clbt) :: l)
	end.

Local Fixpoint RAL_discard_aux (l : RAL) (n : BinNat) (dral : DRAL)
		: option (CLBT * RAL_discard_zipper * RAL) :=
	match l, n with
	| [], _ => None
	| _, [] => None
	| RAL_One clbt :: tl, [1] => Some (clbt, DCLBT_Root dral, RAL_safe_zero tl)
	| RAL_One _ as bit :: tl, 1 :: tn | RAL_Zero as bit :: tl, 0 :: tn
		=> RAL_discard_split (RAL_discard_aux tl tn (bit :: dral)) 0
	| RAL_One _ as bit :: tl, 0 :: tn
		=> RAL_discard_split (RAL_discard_aux tl tn (bit :: dral)) 1
	| RAL_Zero as bit :: tl, 1 :: tn
		=> RAL_discard_split (RAL_discard_borrow tl tn (bit :: dral)) 1
	end
with RAL_discard_borrow  (l : RAL) (n : BinNat) (dral : DRAL)
		: option (CLBT * RAL_discard_zipper * RAL) :=
	match l, n with
	| [], _ => None
	| RAL_One clbt :: tl, [] => Some (clbt, DCLBT_Root dral, RAL_safe_zero tl)
	| RAL_Zero as bit :: tl, []
		=> RAL_discard_split (RAL_discard_borrow tl [] (bit :: dral)) 1
	| RAL_One _ as bit :: tl, 1 :: tn | RAL_Zero as bit :: tl, 0 :: tn
		=> RAL_discard_split (RAL_discard_borrow tl tn (bit :: dral)) 1
	| RAL_One _ as bit :: tl, 0 :: tn
		=> RAL_discard_split (RAL_discard_aux tl tn (bit :: dral)) 0
	| RAL_Zero as bit :: tl, 1 :: tn
		=> RAL_discard_split (RAL_discard_borrow tl tn (bit :: dral)) 0
	end.

Local Definition RAL_undiscard_keep '(dl, l) : (DRAL * RAL) :=
	match dl with
	| [] => ([], l)
	| bit :: dt => (dt, bit :: l)
	end.

Local Fixpoint RAL_undiscard (clbt : CLBT) (zipper : RAL_discard_zipper) (l : RAL)
		: DRAL * RAL :=
	match zipper with
	| DCLBT_Root dral => (dral, RAL_One clbt :: l)
	| DCLBT_Left dt t => RAL_undiscard_keep (RAL_undiscard (Node clbt t) dt (tail l))
	| DCLBT_Right t dt => RAL_undiscard_keep (RAL_undiscard (Node t clbt) dt (tail l)) 
	end.

Definition RAL_discard l n :=
	match n with
	| [] => l 
	| _ => match RAL_discard_aux l n [] with
		| None => []
		| Some (_, _, l) => l
		end
	end.

End RAL_discard.

Section RAL_lookup.

Definition RAL_lookup l n := RAL_head (RAL_discard l n).

(*Local Fixpoint RAL_lookup_aux (l : RAL) (n : BinNat) (pos : list Bit) : option A :=
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

Definition RAL_lookup l n := RAL_lookup_aux l n [].*)

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

End RAL.