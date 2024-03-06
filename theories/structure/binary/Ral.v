Require Import Program Arith Lists.List.
Require Import NumRep.structure.tree.Clbt.
Require Import NumRep.numerical.binary.BinNat.
Require Import NumRep.utils.Utils.

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

Lemma RAL_safe_zero_empty : forall (l : RAL),
	RAL_safe_zero l = [] -> l = [].
Proof.
	intros l H.
	{	destruct l.
	+	reflexivity.
	+	discriminate.
	}
Qed.

Lemma RAL_safe_zero_valid : forall (l : RAL) {n : nat},
	valid_RAL (S n) l \/ l = [] ->
	valid_RAL n (RAL_safe_zero l) \/ RAL_safe_zero l = [].
Proof.
	intros l n H.
	{	destruct H; inversion_clear H.
	+	left.
		apply valid_RAL_Zero, valid_RAL_Top; assumption.
	+	left.
		apply valid_RAL_Zero, valid_RAL_Zero; assumption.
	+	left.
		apply valid_RAL_Zero, valid_RAL_One; assumption.
	+	right.
		reflexivity.
	}
Qed.

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


	(*Lemma RAL_size_non_zero : forall (l : RAL) {n : nat},
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
	Qed.*)

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
Local Definition RAL_discard_zipper := @CLBT_zip A DRAL.

Inductive valid_DRAL : nat -> DRAL -> Prop :=
	| valid_DRAL_Nil : valid_DRAL 0 []
	| valid_DRAL_Zero : forall {n : nat} (dl : DRAL),
		valid_DRAL n dl -> valid_DRAL (S n) (RAL_Zero :: dl)
	| valid_DRAL_One : forall {n : nat} (dl : DRAL) (clbt : CLBT),
		valid_DRAL n dl -> valid_CLBT n clbt -> valid_DRAL (S n) (RAL_One clbt :: dl).

Local Definition RAL_discard_split (o : option (RAL_discard_zipper * RAL)) (b : Bit)
		:	option (RAL_discard_zipper * RAL) :=
	match o, b with
	| None, _ => None
	| Some (zip, l), 0
		=> Some (DCLBT_rotate_left zip, RAL_safe_zero l)
	| Some ((clbt, _) as zip, l), 1
		=> Some (DCLBT_rotate_right zip, RAL_One (CLBT_left clbt) :: l)
	end.

Local Fixpoint RAL_discard_aux (l : RAL) (n : BinNat) (dral : DRAL)
		: option (RAL_discard_zipper * RAL) :=
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
		: option (RAL_discard_zipper * RAL) :=
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

Definition RAL_discard l n :=
	match n with
	| [] => l 
	| _ => match RAL_discard_aux l n [] with
		| None => []
		| Some (_, l) => l
		end
	end.

Definition valid_discard_option (d : nat)
		: option (RAL_discard_zipper * RAL) -> Prop :=
	option_predicate (
		fun '(zip, l) => valid_CLBT_zip valid_DRAL d zip /\ (valid_RAL d l \/ l = [])).

Local Lemma RAL_discard_split_valid : forall o (b : Bit) {d : nat},
	valid_discard_option (S d) o -> valid_discard_option d (RAL_discard_split o b).
Proof.
	intros o b d H.
	{	inversion_clear H; [|destruct a as [p l], p as [t dt]]; simpl.
	+	apply OP_None.
	+	destruct H0 as [Hz Hl], Hz as [Ht Hdt].
		inversion_clear Ht.
		{	destruct b.
		+	apply OP_Some.
			{	split; [split|].
			+	assumption.
			+	apply valid_DCLBT_Left; assumption.
			+	apply RAL_safe_zero_valid.
				assumption.
			}
		+	apply OP_Some.
			{	split; [split|].
			+	assumption.
			+	apply valid_DCLBT_Right; assumption.
			+	left.
				{	inversion_clear Hl.
				+	apply valid_RAL_One; assumption.
				+	rewrite H1.
					apply valid_RAL_Top; assumption.
				}
			}
		}
	}
Qed.

Local Lemma RAL_discard_aux_valid : forall (l : RAL) (n : BinNat) (dral : DRAL) {d : nat},
	valid_RAL d l -> valid_DRAL d dral ->
	valid_discard_option d (RAL_discard_aux l n dral)
	/\ valid_discard_option d (RAL_discard_borrow l n dral).
Proof.
	intro l.
	{	induction l as [| bit t HR]; intros n dral d Hl Hd; split; simpl.
	+	apply OP_None.
	+	apply OP_None.
	+	{	destruct n as [|b tn]; [| destruct b]; destruct bit as [| clbt].
		+	apply OP_None.
		+	apply OP_None.
		+	inversion_clear Hl.
			apply valid_DRAL_Zero in Hd.
			apply RAL_discard_split_valid.
			apply HR; assumption.
		+	apply RAL_discard_split_valid.
			inversion_clear Hl; [apply OP_None|].
			apply (valid_DRAL_One _ clbt) in Hd; [| assumption].
			apply HR; assumption.
		+	inversion_clear Hl.
			apply RAL_discard_split_valid.
			apply valid_DRAL_Zero in Hd.
			apply HR; assumption.
		+	{	destruct tn.
			+	apply OP_Some.				
				{	split; [split|].
				+	inversion_clear Hl; assumption.
				+	apply valid_DCLBT_Root.
					assumption.
				+	apply RAL_safe_zero_valid.	
					{	inversion_clear Hl.
					+	right.
						reflexivity.
					+	left.
						assumption.
					}
				}
			+	{	inversion_clear Hl.
				+	apply OP_None.
				+	apply RAL_discard_split_valid.
					apply (valid_DRAL_One _ clbt) in Hd; [| assumption].
					apply HR; assumption.
				}
			}
		}
	+	{	destruct n as [|b tn]; [| destruct b]; destruct bit as [| clbt].
		+	inversion_clear Hl.
			apply RAL_discard_split_valid.
			apply valid_DRAL_Zero in Hd.
			apply HR; assumption.
		+	apply OP_Some.
			{	split; [split|].
			+	inversion_clear Hl; assumption.
			+	apply valid_DCLBT_Root.
				assumption.
			+	apply RAL_safe_zero_valid.
				{	inversion_clear Hl.
					+	right.
						reflexivity.
					+	left.
						assumption.
				}
			}
		+	inversion_clear Hl.
			apply RAL_discard_split_valid.
			apply valid_DRAL_Zero in Hd.
			apply HR; assumption.
		+	{	inversion_clear Hl.
			+	apply OP_None.
			+	apply RAL_discard_split_valid.
				apply (valid_DRAL_One _ clbt) in Hd; [| assumption].
				apply HR; assumption.
			}
		+	inversion_clear Hl.
			apply RAL_discard_split_valid.
			apply valid_DRAL_Zero in Hd.
			apply HR; assumption.
		+	{	inversion_clear Hl.
			+	apply OP_None.
			+	apply RAL_discard_split_valid.
				apply (valid_DRAL_One _ clbt) in Hd; [| assumption].
				apply HR; assumption.
			}
		}
	}
Qed.

Lemma RAL_discard_valid : forall (l : RAL) (n : BinNat),
	valid_RAL 0 l -> valid_RAL 0 (RAL_discard l n).
Proof.
	intros l n H.
	{	destruct n.
	+	assumption.
	+	simpl.
		{	apply (RAL_discard_aux_valid l (b :: n) []) in H.
		+	destruct H as [H H2].
			{	destruct (RAL_discard_aux l (b :: n)).
			+	destruct p as [p r].
				inversion H.
				destruct H1 as [Hz Hl].
				{	destruct Hl as [Hl|Hl].
				+	assumption.
				+	rewrite Hl.
					apply valid_RAL_Nil.
				}
			+	apply valid_RAL_Nil.
			}
		+	apply valid_DRAL_Nil.
		}
	}
Qed.

Local Definition RAL_undiscard_keep '(dl, l) : (DRAL * RAL) :=
	match dl with
	| [] => ([], l)
	| bit :: dt => (dt, bit :: l)
	end.

Local Fixpoint RAL_undiscard (clbt : CLBT) (zipper : DCLBT) (l : RAL)
		: DRAL * RAL :=
	match zipper, l with
	| DCLBT_Root dral, _ => (dral, RAL_One clbt :: (tail l))
	| DCLBT_Left dt t, _ => RAL_undiscard_keep (RAL_undiscard (Node clbt t) dt (tail l))
	| DCLBT_Right t dt, RAL_Zero :: _ | DCLBT_Right t dt, []
		=> RAL_undiscard_keep (RAL_undiscard (Node t clbt) dt (tail l))
	| DCLBT_Right _ dt, RAL_One t :: _
		=> RAL_undiscard_keep (RAL_undiscard (Node t clbt) dt (tail l))
	end.

Definition valid_RAL_zip (n : nat) '(dl, l) := valid_DRAL n dl /\ valid_RAL n l.

Definition RAL_undiscard_keep_valid : forall (rzip : DRAL * RAL) {n : nat},
	valid_RAL_zip (S n) rzip -> valid_RAL_zip n (RAL_undiscard_keep rzip).
Proof.
	intros rzip n H.
	destruct rzip as [dl l].
	destruct H as [Hdl Hl].
	{	destruct dl; inversion_clear Hdl; split.
	+	assumption.
	+	apply valid_RAL_Zero.
		assumption.
	+	assumption.
	+	apply valid_RAL_One; assumption.
	}
Qed.


Lemma RAL_undiscard_valid : forall (dt : DCLBT) (t : CLBT) (l : RAL) {n : nat},
	valid_RAL n l \/ l = [] -> valid_CLBT_zip valid_DRAL n (t, dt) ->
	valid_RAL_zip n (RAL_undiscard t dt l).
Proof.
	intros dt.
	{	induction dt as [r| dt HR| c dc HR]; intros t l n Hl Hzip; destruct Hzip as [Ht Hdt]; simpl.
	+	inversion_clear Hdt.
		{	split; [| destruct l as [| bit tl]].
		+	assumption.
		+	apply valid_RAL_Top.
			assumption.
		+	destruct Hl as [Hl|Hl]; [|discriminate].
			{	inversion_clear Hl.
			+	apply valid_RAL_Top.
				assumption.
			+	apply valid_RAL_One; assumption.
			+	apply valid_RAL_One; assumption.
			}
		}
	+	apply RAL_undiscard_keep_valid.
		{	apply HR.
		+	{	destruct l as [| bit tl]; [| destruct tl as [|bit2 tl]].
			+	right.
				reflexivity.
			+	right.
				reflexivity.
			+	left.
				destruct Hl as [Hl|Hl]; [|discriminate].
				inversion_clear Hl; assumption.
			}
		+	inversion_clear Hdt.
			pose proof (Hvn := valid_Node _ _ Ht H0).
			split; assumption.
		}
	+	{	destruct l as [| bit tl]; [| destruct bit];
				apply RAL_undiscard_keep_valid.
		+	{	apply HR.
			+	right.
				reflexivity.
			+	inversion_clear Hdt.
				pose proof (Hvn := valid_Node _ _ H Ht).
				split; assumption.
			}
		+	{	apply HR.
			+	{	destruct tl as [|bit2 tl].
				+	right.
					reflexivity.
				+	left.
					destruct Hl as [Hl|Hl]; [|discriminate].
					inversion_clear Hl.
					assumption.
				}
			+	inversion_clear Hdt.
				pose proof (Hvn := valid_Node _ _ H Ht).
				split; assumption.
			}
		+	{	apply HR.
			+	{	destruct tl as [|bit2 tl].
				+	right.
					reflexivity.
				+	left.
					destruct Hl as [Hl|Hl]; [|discriminate].
					inversion_clear Hl.
					assumption.
				}
			+	destruct Hl as [Hl|Hl]; [|discriminate].
				inversion_clear Hdt.
				inversion_clear Hl;
					pose proof (Hvn := valid_Node _ _ H1 Ht);
					split; assumption.
			}
		}
	}
Qed.

End RAL_discard.

Definition RAL_lookup l n := RAL_head (RAL_discard l n).

Section RAL_update.

Local Definition touch_head l a :=
	match l with
	| [] => []
	| _ => RAL_cons a (RAL_tail l)
	end.

Lemma RAL_touch_head_valid : forall (l : RAL) (a : A),
	valid_RAL 0 l -> valid_RAL 0 (touch_head l a).
Proof.
	intros l a H.
	{	destruct l.
	+	assumption.
	+	apply RAL_cons_valid, RAL_tail_valid.
		assumption.
	}
Qed.

Definition RAL_update l n a :=
	match n with
	| [] => touch_head l a
	| _ => match RAL_discard_aux l n [] with
		| None => l
		| Some (c, zipper, r) => snd (RAL_undiscard c zipper (touch_head r a))
		end
	end.

Lemma RAL_update_valid : forall (l : RAL) (n : BinNat) (a : A),
	valid_RAL 0 l -> valid_RAL 0 (RAL_update l n a).
Proof.
	intros l n a H.
	{	destruct n.
	+	apply RAL_touch_head_valid.
		assumption.
	+	simpl.
		apply (RAL_discard_aux_valid _ (b :: n) []) in H as Hd; [| apply valid_DRAL_Nil].
		apply proj1 in Hd.
		{	destruct (RAL_discard_aux l (b :: n)).
		+	destruct p as [zip r], zip as [c zip].
			inversion_clear Hd.
			destruct H0 as [Hz Hr], Hz as [Hc Hz].
			{	assert (valid_RAL 0 (touch_head r a) \/ (touch_head r a) = []).
			+	{	destruct Hr as [Hr|Hr].
				+	left.
					apply RAL_touch_head_valid.
					assumption.
				+	right.
					rewrite Hr.
					reflexivity.
				}
			+	apply (RAL_undiscard_valid zip c _) in H0;
					[| split; assumption].
				destruct RAL_undiscard.
				destruct H0.
				assumption.
			}
		+	assumption.
		}
	}
Qed.

End RAL_update.

End RAL.