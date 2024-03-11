Require Import Arith Lists.List FunInd.
Require Import NumRep.utils.Utils.
Require Import NumRep.structure.tree.Clbt.
Require Import NumRep.numerical.binary.BinNat.
Require Import NumRep.utils.Utils.

Import ListNotations.
Open Scope bin_nat_scope.

(********************************************************************************)
(*	RAL (A : Type) == the type of random access list of items of type A.		*)
(*			VRAL  == a predicate identifying valid RAL,							*)
(*					 all operations are defined only over valid RAL				*)
(*		RAL_empty == the empty RAL												*)
(*		cons a l  == the RAL of element a followed by l							*)
(*	**	Unary operator:															*)
(*		size l == element count of l											*)
(*		RAL_tail l == RAL_empty if l is RAL_empty								*)
(*					  r if l is cons a r										*)
(*	**	Indexed operations:														*)
(*		discard l n  == l without its first n elements							*)
(*		lookup l n   == an option containing the nth element of l,				*)
(*						or None if size l < n									*)
(*		update l n a == if size l < n, l with nth element replaced by a			*)
(*	** Lemmes:																	*)
(*			 RAL_size_valid : forall l, VRAL l -> VBN (size l)					*)
(*			 RAL_cons_valid : forall a l, VRAL l -> VRAL (RAL_cons a l)			*)
(*			 RAL_tail_valid : forall a l, VRAL l -> VRAL (RAL_tail a l)			*)
(*		  RAL_discard_valid : forall l n, VRAL l -> VRAL (RAL_discard l n)		*)
(*		   RAL_update_valid : forall l n a, VRAL l -> VRAL (RAL_update l n a)	*)
(*			  RAL_cons_tail : forall a l, VRAL l -> RAL_tail (RAL_cons a l) = l	*)
(********************************************************************************)

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

Definition VRAL := valid_RAL 0.

Definition RAL_empty : RAL := [].

Local Definition RAL_safe_zero l :=
	match l with
	| [] => []
	| _ => RAL_Zero :: l
	end.

(*Local Lemma RAL_safe_zero_valid : forall (l : RAL) {n : nat},
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
Qed.*)

Section RAL_size.
Local Definition RAL_ends_One := ends_pred (fun b => exists c, b = RAL_One c).

Local Lemma RAL_ends_One_Zero : ~RAL_ends_One [RAL_Zero].
Proof.
	intro H.
	inversion_clear H.
	destruct H0.
	discriminate.
Qed.

End RAL_size.
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
	VRAL l -> VRAL (RAL_cons a l).
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
	| CRAL_Empty : CRAL RAL_empty
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
	VRAL l -> VRAL (RAL_tail l).
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
	VRAL l -> VRAL (RAL_discard l n).
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
	VRAL l -> VRAL (RAL_update l n a).
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