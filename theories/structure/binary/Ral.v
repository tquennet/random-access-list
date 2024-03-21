Require Import Arith Lists.List FunInd.
Require Import NumRep.utils.Utils.
Require Import NumRep.structure.tree.Clbt.
Require Import NumRep.numerical.binary.BinNat.
Require Import NumRep.utils.Utils.

Open Scope type_scope.
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

Variant valid_RAL_BIT : nat -> RAL_BIT -> Prop :=
	| valid_RAL_BIT_Zero : forall {n : nat}, valid_RAL_BIT n RAL_Zero
	| valid_RAL_BIT_One : forall {n : nat} (clbt : CLBT),
		valid_CLBT n clbt -> valid_RAL_BIT n (RAL_One clbt).

Inductive valid_RAL : nat -> RAL -> Prop :=
	| valid_RAL_Nil : forall {n : nat}, valid_RAL n []
	| valid_RAL_Cons : forall {n : nat} (bit : RAL_BIT) (ral : RAL),
		valid_RAL_BIT n bit -> valid_RAL (S n) ral -> valid_RAL n (bit :: ral).

Local Lemma valid_RAL_zero : forall {n : nat} (ral : RAL),
		valid_RAL (S n) ral -> valid_RAL n (RAL_Zero :: ral).
Proof.
	intros n ral H.
	apply valid_RAL_Cons;
		[apply valid_RAL_BIT_Zero | assumption].
Qed.
Local Lemma valid_RAL_one : forall {n : nat} (ral : RAL) (clbt : CLBT),
		valid_CLBT n clbt -> valid_RAL (S n) ral
		-> valid_RAL n (RAL_One clbt :: ral).
Proof.
	intros n ral clbt Hclbt Hral.
	apply valid_RAL_Cons; [apply valid_RAL_BIT_One|];
		assumption.
Qed.
Local Lemma valid_RAL_tail : forall {n : nat} (ral : RAL),
	valid_RAL n ral -> valid_RAL (S n) (tl ral).
Proof.
	intros n ral H.
	{	inversion_clear H.
	+	apply valid_RAL_Nil.
	+	assumption.
	}
Qed.

Definition VRAL := valid_RAL 0.

Definition RAL_empty : RAL := [].

(*Local Definition RAL_safe_zero l :=
	match l with
	| [] => []
	| _ => RAL_Zero :: l
	end.

Local Lemma RAL_safe_zero_valid : forall (l : RAL) {n : nat},
	valid_RAL (S n) l -> valid_RAL n (RAL_safe_zero l).
Proof.
	intros l n H.
	{	destruct l.
	+	apply valid_RAL_Nil.
	+	apply valid_RAL_zero.
		assumption.
	}
Qed.*)

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
	+	apply valid_RAL_one, valid_RAL_Nil.
		assumption.
	+	inversion_clear Hl.
		apply valid_RAL_one; assumption.
	+	inversion_clear Hl; inversion_clear H.
		apply valid_RAL_zero.
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
End RAL_cons.

Section RAL_size.

Fixpoint size (l : RAL) :=
	match l with
	| [] => []
	| RAL_Zero :: t => 0 :: (size t)
	| RAL_One _ :: t => 1 :: (size t)
	end.

Local Lemma RAL_cons_aux_inc : forall (l : RAL) (clbt : CLBT),
	size (RAL_cons_aux clbt l) = BN_inc (size l).
Proof.
	intro l.
	{	induction l as [| bit t HR]; try destruct bit.
	+	reflexivity.
	+	reflexivity.
	+	intro clbt.
		simpl.
		f_equal.
		apply HR.
	}
Qed.

Theorem RAL_cons_inc : forall (l : RAL) (a : A),
	size (RAL_cons a l) = BN_inc (size l).
Proof.
	intros l a.
	apply RAL_cons_aux_inc.
Qed.

End RAL_size.

Section RAL_canonical.

Inductive CRAL_aux (n : nat) : RAL -> Prop :=
	| CRAL_aux_Empty : CRAL_aux n []
	| CRAL_aux_Cons : forall (l : RAL) (t : CLBT),
	  CRAL_aux n l -> valid_CLBT n t -> CRAL_aux n (RAL_cons_aux t l).

Inductive CRAL : RAL -> Prop :=
	| CRAL_Empty : CRAL RAL_empty
	| CRAL_Cons : forall (l : RAL) (a : A),
		  CRAL l -> CRAL (RAL_cons a l).

Lemma CRAL_aux_equiv : forall l,
	  CRAL l <-> CRAL_aux 0 l.
Proof.
	intro l.
	{	split; intro H; induction H.
	+	apply CRAL_aux_Empty.
	+	apply CRAL_aux_Cons; [assumption| apply singleton_valid].
	+	apply CRAL_Empty.
	+	inversion_clear H0.
		apply CRAL_Cons; assumption.
	}
Qed.

Lemma CRAL_aux_One : forall n t, valid_CLBT n t -> CRAL_aux n [RAL_One t].
Proof.
	intros n t H.
	apply (CRAL_aux_Cons n []); [apply CRAL_aux_Empty| assumption].
Qed.


Definition CRAL_struct b l := CBN_struct b (size l).
Definition CRAL_st l := VRAL l /\ CRAL_struct true l = true.

Lemma CRAL_struct_equiv : forall (l : RAL),
	CRAL l <-> CRAL_st l.
Proof.
Admitted.

Fixpoint RAL_trim l :=
	match l with
	| [] => []
	| RAL_One clbt :: tl => RAL_One clbt :: (RAL_trim tl)
	| RAL_Zero :: tl => match (RAL_trim tl) with
		| [] => []
		| r => RAL_Zero :: r
		end
	end.

Functional Scheme RAL_trim_ind := Induction for RAL_trim Sort Prop.

Lemma trim_canonical : forall l, VRAL l -> CRAL (RAL_trim l).
Proof.
Admitted.

End RAL_canonical.

Fixpoint RAL_head (l : RAL) : option A :=
match l with
| [] => None
| RAL_Zero :: t => RAL_head t
| RAL_One clbt :: _ => Some (CLBT_head clbt)
end.

Section RAL_tail.

Local Fixpoint uncons (l : RAL) : option (CLBT) * RAL :=
	match l with
	| [] => (None, [])
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
		inversion_clear Hl; inversion_clear H.
		apply IHp in H0.
		rewrite e1 in H0.
		inversion_clear H0.
		assumption.
	+	apply OP_None.
	+	apply OP_Some.
		inversion_clear Hl; inversion_clear H.
		assumption.
	+	apply OP_Some.
		inversion_clear Hl; inversion_clear H.
		assumption.
	}
Qed.

Local Lemma uncons_valid_rhs : forall (l : RAL) {n : nat},
	valid_RAL n l -> valid_RAL n (snd (uncons l)).
Proof.
	intro l.
	{	functional induction (uncons l); intros n Hl; inversion_clear Hl.
	+	apply valid_RAL_Nil.
	+	inversion_clear H.
		apply uncons_valid_lhs in H0 as Hc.
		apply IHp in H0.
		rewrite e1 in Hc, H0.
		inversion_clear Hc.
		apply CLBT_left_valid in H.
		apply valid_RAL_one; assumption.
	+	inversion_clear H.
		apply valid_RAL_zero.
		apply IHp in H0.
		rewrite e1 in H0.
		assumption.
	+	apply valid_RAL_Nil.
	+	apply valid_RAL_zero.
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
	apply CRAL_struct_equiv in Hcl.
	destruct Hcl as [_ Hcl].
	{	functional induction (RAL_cons_aux clbt l); intros .
	+	reflexivity.
	+	destruct t; [compute in Hcl; discriminate|].
		reflexivity.
	+	simpl.
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

Section RAL_open.

Definition DRAL := RAL.
Definition RAL_zip := DRAL * option (@CLBT_zip A) * RAL.

(*
	Soit el et en les bits déja passés de l et n,
	on a :
		dral = rev el
		dbn = rev (en - (RAL_size el)) pour RAL_open
		dbn = rev (en ++ [1] - (RAL_size el)) pour RAL_open_borrow
*)

Fixpoint RAL_open (l : RAL) (n : BN) (dbn : DBN) (dral : DRAL) : RAL_zip :=
	match l, n with
	| [], _ => (dral, None, [])
	| RAL_Zero as bit :: tl, [] => RAL_open tl [] (0 :: dbn) (bit :: dral)
	| RAL_One t as bit :: tl, [] => (dral, Some (CLBT_open (CLBT_make_zip t) dbn), tl)
	| RAL_Zero as bit :: tl, 0 :: tn => RAL_open tl tn (0 :: dbn) (bit :: dral)
	| RAL_One _ as bit :: tl, 1 :: tn => RAL_open tl tn (0 :: dbn) (bit :: dral)
	| RAL_Zero as bit :: tl, 1 :: tn => RAL_open tl tn (1 :: dbn) (bit :: dral)
	| RAL_One _ as bit :: tl, 0 :: tn => RAL_open_borrow tl tn (1 :: dbn) (bit :: dral)
	end
with RAL_open_borrow (l : RAL) (n : BN) (dbn : DBN) (dral : DRAL) : RAL_zip :=
	match l, n with
	| [], _ => (dral, None, [])
	| _, [] => (dral, None, l)
	| RAL_One t :: tl, [1] => (dral, Some (CLBT_open (CLBT_make_zip t) dbn), tl)
	| RAL_Zero as bit :: tl, 0 :: tn => RAL_open tl tn (1 :: dbn) (bit :: dral)
	| RAL_One _ as bit :: tl, 1 :: tn => RAL_open tl tn (1 :: dbn) (bit :: dral)
	| RAL_Zero as bit :: tl, 1 :: tn => RAL_open_borrow tl tn (0 :: dbn) (bit :: dral)
	| RAL_One _ as bit :: tl, 0 :: tn => RAL_open tl tn (0 :: dbn) (bit :: dral)
	end.

End RAL_open.

Section RAL_discard.

Local Fixpoint DCLBT_to_RAL (l : RAL) (dt : DCLBT) :=
	match dt with
	| DCLBT_Root => l
	| DCLBT_Left dt _ => RAL_Zero :: DCLBT_to_RAL l dt
	| DCLBT_Right t dt => RAL_One t :: DCLBT_to_RAL l dt
	end.

Definition RAL_discard l n :=
	match RAL_open l n [] [] with
	| (l, Some (t, dt), _) => RAL_trim (RAL_cons_aux t (DCLBT_to_RAL l dt))
	| _ => []
	end.

(*Definition valid_discard_option (d : nat)
		: option (RAL_discard_zip * RAL) -> Prop :=
	option_predicate (fun '(zip, dels, l) => valid_CLBT_zip d zip
		/\ valid_RAL d dels /\ valid_RAL d l).

Local Lemma RAL_discard_split_valid : forall o (bit : RAL_BIT) (b : Bit) {d : nat},
	valid_discard_option (S d) o -> valid_RAL_BIT d bit ->
	valid_discard_option d (RAL_discard_split bit o b).
Proof.
	intros o bit b d Ho Hbit.
	{	inversion_clear Ho.
	+	apply OP_None.
	+	destruct a as [a l], a as [zip dels], zip as [t dt].
		destruct H as [Hzip H], H as [Hdels Hl].
		{	destruct b.
		+	apply OP_Some.
			{	split; [|split].
			+	apply CLBT_down_left_valid; assumption.
			+	apply valid_RAL_Cons; assumption.
			+	apply RAL_safe_zero_valid.
				assumption.
			}
		+	apply OP_Some.
			{	split; [|split].
			+	apply CLBT_down_right_valid; assumption.
			+	apply valid_RAL_Cons; assumption.
			+	destruct Hzip as [Ht hdt].
				apply CLBT_left_valid in Ht.
				apply valid_RAL_one; assumption.
			}
		}
	}
Qed.

Local Lemma RAL_discard_aux_valid : forall (l : RAL) (n : BinNat) {d : nat},
	valid_RAL d l ->
	valid_discard_option d (RAL_discard_aux l n)
	/\ valid_discard_option d (RAL_discard_borrow l n).
Proof.
	intro l.
	{	induction l as [| bit t HR]; intros n d Hl; split;
		inversion_clear Hl; simpl.
	+	apply OP_None.
	+	apply OP_None.
	+	{	destruct n as [|b tn]; [| destruct b]; destruct bit as [| clbt].
		+	apply OP_None.
		+	apply OP_None.
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	{	destruct tn.
			+	apply OP_Some.				
				{	split; split.
				+	inversion_clear H; assumption.
				+	apply valid_DCLBT_Root.
				+	apply valid_RAL_Nil.
				+	apply RAL_safe_zero_valid.
					assumption.
				}
			+	apply RAL_discard_split_valid; [|assumption].
				apply HR; assumption.
			}
		}
	+	{	destruct n as [|b tn]; [| destruct b]; destruct bit as [| clbt].
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	apply OP_Some.
			{	split; split.
			+	inversion_clear H; assumption.
			+	apply valid_DCLBT_Root.
			+	apply valid_RAL_Nil.
			+	apply RAL_safe_zero_valid.
				assumption.
			}
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		+	apply RAL_discard_split_valid; [|assumption].
			apply HR; assumption.
		}
	}
Qed.

Lemma RAL_discard_valid : forall (l : RAL) (n : BinNat),
	VRAL l -> VRAL (RAL_discard l n).
Proof.
	intros l n H.
	{	destruct n.
	+	assumption.
	+	apply (RAL_discard_aux_valid l (b :: n)) in H.
		simpl.
		{	destruct H as [H _], RAL_discard_aux.
		+	destruct p as [p r], p.
			inversion_clear H.
			destruct H0 as [_ H], H as [_ H].
			assumption.
		+	apply valid_RAL_Nil.
		}
	}
Qed.*)

End RAL_discard.

Definition RAL_lookup l n :=
	match RAL_open l n [] [] with
	| (_, Some (t, _), _) => Some (CLBT_head t)
	| _ => None
	end.

Section RAL_update.

Fixpoint RAL_plug (l : RAL) (dl : DRAL) :=
	match dl with
	| [] => l
	| b :: tdl => RAL_plug (b :: l) tdl
	end.

Definition RAL_update l n a :=
	match RAL_open l n [] [] with
	| (l, Some (_, dt), dl) => RAL_plug (RAL_One (CLBT_plug (singleton a) dt) :: l) dl
	| _ => l
	end.

(*Lemma RAL_update_valid : forall (l : RAL) (n : BinNat) (a : A),
	VRAL l -> VRAL (RAL_update l n a).
Proof.
	intros l n a H.
	{	destruct n.
	+	apply RAL_touch_head_valid.
		assumption.
	+	apply (RAL_discard_aux_valid _ (b :: n)) in H as Hd.
		destruct Hd as [Hd _].
		simpl.
		{	destruct RAL_discard_aux.
		+	destruct p as [zip r], zip as [zip dels], zip as [t dt].
			inversion_clear Hd.
			destruct H0 as [Hzip Hr], Hr as [Hdels Hr], Hzip as [Ht Hdt].
			apply (RAL_touch_head_valid _ a) in Hr.
			apply RAL_undiscard_valid; assumption.
		+	assumption.
		}
	}
Qed.*)

End RAL_update.

End RAL.
