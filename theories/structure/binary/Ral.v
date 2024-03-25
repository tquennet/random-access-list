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


Definition CRAL_struct n l := valid_RAL n l /\ CBN_struct true (size l) = true.
Definition CRAL_st l := CRAL_struct 0 l.

Lemma CRAL_aux_to_struct : forall n l, CRAL_aux n l -> CRAL_struct n l.
Proof.
	intros n l H.
	{	induction H as [| l t Hl HR Ht].
	+	split; [apply valid_RAL_Nil| reflexivity].
	+	destruct HR as [Hvl Hs].
		split; [apply RAL_cons_aux_valid; assumption|].
		enough (forall b, CBN_struct b (size (RAL_cons_aux t l)) = true); [apply H|].
		clear Hl Ht Hvl.
		{	functional induction (RAL_cons_aux t l); intro b; simpl in *.
		+	reflexivity.
		+	apply BinNat.CBN_struct_false.
			assumption.
		+	apply IHr.
			assumption.
		}
	}
Qed.


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

Lemma CRAL_aux_double : forall n l b,
		CRAL_aux (S n) (b :: l) -> CRAL_aux n (RAL_Zero :: b :: l).
Proof.
	intros n l b H.
	assert (b :: l <> []) by discriminate.
	{	induction H as [| r t Hr HR Ht].
	+	contradiction.
	+	inversion_clear Ht.
		apply (CRAL_aux_Cons n (RAL_One l0 :: r)); [|assumption].
		{	destruct r as [|bl tl].
		+	apply (CRAL_aux_Cons n []); [|assumption].
			apply CRAL_aux_Empty.
		+	apply (CRAL_aux_Cons n (RAL_Zero :: bl :: tl)); [|assumption].
			apply HR.
			discriminate.
		}
	}
Qed.

Lemma CRAL_struct_equiv_aux : forall n (l : RAL),
	CRAL_aux n l <-> CRAL_struct n l.
Proof.
	intros n l.
	{	split; intro H.
	+	apply CRAL_aux_to_struct.
		assumption.
	+	generalize dependent n.
		{	induction l as [|b tl HR]; [|destruct b]; intros n H; destruct H as [Hv Hs].
		+	apply CRAL_aux_Empty.
		+	destruct tl; [discriminate|].
			inversion_clear Hv.
			apply CRAL_aux_double, HR.
			destruct r; split; assumption.
		+	inversion_clear Hv.
			inversion_clear H.
			destruct tl; [apply CRAL_aux_One; assumption|].
			apply (CRAL_aux_Cons n (RAL_Zero :: r :: tl)); [|assumption].
			apply CRAL_aux_double, HR.
			split; assumption.
		}
	}
Qed.

Lemma CRAL_struct_equiv : forall l,
	  CRAL l <-> CRAL_st l.
Proof.
	intro l.
	{	split; intro H.
	+	apply CRAL_struct_equiv_aux, CRAL_aux_equiv.
		assumption.
	+	apply CRAL_aux_equiv, CRAL_struct_equiv_aux.
		assumption.
	}
Qed.

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

Lemma RAL_trim_canonical : forall l, VRAL l -> CRAL (RAL_trim l).
Proof.
	intros l H.
	apply CRAL_struct_equiv.
	enough (He : forall n, valid_RAL n l -> CRAL_struct n (RAL_trim l));
		[apply He; assumption|].
	clear H.
	{	functional induction (RAL_trim l); intros n H.
	+	split; [apply valid_RAL_Nil| reflexivity].
	+	split; [apply valid_RAL_Nil| reflexivity].
	+	inversion_clear H.
		apply IHl0 in H1.
		rewrite e1 in H1.
		destruct H1 as [Hv Hs].
		split; [apply valid_RAL_zero; assumption|destruct y0; assumption].
	+	inversion_clear H.
		inversion_clear H0.
		apply IHl0 in H1.
		destruct H1 as [Hv Hs].
		split; [apply valid_RAL_one|]; assumption.
	}
Qed.

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

Inductive valid_DRAL : nat -> DRAL -> Prop :=
	| valid_DRAL_Nil : valid_DRAL 0 []
	| valid_DRAL_Cons : forall (n : nat) (b : RAL_BIT) (dl : DRAL),
		valid_RAL_BIT n b -> valid_DRAL n dl -> valid_DRAL (S n) (b :: dl).

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
	| _ :: tl, [] => (dral, None, tl)
	| RAL_One t :: tl, [1] => (dral, Some (CLBT_open (CLBT_make_zip t) dbn), tl)
	| RAL_Zero as bit :: tl, 0 :: tn => RAL_open tl tn (1 :: dbn) (bit :: dral)
	| RAL_One _ as bit :: tl, 1 :: tn => RAL_open tl tn (1 :: dbn) (bit :: dral)
	| RAL_Zero as bit :: tl, 1 :: tn => RAL_open_borrow tl tn (0 :: dbn) (bit :: dral)
	| RAL_One _ as bit :: tl, 0 :: tn => RAL_open tl tn (0 :: dbn) (bit :: dral)
	end.

Lemma RAL_open_valid : forall l n dbn dl d rdl rcz rl,
		(rdl, rcz, rl) = RAL_open l n dbn dl \/ (rdl, rcz, rl) = RAL_open_borrow l n dbn dl ->
		valid_RAL d l -> length dbn = d -> valid_DRAL d dl ->
		exists rd, valid_RAL (S rd) rl /\ valid_DRAL rd rdl /\ option_predicate (valid_CLBT_zip rd 0) rcz.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; intro n; [|destruct bl; (destruct n as [|bn tn]; [|destruct bn])];
			intros dbn dral d rdl rcz rl Hr Hl Hdbn Hdl; simpl in *;
			destruct Hr as [Hr|Hr];
			assert (Hsdbn : forall b, length (b :: dbn) = S d) by (simpl; rewrite Hdbn; reflexivity);
			inversion_clear Hl.
	+	inversion_clear Hr.
		exists d.
		{	split; [|split].
		+	apply valid_RAL_Nil.
		+	assumption.
		+	apply OP_None.
		}
	+	inversion_clear Hr.
		exists d.
		{	split; [|split].
		+	apply valid_RAL_Nil.
		+	assumption.
		+	apply OP_None.
		}
	+	apply (valid_DRAL_Cons _ RAL_Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	inversion_clear Hr.
		exists d.
		split; [|split]; [assumption|assumption|apply OP_None].
	+	apply (valid_DRAL_Cons _ RAL_Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	apply (valid_DRAL_Cons _ RAL_Zero) in Hdl; [|assumption].
		specialize (Hsdbn 1).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	apply (valid_DRAL_Cons _ RAL_Zero) in Hdl; [|assumption].
		specialize (Hsdbn 1).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	apply (valid_DRAL_Cons _ RAL_Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_intror Hr)); assumption.
	+	inversion_clear Hr.
		exists d.
		{	split; [|split].
		+	assumption.
		+	assumption.
		+	apply OP_Some.
			apply CLBT_open_valid.
			rewrite Hdbn.
			apply CLBT_make_zip_valid.
			inversion_clear H.
			assumption.
		}
	+	inversion_clear Hr.
		exists d.
		split; [|split]; [assumption|assumption|apply OP_None].
	+	apply (valid_DRAL_Cons _ (RAL_One c)) in Hdl; [|assumption].
		specialize (Hsdbn 1).
		apply (HR _ _ _ (S d) _ _ _  (or_intror Hr)); assumption.
	+	apply (valid_DRAL_Cons _ (RAL_One c)) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _  (or_introl Hr)); assumption.
	+	apply (valid_DRAL_Cons _ (RAL_One c)) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _  (or_introl Hr)); assumption.
	+	{	destruct tn.
		+	inversion_clear Hr.
			exists d.
			split; [|split]; [assumption|assumption|].
			apply OP_Some.
			apply CLBT_open_valid.
			rewrite Hdbn.
			apply CLBT_make_zip_valid.
			inversion_clear H.
			assumption.
		+	apply (valid_DRAL_Cons _ (RAL_One c)) in Hdl; [|assumption].
			specialize (Hsdbn 1).
			apply (HR _ _ _ (S d) _ _ _  (or_introl Hr)); assumption.
		}
	}
Qed.

Lemma RAL_open_valid_init : forall l n rdl rcz rl,
	  (rdl, rcz, rl) = RAL_open l n [] [] -> VRAL l ->
	  exists d, valid_RAL (S d) rl /\ valid_DRAL d rdl /\ option_predicate (valid_CLBT_zip d 0) rcz.
Proof.
	intros l n rdl rcz rl Hr Hv.
	{	apply (RAL_open_valid _ _ _ _ 0 _ _ _ (or_introl Hr)).
	+	assumption.
	+	reflexivity.
	+	apply valid_DRAL_Nil.
	}
Qed.

End RAL_open.

Section RAL_discard.

Local Fixpoint DCLBT_to_RAL (l : RAL) (dt : DCLBT) :=
	match dt with
	| DCLBT_Root => (RAL_Zero :: l)
	| DCLBT_Left dt _ => RAL_Zero :: DCLBT_to_RAL l dt
	| DCLBT_Right t dt => RAL_One t :: DCLBT_to_RAL l dt
	end.

Lemma DCLBT_to_RAL_valid : forall l dt d n,
		valid_RAL (S d) l -> valid_DCLBT d n dt ->
		valid_RAL n (DCLBT_to_RAL l dt).
Proof.
	intros l dt d.
	{	induction dt as [|dt HR t| t dt HR]; intros n Hl Hdt; simpl in *.
	+	inversion Hdt.
		rewrite <- H0.
		apply valid_RAL_zero.
		assumption.
	+	inversion_clear Hdt.
		apply valid_RAL_zero.
		apply HR; assumption.
	+	inversion_clear Hdt.
		apply valid_RAL_one; [assumption|].
		apply HR; assumption.
	}
Qed.

Definition RAL_discard l n :=
	match RAL_open l n [] [] with
	| (_, Some (t, dt), l) => RAL_trim (RAL_cons_aux t (DCLBT_to_RAL l dt))
	| _ => []
	end.

Lemma RAL_discard_canonical : forall l n,
		VRAL l -> CRAL (RAL_discard l n).
Proof.
	intros l n H.
	unfold RAL_discard.
	remember (RAL_open l n [] []) as r eqn:Hr.
	destruct r as [r rl], r as [rdl rzip].
	assert (Hopen : exists d, valid_RAL (S d) rl /\ valid_DRAL d rdl
						 /\ option_predicate (valid_CLBT_zip d 0) rzip);
		[apply (RAL_open_valid_init _ _ _ _ _ Hr H)|].
	destruct rzip as [rzip|]; [|apply CRAL_Empty].
	destruct rzip as [t dt].
	destruct Hopen as [d Hopen], Hopen as [Hrl Hopen], Hopen as [Hrdl Hzip].
	inversion_clear Hzip.
	inversion_clear H0.
	apply RAL_trim_canonical.
	apply RAL_cons_aux_valid; [|assumption].
	apply (DCLBT_to_RAL_valid _ _ d); assumption.
Qed.
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

Lemma RAL_plug_valid : forall l dl n,
		valid_RAL n l -> valid_DRAL n dl ->
		VRAL (RAL_plug l dl).
Proof.
	intros l dl n Hl Hdl.
	revert l n Hl Hdl.
	{	induction dl as [|b tdl HR]; intros l n Hl Hdl; simpl in *.
	+	inversion Hdl.
		rewrite <-H in Hl.
		assumption.
	+	inversion Hdl.
		rewrite <-H1 in *.
		apply (HR _ n0); [|assumption].
		apply valid_RAL_Cons; assumption.
	}
Qed.

Definition RAL_update l n a :=
	match RAL_open l n [] [] with
	| (dl, Some (_, dt), l) => RAL_plug (RAL_One (CLBT_plug (singleton a) dt) :: l) dl
	| _ => l
	end.

Lemma RAL_update_valid : forall l n a, VRAL l -> VRAL (RAL_update l n a).
Proof.
	intros l n a H.
	unfold RAL_update.
	remember (RAL_open l n [] []) as r eqn:Hr.
	destruct r as [r rl], r as [rdl rzip].
	assert (Hopen : exists d, valid_RAL (S d) rl /\ valid_DRAL d rdl
						 /\ option_predicate (valid_CLBT_zip d 0) rzip);
		[apply (RAL_open_valid_init _ _ _ _ _ Hr H)|].
	destruct rzip as [rzip|]; [|assumption].
	destruct rzip as [t dt].
	destruct Hopen as [d Hopen], Hopen as [Hrl Hopen], Hopen as [Hrdl Hzip].
	inversion_clear Hzip.
	inversion_clear H0.
	apply (RAL_plug_valid _ _ d); [|assumption].
	apply valid_RAL_one; [|assumption].
	apply (CLBT_plug_valid _ _ _ 0);
		[apply singleton_valid|assumption].
Qed.

End RAL_update.

End RAL.
