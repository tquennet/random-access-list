Require Import Arith Lists.List FunInd.
Require structure.tree.Clbt numerical.binary.BinNat.
Require Import NumRep.utils.Utils.
Module CLBT := structure.tree.Clbt.
Module BinNat := numerical.binary.BinNat.
Import BinNat.Notations.

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

Notation CLBT := (@CLBT.t A).

Variant BIT :=
	| Zero : BIT
	| One : CLBT -> BIT.

Definition t := list BIT.

Variant is_valid_BIT : nat -> BIT -> Prop :=
	| valid_BIT_Zero : forall {n : nat}, is_valid_BIT n Zero
	| valid_BIT_One : forall {n : nat} (clbt : CLBT.t),
		CLBT.is_valid n clbt -> is_valid_BIT n (One clbt).

Inductive valid : nat -> t -> Prop :=
	| valid_Nil : forall {n : nat}, valid n []
	| valid_Cons : forall {n : nat} (bit : BIT) (ral : t),
		is_valid_BIT n bit -> valid (S n) ral -> valid n (bit :: ral).

Local Lemma valid_zero : forall {n : nat} (ral : t),
		valid (S n) ral -> valid n (Zero :: ral).
Proof.
	intros n ral H.
	apply valid_Cons;
		[apply valid_BIT_Zero | assumption].
Qed.
Local Lemma valid_one : forall {n : nat} (ral : t) (clbt : CLBT.t),
		CLBT.is_valid n clbt -> valid (S n) ral
		-> valid n (One clbt :: ral).
Proof.
	intros n ral clbt Hclbt Hral.
	apply valid_Cons; [apply valid_BIT_One|];
		assumption.
Qed.
Local Lemma valid_tail : forall {n : nat} (ral : t),
	valid n ral -> valid (S n) (tl ral).
Proof.
	intros n ral H.
	{	inversion_clear H.
	+	apply valid_Nil.
	+	assumption.
	}
Qed.

Definition is_valid := valid 0.

Definition empty : t := [].

Section cons.

Local Fixpoint cons_aux (clbt : CLBT.t) (l : t) : t :=
	match l with
	| [] => [One clbt]
	| Zero :: t => One clbt :: t
	| One e :: t => Zero :: cons_aux (CLBT.Node e clbt) t
	end.

Functional Scheme cons_aux_ind := Induction for cons_aux Sort Prop.

Lemma cons_aux_valid : forall  (l : t) (clbt : CLBT) {n : nat},
	valid n l -> CLBT.is_valid n clbt ->
	valid n (cons_aux clbt l).
Proof.
	intros clbt l.
	{	functional induction (cons_aux l clbt); intros n Hl Hclbt.
	+	apply valid_one, valid_Nil.
		assumption.
	+	inversion_clear Hl.
		apply valid_one; assumption.
	+	inversion_clear Hl; inversion_clear H.
		apply valid_zero.
		apply IHt0; [assumption|].
		apply CLBT.valid_Node; assumption.
	}
Qed.

Definition cons (a : A) (l : t) := cons_aux (CLBT.singleton a) l.

Lemma cons_valid : forall (a : A) (l : t),
	is_valid l -> is_valid (cons a l).
Proof.
	intros a l H.
	{	apply cons_aux_valid.
	+	exact H.
	+	apply CLBT.singleton_valid.
	}
Qed.

Local Lemma cons_aux_non_empty : forall (l : t) (clbt : CLBT),
	exists b tl, b :: tl = cons_aux clbt l.
Proof.
	intros l clbt.
	{	destruct l as [|b tl]; [|destruct b].
	+	exists (One clbt), []; reflexivity.
	+	exists (One clbt), tl; reflexivity.
	+	exists Zero, (cons_aux (CLBT.Node t0 clbt) tl).
		reflexivity.
	}
Qed.

End cons.

Section size.

Fixpoint size (l : t) : BinNat.t :=
	match l with
	| [] => []
	| Zero :: t => 0 :: (size t)
	| One _ :: t => 1 :: (size t)
	end.

Local Lemma cons_aux_inc : forall (l : t) (clbt : CLBT),
	size (cons_aux clbt l) = BinNat.inc (size l).
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

Theorem cons_inc : forall (l : t) (a : A),
	size (cons a l) = BinNat.inc (size l).
Proof.
	intros l a.
	apply cons_aux_inc.
Qed.

End size.

Section canonical.

Inductive is_canonical_aux (n : nat) : t -> Prop :=
	| is_canonical_aux_Empty : is_canonical_aux n []
	| is_canonical_aux_Cons : forall (l : t) (t : CLBT),
	  is_canonical_aux n l -> CLBT.is_valid n t -> is_canonical_aux n (cons_aux t l).

Inductive is_canonical : t -> Prop :=
	| is_canonical_Empty : is_canonical empty
	| is_canonical_Cons : forall (l : t) (a : A),
		  is_canonical l -> is_canonical (cons a l).


Definition is_canonical_struct n l := valid n l /\ BinNat.is_canonical_struct (size l).

Lemma is_canonical_aux_to_struct : forall n l, is_canonical_aux n l -> is_canonical_struct n l.
Proof.
	intros n l H.
	{	induction H as [| l t Hl HR Ht].
	+	split; [apply valid_Nil| reflexivity].
	+	destruct HR as [Hvl Hs].
		split; [apply cons_aux_valid; assumption|].
		enough (forall b, BinNat.is_canonical_struct_fix b (size (cons_aux t l)) = true);
			[apply H|].
		clear Hl Ht Hvl.
		{	functional induction (cons_aux t l); intro b; simpl in *.
		+	reflexivity.
		+	apply BinNat.is_canonical_struct_false.
			assumption.
		+	apply IHt0.
			assumption.
		}
	}
Qed.


Lemma is_canonical_aux_equiv : forall l,
	  is_canonical l <-> is_canonical_aux 0 l.
Proof.
	intro l.
	{	split; intro H; induction H.
	+	apply is_canonical_aux_Empty.
	+	apply is_canonical_aux_Cons; [assumption| apply CLBT.singleton_valid].
	+	apply is_canonical_Empty.
	+	inversion_clear H0.
		apply is_canonical_Cons; assumption.
	}
Qed.

Lemma is_canonical_aux_One : forall n t, CLBT.is_valid n t -> is_canonical_aux n [One t].
Proof.
	intros n t H.
	apply (is_canonical_aux_Cons n []); [apply is_canonical_aux_Empty| assumption].
Qed.

Lemma is_canonical_aux_double : forall n l b,
		is_canonical_aux (S n) (b :: l) -> is_canonical_aux n (Zero :: b :: l).
Proof.
	intros n l b H.
	assert (b :: l <> []) by discriminate.
	{	induction H as [| r t Hr HR Ht].
	+	contradiction.
	+	inversion_clear Ht.
		apply (is_canonical_aux_Cons n (One l0 :: r)); [|assumption].
		{	destruct r as [|bl tl].
		+	apply (is_canonical_aux_Cons n []); [|assumption].
			apply is_canonical_aux_Empty.
		+	apply (is_canonical_aux_Cons n (Zero :: bl :: tl)); [|assumption].
			apply HR.
			discriminate.
		}
	}
Qed.

Lemma is_canonical_struct_equiv_aux : forall n (l : t),
	is_canonical_aux n l <-> is_canonical_struct n l.
Proof.
	intros n l.
	{	split; intro H.
	+	apply is_canonical_aux_to_struct.
		assumption.
	+	generalize dependent n.
		{	induction l as [|b tl HR]; [|destruct b]; intros n H; destruct H as [Hv Hs].
		+	apply is_canonical_aux_Empty.
		+	destruct tl; [discriminate|].
			inversion_clear Hv.
			apply is_canonical_aux_double, HR.
			destruct b; split; assumption.
		+	inversion_clear Hv.
			inversion_clear H.
			destruct tl; [apply is_canonical_aux_One; assumption|].
			apply (is_canonical_aux_Cons n (Zero :: b :: tl)); [|assumption].
			apply is_canonical_aux_double, HR.
			split; assumption.
		}
	}
Qed.

Lemma is_canonical_struct_equiv : forall (l : t),
	  is_canonical l <-> is_canonical_struct 0 l.
Proof.
	intro l.
	{	split; intro H.
	+	apply is_canonical_struct_equiv_aux, is_canonical_aux_equiv.
		assumption.
	+	apply is_canonical_aux_equiv, is_canonical_struct_equiv_aux.
		assumption.
	}
Qed.

Fixpoint trim l :=
	match l with
	| [] => []
	| One clbt :: tl => One clbt :: (trim tl)
	| Zero :: tl => match (trim tl) with
		| [] => []
		| r => Zero :: r
		end
	end.

Functional Scheme trim_ind := Induction for trim Sort Prop.

Lemma trim_canonical : forall l, is_valid l -> is_canonical (trim l).
Proof.
	intros l H.
	apply is_canonical_struct_equiv.
	enough (He : forall n, valid n l -> is_canonical_struct n (trim l));
		[apply He; assumption|].
	clear H.
	{	functional induction (trim l); intros n H.
	+	split; [apply valid_Nil| reflexivity].
	+	split; [apply valid_Nil| reflexivity].
	+	inversion_clear H.
		apply IHl0 in H1.
		rewrite e1 in H1.
		destruct H1 as [Hv Hs].
		split; [apply valid_zero; assumption|destruct y0; assumption].
	+	inversion_clear H.
		inversion_clear H0.
		apply IHl0 in H1.
		destruct H1 as [Hv Hs].
		split; [apply valid_one|]; assumption.
	}
Qed.

End canonical.

Fixpoint head (l : t) : option A :=
match l with
| [] => None
| Zero :: t => head t
| One clbt :: _ => Some (CLBT.head clbt)
end.

Section tail.

Local Fixpoint uncons (l : t) : option (CLBT) * t :=
	match l with
	| [] => (None, [])
	| [One clbt] => (Some clbt, [])
	| One clbt :: t => (Some clbt, Zero :: t)
	| Zero :: t => let (clbt, r) := uncons t in
		match clbt with
		| None => (None, Zero :: r)
		| Some clbt => (Some (CLBT.right clbt), One (CLBT.left clbt) :: r)
		end
	end.

Functional Scheme uncons_ind := Induction for uncons Sort Prop.

Local Lemma uncons_valid_lhs : forall (l : t) {n : nat},
	valid n l -> option_predicate (CLBT.is_valid n) (fst (uncons l)).
Proof.
	intro l.
	{	functional induction (uncons l); intros n Hl.
	+ apply OP_None.
	+	apply OP_Some.
		apply CLBT.right_valid.
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

Local Lemma uncons_valid_rhs : forall (l : t) {n : nat},
	valid n l -> valid n (snd (uncons l)).
Proof.
	intro l.
	{	functional induction (uncons l); intros n Hl; inversion_clear Hl.
	+	apply valid_Nil.
	+	inversion_clear H.
		apply uncons_valid_lhs in H0 as Hc.
		apply IHp in H0.
		rewrite e1 in Hc, H0.
		inversion_clear Hc.
		apply CLBT.left_valid in H.
		apply valid_one; assumption.
	+	inversion_clear H.
		apply valid_zero.
		apply IHp in H0.
		rewrite e1 in H0.
		assumption.
	+	apply valid_Nil.
	+	apply valid_zero.
		assumption.
	}
Qed.

Definition tail (l : t) : t := snd (uncons l).

Lemma tail_valid : forall (l : t),
	is_valid l -> is_valid (tail l).
Proof.
	intros l H.
	apply uncons_valid_rhs.
	assumption.
Qed.

Lemma cons_uncons : forall (l : t) (clbt : CLBT),
	is_canonical l -> uncons (cons_aux clbt l) = (Some clbt, l).
Proof.
	intros l clbt Hcl.
	apply is_canonical_struct_equiv in Hcl.
	destruct Hcl as [_ Hcl].
	{	functional induction (cons_aux clbt l); intros .
	+	reflexivity.
	+	destruct t0; [compute in Hcl; discriminate|].
		reflexivity.
	+	simpl.
		apply IHt0 in Hcl.
		rewrite Hcl.
		reflexivity.
	}
Qed.

Lemma cons_tail : forall (l : t) (a : A),
	is_canonical l -> tail (cons a l) = l.
Proof.
	intros l a H.
	pose proof (HR := cons_uncons _ (CLBT.singleton a) H).
	unfold tail, cons.
	rewrite HR.
	reflexivity.
Qed.

End tail.

Section open.

Definition dt := t.
Definition zip := dt * option (@CLBT.zip A) * t.

Inductive valid_dt : nat -> dt -> Prop :=
	| valid_DNil : valid_dt 0 []
	| valid_DCons : forall (n : nat) (b : BIT) (dl : dt),
		is_valid_BIT n b -> valid_dt n dl -> valid_dt (S n) (b :: dl).

(*
	Soit el et en les bits déja passés de l et n,
	on a :
		dral = rev el
		dbn = rev (en - (size el)) pour open
		dbn = rev (en ++ [1] - (size el)) pour open_borrow
*)

Fixpoint open (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) : zip :=
	match l, n with
	| [], _ => (dral, None, [])
	| Zero as bit :: tl, [] => open tl [] (0 :: dbn) (bit :: dral)
	| One t as bit :: tl, [] => (dral, Some (CLBT.open (CLBT.make_zip t) dbn), tl)
	| Zero as bit :: tl, 0 :: tn => open tl tn (0 :: dbn) (bit :: dral)
	| One _ as bit :: tl, 1 :: tn => open tl tn (0 :: dbn) (bit :: dral)
	| Zero as bit :: tl, 1 :: tn => open tl tn (1 :: dbn) (bit :: dral)
	| One _ as bit :: tl, 0 :: tn => open_borrow tl tn (1 :: dbn) (bit :: dral)
	end
with open_borrow (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) : zip :=
	match l, n with
	| [], _ => (dral, None, [])
	| _ as bit :: tl, [] => open_borrow tl [] (0 :: dbn) (bit :: dral)
	| One t :: tl, [1] => (dral, Some (CLBT.open (CLBT.make_zip t) dbn), tl)
	| Zero as bit :: tl, 0 :: tn | One _ as bit :: tl, 1 :: tn
		=> open_borrow tl tn (1 :: dbn) (bit :: dral)
	| One _ as bit :: tl, 0 :: tn => open_borrow tl tn (0 :: dbn) (bit :: dral)
	| Zero as bit :: tl, 1 :: tn => open tl tn (0 :: dbn) (bit :: dral)
	end.

Lemma open_borrow_O : forall l dbn dl, exists rl rdl,
		open_borrow l [] dbn dl = (rdl, None, rl).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros dbn dl.
	+	exists [], dl.
		reflexivity.
	+	apply HR.
	+	apply HR.
	}
Qed.

Lemma open_valid : forall l n dbn dl d rdl rcz rl,
		(rdl, rcz, rl) = open l n dbn dl \/ (rdl, rcz, rl) = open_borrow l n dbn dl ->
		valid d l -> length dbn = d -> valid_dt d dl ->
		exists rd, valid (S rd) rl /\ valid_dt rd rdl
			  /\ option_predicate (CLBT.is_valid_zip rd 0) rcz.
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
		+	apply valid_Nil.
		+	assumption.
		+	apply OP_None.
		}
	+	inversion_clear Hr.
		exists d.
		{	split; [|split].
		+	apply valid_Nil.
		+	assumption.
		+	apply OP_None.
		}
	+	apply (valid_DCons _ Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	apply (valid_DCons _ Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_intror Hr)); assumption.
	+	apply (valid_DCons _ Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	apply (valid_DCons _ Zero) in Hdl; [|assumption].
		specialize (Hsdbn 1).
		apply (HR _ _ _ (S d) _ _ _ (or_intror Hr)); assumption.
	+	apply (valid_DCons _ Zero) in Hdl; [|assumption].
		specialize (Hsdbn 1).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	apply (valid_DCons _ Zero) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_introl Hr)); assumption.
	+	inversion_clear Hr.
		exists d.
		{	split; [|split].
		+	assumption.
		+	assumption.
		+	apply OP_Some.
			apply CLBT.open_valid.
			rewrite Hdbn.
			apply CLBT.make_zip_valid.
			inversion_clear H.
			assumption.
		}
	+	apply (valid_DCons _ (One t0)) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _ (or_intror Hr)); assumption.
	+	apply (valid_DCons _ (One t0)) in Hdl; [|assumption].
		specialize (Hsdbn 1).
		apply (HR _ _ _ (S d) _ _ _  (or_intror Hr)); assumption.
	+	apply (valid_DCons _ (One t0)) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _  (or_intror Hr)); assumption.
	+	apply (valid_DCons _ (One t0)) in Hdl; [|assumption].
		specialize (Hsdbn 0).
		apply (HR _ _ _ (S d) _ _ _  (or_introl Hr)); assumption.
	+	{	destruct tn.
		+	inversion_clear Hr.
			exists d.
			split; [|split]; [assumption|assumption|].
			apply OP_Some.
			apply CLBT.open_valid.
			rewrite Hdbn.
			apply CLBT.make_zip_valid.
			inversion_clear H.
			assumption.
		+	apply (valid_DCons _ (One t0)) in Hdl; [|assumption].
			specialize (Hsdbn 1).
			apply (HR _ _ _ (S d) _ _ _  (or_intror Hr)); assumption.
		}
	}
Qed.

Lemma open_valid_init : forall l n rdl rcz rl,
	  (rdl, rcz, rl) = open l n [] [] -> is_valid l ->
	  exists d, valid (S d) rl /\ valid_dt d rdl /\ option_predicate (CLBT.is_valid_zip d 0) rcz.
Proof.
	intros l n rdl rcz rl Hr Hv.
	{	apply (open_valid _ _ _ _ 0 _ _ _ (or_introl Hr)).
	+	assumption.
	+	reflexivity.
	+	apply valid_DNil.
	}
Qed.


Lemma open_None : forall (l : t) (n : BinNat.t) rdl rl,
		open l n [] [] = (rdl, None, rl) -> rdl = rev l /\ rl = [].
Proof.
	intros l n rdl rl H.
	enough (He : forall n dn dl rdl rl,
				 (open l n dn dl = (rdl, None, rl) -> rdl = rev l ++ dl /\ rl = [])
		   /\ (open_borrow l n dn dl = (rdl, None, rl) -> rdl = rev l ++ dl /\ rl = []));
	  [apply He in H; rewrite app_nil_r in H; assumption|].
	clear n rdl rl H.
	{	induction l as [|bl tl HR]; [|destruct bl]; intro n; destruct n as [|bn tn];
			intros dn dl rdl rl; split; intro He; simpl in *; try discriminate.
	+	inversion_clear He.
		split; reflexivity.
	+	inversion_clear He.
		split; reflexivity.
	+	inversion_clear He.
		split; reflexivity.
	+	inversion_clear He.
		split; reflexivity.
	+	apply HR in He.
		rewrite <- app_assoc.
		assumption.
	+	apply HR in He.
		rewrite <- app_assoc.
		assumption.
	+	destruct bn;
			apply HR in He;
			rewrite <- app_assoc;
			assumption.
	+	destruct bn;
			apply HR in He;
			rewrite <- app_assoc;
			assumption.
	+	apply HR in He.
		rewrite <- app_assoc.
		assumption.
	+	destruct bn;
			apply HR in He;
			rewrite <- app_assoc;
			assumption.
	+	destruct bn; [|destruct tn]; [|inversion_clear He|];
			apply HR in He;
			rewrite <- app_assoc;
			assumption.
	}
Qed.

End open.

Section drop.

Local Fixpoint DCLBT_to_RAL (l : t) (dt : CLBT.dt) :=
	match dt with
	| CLBT.DRoot => (Zero :: l)
	| CLBT.DLeft dt _ => Zero :: DCLBT_to_RAL l dt
	| CLBT.DRight t dt => One t :: DCLBT_to_RAL l dt
	end.

Lemma DCLBT_to_RAL_valid : forall l dt d n,
		valid (S d) l -> CLBT.is_valid_d d n dt ->
		valid n (DCLBT_to_RAL l dt).
Proof.
	intros l dt d.
	{	induction dt as [|dt HR t| t dt HR]; intros n Hl Hdt; simpl in *.
	+	inversion Hdt.
		rewrite <- H0.
		apply valid_zero.
		assumption.
	+	inversion_clear Hdt.
		apply valid_zero.
		apply HR; assumption.
	+	inversion_clear Hdt.
		apply valid_one; [assumption|].
		apply HR; assumption.
	}
Qed.

Definition drop l n :=
	match open l n [] [] with
	| (_, Some (t, dt), l) => trim (cons_aux t (DCLBT_to_RAL l dt))
	| _ => []
	end.

Lemma drop_canonical : forall l n,
		is_valid l -> is_canonical (drop l n).
Proof.
	intros l n H.
	unfold drop.
	remember (open l n [] []) as r eqn:Hr.
	destruct r as [r rl], r as [rdl rzip].
	assert (Hopen : exists d, valid (S d) rl /\ valid_dt d rdl
						 /\ option_predicate (CLBT.is_valid_zip d 0) rzip);
		[apply (open_valid_init _ _ _ _ _ Hr H)|].
	destruct rzip as [rzip|]; [|apply is_canonical_Empty].
	destruct rzip as [t dt].
	destruct Hopen as [d Hopen], Hopen as [Hrl Hopen], Hopen as [Hrdl Hzip].
	inversion_clear Hzip.
	inversion_clear H0.
	apply trim_canonical.
	apply cons_aux_valid; [|assumption].
	apply (DCLBT_to_RAL_valid _ _ d); assumption.
Qed.
End drop.

Definition lookup l n :=
	match open l n [] [] with
	| (_, Some (t, _), _) => Some (CLBT.head t)
	| _ => None
	end.

Section update.

Fixpoint plug (l : t) (dl : dt) :=
	match dl with
	| [] => l
	| b :: tdl => plug (b :: l) tdl
	end.

Lemma plug_valid : forall l dl n,
		valid n l -> valid_dt n dl ->
		is_valid (plug l dl).
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
		apply valid_Cons; assumption.
	}
Qed.

Definition update l n a :=
	match open l n [] [] with
	| (dl, Some (_, dt), l) => plug (One (CLBT.plug (CLBT.singleton a) dt) :: l) dl
	| _ => l
	end.

Lemma update_valid : forall l n a, is_valid l -> is_valid (update l n a).
Proof.
	intros l n a H.
	unfold update.
	remember (open l n [] []) as r eqn:Hr.
	destruct r as [r rl], r as [rdl rzip].
	assert (Hopen : exists d, valid (S d) rl /\ valid_dt d rdl
						 /\ option_predicate (CLBT.is_valid_zip d 0) rzip);
		[apply (open_valid_init _ _ _ _ _ Hr H)|].
	destruct rzip as [rzip|]; [|assumption].
	destruct rzip as [t dt].
	destruct Hopen as [d Hopen], Hopen as [Hrl Hopen], Hopen as [Hrdl Hzip].
	inversion_clear Hzip.
	inversion_clear H0.
	apply (plug_valid _ _ d); [|assumption].
	apply valid_one; [|assumption].
	apply (CLBT.plug_valid _ _ _ 0);
		[apply CLBT.singleton_valid|assumption].
Qed.

End update.

Section create.

Fixpoint create_aux n t :=
	match n with
	| [] => []
	| 0 :: tn => Zero :: create_aux tn (CLBT.Node t t)
	| 1 :: tn => One t :: create_aux tn (CLBT.Node t t)
	end.

Functional Scheme create_aux_ind := Induction for create_aux Sort Prop.

Definition create n a := create_aux n (CLBT.singleton a).

Lemma create_valid : forall n a, is_valid (create n a).
Proof.
	intros n a.
	set (t := CLBT.singleton a).
	enough (forall d, CLBT.is_valid d t -> valid d (create_aux n (CLBT.singleton a)));
		[apply H, CLBT.singleton_valid|].
	{	functional induction (create_aux n (CLBT.singleton a));
			intros d Ht; simpl in *.
	+	apply valid_Nil.
	+	apply valid_zero.
		apply IHl.
		apply CLBT.valid_Node; assumption.
	+	apply valid_one; [assumption|].
		apply IHl.
		apply CLBT.valid_Node; assumption.
	}
Qed.

End create.

End RAL.
