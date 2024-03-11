Require Import Lists.List FunInd.
Require Import Init.Nat.
Import ListNotations.

Declare Scope bin_nat_scope.
Open Scope bin_nat_scope.

(********************************************************************************)
(*	Notations are defined in bin_nat_scope.										*)
(*	BinNat == the type of binazy numbers.										*)
(*			 VBN == a predicate identifying valid BinNat						*)
(*					all operations are defined only for valid BinNat			*)
(*		BN_zero  == the BN representing 0										*)
(*		BN_inc n == the successor of n											*)
(*	**	Unary operator:															*)
(*		BN_to_nat n == n as native coq nat									*)
(*			   BN_dec n == the predecessor of n									*)
(*	**	Binary operators:														*)
(*		 sub n m, n - m == the difference between n and m						*)
(*	** Lemmes:																	*)
(*		BN_inc_valid : forall l, VBN l -> VBN (BN_inc l)						*)
(*		BN_dec_valid : forall l, VBN l -> VBN (BN_dec l)						*)
(*		BN_inc_dec : forall l, VBN l -> VBN d n -> dec (inc n) = n				*)
(********************************************************************************)

Variant Bit := Zero | One.
Definition BinNat := list Bit.

Notation "0" := Zero.
Notation "1" := One.

Fixpoint BN_to_nat n : nat :=
	match n with
	| [] => O
	| 0 :: t => 2 * (BN_to_nat t)
	| 1 :: t => S (2 * BN_to_nat t)
	end.

Local Definition BN_safe_zero n :=
	match n with
	| [] => []
	| _ => 0 :: n
	end.
Local Definition BN_safe_bit b n :=
	match b with
	| 0 => BN_safe_zero n
	| 1 => 1 :: n
	end.
Local Definition BN_add_bit o b :=
	match o with
	| None => None
	| Some n => Some (BN_safe_bit b n)
	end.

(*Local Lemma BN_safe_bit_valid : forall (b : Bit) (n : BinNat) {d : nat},
	valid_BinNat (S d) n \/ n = [] ->
	valid_BinNat d (BN_safe_bit b n) \/ BN_safe_bit b n = [].
Proof.
	intros b n d H.
	{	destruct H; inversion_clear H.
	+	left.
		destruct b; apply valid_BinNat_Cons, valid_BinNat_Top.
	+	left.
		destruct b; repeat apply valid_BinNat_Cons; assumption.
	+	{	destruct b.
		+	right; reflexivity.
		+	left; apply valid_BinNat_Top.
		}
	}
Qed.

Definition BN_zero : BinNat := [].

Lemma BN_zero_valid : VBN BN_zero.
Proof.
	apply valid_BinNat_Nil.
Qed.*)

Fixpoint BN_inc n :=
	match n with
	| [] => [1]
	| 0 :: t => 1 :: t
	| 1 :: t => 0 :: BN_inc t
	end.


Functional Scheme BN_inc_ind := Induction for BN_inc Sort Prop.

Lemma BN_inc_S : forall (n : BinNat),
	BN_to_nat (BN_inc n) = S (BN_to_nat n).
Proof.
	intro n.
	{	induction n as [| b tn HR]; [|destruct b]; simpl.
	+	reflexivity.
	+	reflexivity.
	+	rewrite !PeanoNat.Nat.add_0_r, HR.
		rewrite plus_Sn_m, <- plus_n_Sm.
		reflexivity.
	}
Qed.

Inductive CBN : BinNat -> Prop :=
	| CBN_0 : CBN []
	| CBN_inc : forall (n : BinNat),
		CBN n -> CBN (BN_inc n).

Local Lemma BN_inc_non_empty : forall (n : BinNat),
	exists b tn, b :: tn = BN_inc n.
Proof.
	intros n.
	{	destruct n as [|b tn]; [|destruct b].
	+	exists 1, []; reflexivity.
	+	exists 1, tn; reflexivity.
	+	exists 0, (BN_inc tn); reflexivity.
	}
Qed.

Local Lemma BN_inc_last : forall (n : BinNat),
	last n 1 = 1 -> last (BN_inc n) 1 = 1.
Proof.
	intro n.
	{	functional induction (BN_inc n); intro H.
		+	reflexivity.
		+	destruct t; [discriminate|].
			exact H.
		+	decompose record (BN_inc_non_empty t).
			assert (Ht : last t 1 = 1) by (destruct t; [reflexivity | assumption]).
			apply IHl in Ht.
			rewrite <- H1 in*.
			exact Ht.
		}
Qed.

Lemma CBN_last : forall (n : BinNat),
	CBN n -> last n 1 = 1.
Proof.
	intros n H.
	{	induction H as [| n HCBN HR].
	+ reflexivity.
	+ apply BN_inc_last.
		assumption.
	}
Qed.

Fixpoint BN_dec n :=
	match n with
	| [] => []
	| 0 :: t => BN_safe_bit 1 (BN_dec t)
	| 1 :: t => BN_safe_bit 0 t
	end.
(*Lemma BN_dec_valid : forall (n : BinNat),
	VBN n -> VBN (BN_dec n).
Proof.
	intros n.
	{	assert (Haux : forall {d : nat}, valid_BinNat d n \/ n = [] -> valid_BinNat d (BN_dec n) \/ (BN_dec n) = []).
	+	{	induction n as [|b tn HR]; [|destruct b]; intros d H.
		+	right; reflexivity.
		+ apply BN_safe_bit_valid, HR.
			destruct H; [|discriminate].
			left; inversion_clear H; assumption.
		+	{	destruct tn; simpl.
			+	right; reflexivity.
			+ destruct H; [|discriminate].
				inversion_clear H.
				left.
				apply valid_BinNat_Cons.
				assumption.
			}
		}
	+	intro H.
		assert (He : VBN n \/ n = []) by (left; assumption).
		apply Haux in He.
		{	destruct He as [He|He].
		+	assumption.
		+	rewrite He.
			apply valid_BinNat_Nil.
		}
	}
Qed.*)

Lemma BN_inc_dec : forall (n : BinNat),
	CBN n -> BN_dec (BN_inc n) = n.
Proof.
	intros n Hn.
	apply CBN_last in Hn.
	{	functional induction (BN_inc n).
	+ reflexivity.
	+	destruct t; [discriminate|].
		reflexivity.
	+	simpl.
		destruct t; [reflexivity|].
		apply IHl in Hn.
		rewrite Hn.
		reflexivity.
	}
Qed.

Local Fixpoint BN_sub_aux n m :=
	match n, m with
	| [], _ => None
	| _, [] => None
	| 1 :: tn, [1] => Some (BN_safe_zero tn)
	| 1 :: tn, 0 :: tm => BN_add_bit (BN_sub_aux tn tm) 1
	| 0 :: tn, 0 :: tm => BN_add_bit (BN_sub_aux tn tm) 0
	| 1 :: tn, 1 :: tm => BN_add_bit (BN_sub_aux tn tm) 0
	| 0 :: tn, 1 :: tm => BN_add_bit (BN_sub_borrow tn tm) 1
	end
with BN_sub_borrow n m :=
	match n, m with
	| [], _ => None
	| 0 :: tn, [] => BN_add_bit (BN_sub_borrow tn []) 1
	| 1 :: tn, [] => Some (BN_safe_zero tn)
	| 1 :: tn, 0 :: tm => BN_add_bit (BN_sub_aux tn tm) 0
	| 0 :: tn, 0 :: tm => BN_add_bit (BN_sub_borrow tn tm) 1
	| 1 :: tn, 1 :: tm => BN_add_bit (BN_sub_borrow tn tm) 1
	| 0 :: tn, 1 :: tm => BN_add_bit (BN_sub_borrow tn tm) 0
	end.

Definition BN_sub n m :=
	match m with
	| [] => n
	| _ =>	match BN_sub_aux n m with
		| None => []
		| Some n => n
		end
	end.
	
Notation "n - m" := (BN_sub n m) : bin_nat_scope.