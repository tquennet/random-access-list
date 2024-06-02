Require Import Arith Lists.List FunInd.
Require structure.tree.Clbt numerical.binary.BinNat.
Require Import NumRep.utils.Utils.
Module CLBT := structure.tree.Clbt.
Module BinNat := numerical.binary.BinNat.
Import BinNat.Notations.

Open Scope nat_scope.
Open Scope bin_nat_scope.
Import ListNotations.

(********************************************************************************)
(*	RAL (A : Type) == the type of random access list of items of type A.		*)
(*		 is_valid  == a predicate identifying valid RAL,						*)
(*					 all operations are defined only over valid RAL				*)
(*	  is_canonical == a predicate identifying canonical RAL						*)
(*		empty == the empty RAL													*)
(*			+: canonical_Empty : is_canonical empty								*)
(*		cons a l  == the RAL of element a followed by l							*)
(*			+: canonical_Cons : forall a l,										*)
(*					 			is_canonical l -> is_canonical (cons a l) 		*)
(*	**	Unary operator:															*)
(*		strip l == underlying BinNat structure									*)
(*		size l == element count of l											*)
(*		trim l == a canonical equivalent of l									*)
(*		head l == Some (first element of l) or None								*)
(*		tail l == empty if l is emptyr if l is cons a r							*)
(*	**	generator:																*)
(*		create n a == a list consisting of n copy of a							*)
(*	**	Indexed operations:														*)
(*		drop l n  == l without its first n elements								*)
(*		lookup l n == an option containing the nth element of l,				*)
(*						or None if size l < n									*)
(*		update l n a == if size l < n, l with nth element replaced by a			*)
(*	** Lemmes:																	*)
(*			size_strip_valid :	forall l, is_valid l ->							*)
(*								to_nat (strip l) = size l						*)
(*			strip_canonical :	forall l, is_canonical l -> 					*)
(*								BinNat.is_canonical (strip l) 					*)
(*																				*)
(*			cons_valid : forall a l, is_valid l -> is_valid (cons a l)			*)
(*			tail_valid : forall a l, is_valid l -> is_valid (tail a l)			*)
(*			drop_valid : forall l n, is_valid l -> is_valid (drop l n)			*)
(*			update_valid : forall l n a, is_valid l -> is_valid (update l n a)	*)
(*			create_valid : forall n a, is_valid (create n a)					*)
(*																				*)
(*			trim_canonical : forall l, is_valid l -> is_canonical (trim l)		*)
(*			tail_canonical : forall l, is_canonical l -> is_canonical (tail l)	*)
(*			drop_canonical : forall l n, is_valid l -> is_canonical (drop l n)	*)
(*																				*)
(*			cons_tail : forall a l, is_canonical l -> tail (cons a l) = l		*)
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

Lemma valid_zero : forall {n : nat} (ral : t),
		valid (S n) ral -> valid n (Zero :: ral).
Proof.
	intros n ral H.
	apply valid_Cons;
		[apply valid_BIT_Zero | assumption].
Qed.
Lemma valid_one : forall {n : nat} (ral : t) (clbt : CLBT.t),
		CLBT.is_valid n clbt -> valid (S n) ral
		-> valid n (One clbt :: ral).
Proof.
	intros n ral clbt Hclbt Hral.
	apply valid_Cons; [apply valid_BIT_One|];
		assumption.
Qed.
Lemma valid_tail : forall {n : nat} (ral : t),
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


Section size.

Definition strip_aux b :=
	match b with
	| Zero => 0
	| One _ => 1
	end.
Definition strip := map strip_aux.

Lemma strip_length : forall l, length (strip l) = length l.
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; simpl in *.
	+	reflexivity.
	+	f_equal.
		apply HR.
	+	f_equal.
		apply HR.
	}
Qed.
Lemma strip_zero_inj : forall n l, strip l = repeat 0 n -> l = repeat Zero n.
Proof.
	intro n.
	{	induction n as [|n HR]; intros l H; simpl in *.
	+	apply map_eq_nil in H.
		assumption.
	+	destruct l as [|bl tl]; [discriminate|destruct bl; [|discriminate]].
		f_equal.
		apply HR.
		apply (f_equal (@List.tl BinNat.Bit)) in H.
		assumption.
	}
Qed.

Fixpoint size (l : t) : nat :=
	match l with
	| [] => 0
	| Zero :: t => size t
	| One c :: t => CLBT.size c + size t
	end.
Theorem size_strip_valid : forall l, is_valid l -> BinNat.to_nat (strip l) = size l.
Proof.
	intros l H.
	enough (Ha : forall n, valid n l -> 2 ^ n * BinNat.to_nat (strip l) = size l);
	  [apply Ha in H; simpl in H; rewrite <- plus_n_O in H; assumption|].
	clear H.
	{	induction l as [| b tl HR]; [|destruct b]; intros n H; simpl in *.
	+	rewrite Nat.mul_0_r.
		reflexivity.
	+	inversion_clear H.
		apply HR in H1 as H.
		rewrite <- H, Nat.pow_succ_r', (Nat.mul_comm 2), <- Nat.mul_assoc.
		reflexivity.
	+	inversion_clear H.
		apply HR in H1 as H.
		inversion_clear H0.
		rewrite <- mult_n_Sm, Nat.add_comm.
		{	apply f_equal2_plus.
		+	symmetry.
			apply CLBT.valid_size.
			assumption.
		+	rewrite <- H, Nat.pow_succ_r', (Nat.mul_comm 2), <- Nat.mul_assoc.
			reflexivity.
		}
	}
Qed.

End size.

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

Lemma cons_aux_non_empty : forall (l : t) (clbt : CLBT),
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

Lemma cons_aux_inc_strip : forall (l : t) (clbt : CLBT),
	strip (cons_aux clbt l) = BinNat.inc (strip l).
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

Theorem cons_inc_strip : forall (l : t) (a : A),
	strip (cons a l) = BinNat.inc (strip l).
Proof.
	intros l a.
	apply cons_aux_inc_strip.
Qed.


Lemma cons_aux_empty : forall a l, cons_aux a l <> [].
Proof.
	intros a l H.
	apply (f_equal strip), (f_equal BinNat.to_nat) in H.
	rewrite cons_aux_inc_strip, BinNat.inc_S in H.
	discriminate.
Qed.

End cons.

Section canonical.

(*Inductive is_canonical_aux (n : nat) : t -> Prop :=
	| canonical_aux_Empty : is_canonical_aux n []
	| canonical_aux_Cons : forall (l : t) (t : CLBT),
	  is_canonical_aux n l -> CLBT.is_valid n t -> is_canonical_aux n (cons_aux t l).

Inductive is_canonical : t -> Prop :=
	| canonical_Empty : is_canonical empty
	| canonical_Cons : forall (l : t) (a : A),
		  is_canonical l -> is_canonical (cons a l).

*)
Definition is_canonical l := (BinNat.is_canonical (strip l)).
Definition is_inhabited l := (BinNat.is_positive (strip l)).

Lemma canonical_destruct (P : t -> Prop) :
		(P empty) ->
		(forall l, is_inhabited l -> P l) ->
		forall l, is_canonical l -> P l.
Proof.
	intros P0 Pi l Hl.
	specialize (Pi l).
	unfold is_canonical, is_inhabited in *.
	remember (strip l) as s eqn:Hs.
	destruct Hl; [|apply Pi; assumption].
	destruct l; [|discriminate].
	apply P0.
Qed.
Lemma cons_aux_inhabited : forall t l, is_canonical l -> is_inhabited (cons_aux t l).
Proof.
	intros t l H.
	unfold is_canonical, is_inhabited in *.
	rewrite cons_aux_inc_strip.
	apply BinNat.inc_positive.
	assumption.
Qed.

Lemma cons_inhabited : forall a l, is_canonical l -> is_inhabited (cons a l).
Proof.
	intros a l H.
	apply cons_aux_inhabited.
	assumption.
Qed.

Lemma is_canonical_tl : forall b l,
	  is_canonical (b :: l) -> is_canonical l.
Proof.
	intros b l H.
	unfold is_canonical in *.
	apply BinNat.is_canonical_equiv, BinNat.is_canonical_struct_tl in H.
	apply BinNat.is_canonical_equiv.
	assumption.
Qed.

(*Lemma is_canonical_aux_to_struct : forall n l, is_canonical_aux n l -> is_canonical_struct n l.
Proof.
	intros n l H.
	{	induction H as [| l t Hl HR Ht].
	+	split; [apply valid_Nil| reflexivity].
	+	destruct HR as [Hvl Hs].
		split; [apply cons_aux_valid; assumption|].
		enough (forall b, BinNat.is_canonical_struct_fix b (strip (cons_aux t l)) = true);
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
	+	apply canonical_aux_Empty.
	+	apply canonical_aux_Cons; [assumption| apply CLBT.singleton_valid].
	+	apply canonical_Empty.
	+	inversion_clear H0.
		apply canonical_Cons; assumption.
	}
Qed.

Lemma is_canonical_aux_One : forall n t, CLBT.is_valid n t -> is_canonical_aux n [One t].
Proof.
	intros n t H.
	apply (canonical_aux_Cons n []); [apply canonical_aux_Empty| assumption].
Qed.

Lemma is_canonical_aux_double : forall n l b,
		is_canonical_aux (S n) (b :: l) -> is_canonical_aux n (Zero :: b :: l).
Proof.
	intros n l b H.
	assert (b :: l <> []) by discriminate.
	{	induction H as [| r t Hr HR Ht].
	+	contradiction.
	+	inversion_clear Ht.
		apply (canonical_aux_Cons n (One l0 :: r)); [|assumption].
		{	destruct r as [|bl tl].
		+	apply (canonical_aux_Cons n []); [|assumption].
			apply canonical_aux_Empty.
		+	apply (canonical_aux_Cons n (Zero :: bl :: tl)); [|assumption].
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
		+	apply canonical_aux_Empty.
		+	destruct tl; [discriminate|].
			inversion_clear Hv.
			apply is_canonical_aux_double, HR.
			destruct b; split; assumption.
		+	inversion_clear Hv.
			inversion_clear H.
			destruct tl; [apply is_canonical_aux_One; assumption|].
			apply (canonical_aux_Cons n (Zero :: b :: tl)); [|assumption].
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

Lemma canonical_valid : forall l, is_canonical l -> is_valid l.
Proof.
	intros l H.
	apply is_canonical_struct_equiv in H.
	destruct H as [H _].
	assumption.
Qed.

Theorem strip_canonical : forall l, is_canonical l -> is_precanonical l.
Proof.
	intros l H.
	apply is_canonical_struct_equiv in H.
	destruct H as [_ H].
	assumption.
Qed.*)

(*Fixpoint trim l :=
	match l with
	| [] => []
	| One clbt :: tl => One clbt :: (trim tl)
	| Zero :: tl => match (trim tl) with
		| [] => []
		| r => Zero :: r
		end
	end.

Functional Scheme trim_ind := Induction for trim Sort Prop.

Lemma trim_precanonical : forall l, is_precanonical (trim l).
Proof.
	intro l.
	{	functional induction (trim l); simpl in *.
	+	reflexivity.
	+	reflexivity.
	+	rewrite e1 in IHl0.
		destruct y0; assumption.
	+	assumption.
	}
Qed.
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
Lemma trim_valid : forall l, is_valid l -> is_valid (trim l).
Proof.
	intros l H.
	apply trim_canonical in H.
	apply is_canonical_struct_equiv in H.
	destruct H.
	assumption.
Qed.

Lemma trim_strip_canonical_id : forall l,
		is_precanonical l -> trim l = l.
Proof.
	intros l.
	{	induction l as [|bl tl HR]; intro H;
			[|destruct bl; apply BinNat.is_canonical_struct_tl in H as Htl];
			simpl.
	+	reflexivity.
	+	rewrite HR; [|assumption].
		destruct tl; [discriminate|].
		reflexivity.
	+	rewrite HR; [|assumption].
		reflexivity.
	}
Qed.
Lemma trim_canonical_id : forall l, is_canonical l -> trim l = l.
Proof.
	intros l H.
	apply is_canonical_struct_equiv in H.
	destruct H as [_ H].
	apply trim_strip_canonical_id.
	assumption.
Qed.

Local Lemma trim_cons_aux : forall l a, trim (cons_aux a l) = cons_aux a (trim l).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intro a; simpl.
	+	reflexivity.
	+	destruct trim; reflexivity.
	+	pose proof (cons_aux_empty (CLBT.Node t0 a) (trim tl)).
		rewrite HR.
		destruct cons_aux; [contradiction|].
		reflexivity.
	}
Qed.

Lemma trim_cons : forall l a, trim (cons a l) = cons a (trim l).
Proof.
	intros l a.
	apply trim_cons_aux.
Qed.
Lemma trim_last_zero : forall l, trim (l ++ [Zero]) = trim l.
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; simpl.
	+	reflexivity.
	+	rewrite HR; reflexivity.
	+	rewrite HR; reflexivity.
	}
Qed.
Lemma trim_cons_zero : forall l n,
	l <> [] -> is_canonical_struct n l ->
	trim (Zero :: l) = Zero :: l.
Proof.
	intros l He H.
	revert He H.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n He H.
	+	contradiction.
	+	apply proj2 in H as Hs.
		assert (Htl : tl <> []) by (destruct tl; discriminate).
		apply is_canonical_struct_tl in H; fold strip in H.
		specialize (HR _ Htl H).
		simpl in *.
		rewrite HR.
		reflexivity.
	+	simpl.
		destruct H as [_ H].
		rewrite trim_strip_canonical_id; [|assumption].
		reflexivity.
	}
Qed.
*)
End canonical.


Section uncons.

Fixpoint uncons (l : t) : option (CLBT * t) :=
	match l with
	| [] => None
	| [One clbt] => Some (clbt, [])
	| One clbt :: t => Some (clbt, Zero :: t)
	| Zero :: t =>
		match uncons t with
		| None => None
		| Some (clbt, r) => Some (CLBT.right clbt, One (CLBT.left clbt) :: r)
		end
	end.
Functional Scheme uncons_ind := Induction for uncons Sort Prop.

(*Definition uncons_map_trim : option (CLBT * t) -> option (CLBT * t) :=
	option_map (fun '(clbt, r) => (clbt, trim r)).
Lemma trim_uncons : forall l, uncons_map_trim (uncons l) = uncons (trim l).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; simpl in *.
	+	reflexivity.
	+	destruct (trim tl), (uncons tl) as [p|];
			[discriminate|reflexivity|destruct p as [tt tr]|];
			simpl in *; rewrite <- HR; reflexivity.
	+	destruct tl; [reflexivity|].
		remember (b :: tl) as L.
		simpl.
		destruct trim; reflexivity.
	}
Qed.*)

Lemma uncons_valid : forall l n t r,
		valid n l ->
		Some (t, r) = uncons l ->
		CLBT.is_valid n t /\ valid n r.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [discriminate|destruct bl];
			intros n t r Hl H; inversion_clear Hl; simpl in *.
	+	destruct (uncons tl) as [p|]; [destruct p|discriminate].
		destruct (HR _ _ _ H1 eq_refl).
		inversion_clear H.
		split; [apply CLBT.right_valid; assumption|].
		apply valid_one; [apply CLBT.left_valid|]; assumption.
	+	inversion_clear H0.
		{	destruct tl; inversion_clear H.
		+	split; [assumption|apply valid_Nil].
		+	split; [|apply valid_zero]; assumption.
		}
	}
Qed.


Lemma uncons_cons : forall (l : t) (clbt : CLBT),
		is_canonical l -> uncons (cons_aux clbt l) = Some (clbt, l).
Proof.
	intros l clbt Hcl.
	unfold is_canonical in *.
	inversion Hcl as [|n Hl H]; [destruct l; [reflexivity|discriminate]|].
	clear Hcl.
	revert n Hl H.
	{	functional induction (cons_aux clbt l); intros n Hl H; simpl in *.
	+	reflexivity.
	+	destruct t0; [inversion_clear Hl; inversion_clear H0|].
		reflexivity.
	+	destruct t0; [reflexivity|].
		inversion_clear Hl.
		specialize (IHt0 _ H0 eq_refl).
		rewrite IHt0; simpl.
		reflexivity.
	}
Qed.

Lemma uncons_inhabited : forall (l : t),
		is_inhabited l -> is_some (uncons l) = true.
Proof.
	intros l Hl.
	{	induction l as [|bl tl HR]; [|destruct bl]; simpl.
	+	inversion_clear Hl.
	+	inversion_clear Hl.
		destruct uncons as [p|]; [destruct p; reflexivity|discriminate HR; assumption].
	+	destruct tl; reflexivity.
	}
Qed.
Lemma cons_uncons : forall l a r n,
		valid n l ->
		Some (a, r) = uncons l ->
		cons_aux a r = l.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros a r n Hl H.
	+	discriminate.
	+	inversion_clear Hl as [| _a _b _c Hb Htl].
		pose proof (Hv := uncons_valid tl).
		simpl in *.
		destruct (uncons tl) as [p|]; [destruct p as [rt rr]|discriminate].
		specialize (Hv _ _ _ Htl eq_refl).
		specialize (HR _ _ _ Htl eq_refl).
		destruct Hv as [Hvt Hvr].
		inversion_clear H; simpl.
		revert HR.
		inversion_clear Hvt; simpl.
		intro HR; rewrite HR.
		reflexivity.
	+	simpl in H.
		destruct tl; inversion_clear H; reflexivity.
	}
Qed.
Lemma uncons_canonical : forall l t r,
		is_inhabited l ->
		uncons l = Some (t, r) ->
		is_canonical r.
Proof.
	intro l.
	unfold is_canonical, is_inhabited in *.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros t r Hl H; simpl in *.
	+	discriminate.
	+	destruct (uncons tl) as [p|]; [destruct p as [rt rr]|discriminate].
		inversion_clear H; inversion_clear Hl.
		specialize (HR _ _ H eq_refl).
		remember (strip rr) as s eqn:Hs.
		destruct HR; [destruct rr;
					  [apply BinNat.canonical_pos, BinNat.positive_top|discriminate]|].
		rewrite Hs in H0.
		apply BinNat.canonical_pos, BinNat.positive_cons.
		assumption.
	+	inversion Hl; destruct tl; try discriminate;
					   [inversion_clear H; apply BinNat.canonical_0..|].
		inversion_clear H.
		apply BinNat.canonical_pos, BinNat.positive_cons.
		assumption.
	}
Qed.

Definition tail (l : t) : t :=
	match uncons l with
	| None => []
	| Some (_, r) => r
	end.
Lemma tail_valid : forall (l : t),
	is_valid l -> is_valid (tail l).
Proof.
	intros l H.
	unfold tail.
	pose proof (Hu := uncons_valid l 0).
	destruct uncons as [p|]; [destruct p|apply valid_Nil].
	destruct (Hu _ _ H eq_refl).
	assumption.
Qed.

Lemma tail_cons : forall (l : t) (a : A),
		is_canonical l -> tail (cons a l) = l.
Proof.
	intros l a H.
	unfold tail, cons.
	rewrite uncons_cons.
	reflexivity.
	assumption.
Qed.

Definition head (l : t) : option A :=
	match uncons l with
	| None => None
	| Some (t, _) => Some (CLBT.head t)
	end.
Lemma head_cons_aux : forall l t,
		is_canonical l ->
		head (cons_aux t l) = Some (CLBT.head t).
Proof.
	intros l t Hl.
	unfold head.
	rewrite uncons_cons; [|assumption].
	reflexivity.
Qed.
Lemma head_cons : forall l a,
		is_canonical l ->
		head (cons a l) = Some a.
Proof.
	intros l a.
	apply head_cons_aux.
Qed.
(*Lemma head_trim : forall l, head (trim l) = head l.
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; simpl.
	+	reflexivity.
	+	destruct (trim tl);	assumption.
	+	reflexivity.
	}
Qed.*)

(*Lemma trim_tail : forall l, trim (tail l) = tail (trim l).
Proof.
	intro l.
	unfold tail.
	pose proof (trim_uncons l).
	destruct uncons as [p0|], uncons as [p1|]; [|discriminate..|reflexivity].
	destruct p0, p1; simpl in *.
	inversion_clear H.
	reflexivity.
Qed.*)
End uncons.

Section well_formed.

Definition is_non_empty l := is_valid l /\ is_inhabited l.
Definition is_well_formed l := is_valid l /\ is_canonical l.

Lemma well_formed_induction (P : t -> Prop):
		(P empty) ->
		(forall a l, is_well_formed l -> P l -> P (cons a l)) ->
		(forall l, is_well_formed l -> P l).
Proof.
	intros H0 Hc l Hl.
	destruct Hl as [Hvl Hsl].
	unfold is_canonical in Hsl.
	remember (strip l) as s eqn:Hs.
	revert l Hvl Hs.
	{	induction Hsl as [|s Hsl HR] using BinNat.canonical_induction; intros l Hvl Hs.
	+	destruct l as [|bl tl]; [|discriminate].
		apply H0.
	+	apply BinNat.inc_positive in Hsl as Hl.
		rewrite Hs in Hl.
		apply uncons_inhabited in Hl as Hin.
		pose proof (Hcu := cons_uncons l).
		pose proof (Hucan := uncons_canonical l).
		pose proof (Huval := uncons_valid l).
		destruct (uncons l) as [p|]; [destruct p as [h tl]|discriminate].
		specialize (Hcu _ _ _ Hvl eq_refl).
		specialize (Hucan _ _ Hl eq_refl).
		specialize (Huval _ _ _ Hvl eq_refl).
		destruct Huval as [Hh Htl].
		apply (f_equal BinNat.dec) in Hs.
		rewrite <- Hcu, cons_aux_inc_strip, !BinNat.dec_inc in Hs; [|assumption..].
		rewrite <- Hcu; inversion_clear Hh.
		apply Hc; [split; assumption|].
		apply HR; assumption.
	}
Qed.

Lemma well_formed_destruct (P : t -> Prop):
		(P empty) ->
		(forall a l, is_well_formed l -> P (cons a l)) ->
		(forall l, is_well_formed l -> P l).
Proof.
	intros P0 Pc l Hl.
	apply well_formed_induction; [assumption| |assumption].
	intros a l0 Hl0 _.
	apply Pc.
	assumption.
Qed.

Lemma empty_well_formed : is_well_formed empty.
Proof.
	split; [apply valid_Nil|apply BinNat.canonical_0].
Qed.
Lemma cons_well_formed : forall a l,
		is_well_formed l -> is_well_formed (cons a l).
Proof.
	intros a l Hl.
	destruct Hl as [Hvl Hl].
	split; [apply cons_valid|apply BinNat.canonical_pos, cons_inhabited]; assumption.
Qed.
Lemma tail_well_formed : forall l,
		is_well_formed l -> is_well_formed (tail l).
Proof.
	intros l Hl.
	destruct Hl as [Hvl Hl].
	split; [apply tail_valid; assumption|].
	pose proof (Hc := uncons_canonical l).
	unfold tail.
	destruct Hl as [|l Hl] using canonical_destruct; [apply BinNat.canonical_0|].
	destruct uncons; [destruct p|apply BinNat.canonical_0].
	specialize (Hc _ _ Hl eq_refl).
	assumption.
Qed.

End well_formed.

Section open.

Open Scope type_scope.

Definition dt := t.

Inductive valid_dt : nat -> dt -> Prop :=
	| valid_DNil : valid_dt 0 []
	| valid_DCons : forall (n : nat) (b : BIT) (dl : dt),
		is_valid_BIT n b -> valid_dt n dl -> valid_dt (S n) (b :: dl).

Lemma valid_dt_length : forall n dt, valid_dt n dt -> length dt = n.
Proof.
	intro n.
	{	induction n as [|n HR]; intros dt H; inversion_clear H; simpl.
	+	reflexivity.
	+	rewrite (HR dl); [reflexivity | assumption].
	}
Qed.

(*
	Soit el et en les bits déja passés de l et n,
	on a :
		dral = rev el
		dbn = rev (en - (size el)) pour open
		dbn = rev (en ++ [1] - (size el)) pour open_borrow
*)

Record zipper := mkZip
{
	zip_tl : t;
	zip_dl : dt;
	zip_tree : CLBT;
	zip_nb : BinNat.dt;
}.

Definition is_zipper l zip :=
	l = rev_append zip.(zip_dl) (One zip.(zip_tree) :: zip.(zip_tl)).

Record valid_zipper (zip : zipper) :=
{
	dec_rtl : valid (S (length zip.(zip_dl))) zip.(zip_tl);
	dec_rdl : valid_dt (length zip.(zip_dl)) zip.(zip_dl);
	dec_rt : CLBT.is_valid (length zip.(zip_dl)) zip.(zip_tree);
	del_rn : length zip.(zip_nb) = length zip.(zip_dl);
}.

Fixpoint open_aux (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) :=
	match l, n with
	| [], _ => None
	| _, [] => None (* unreachable if n canonical *)
	| One t :: tl, [1] => Some (mkZip tl dral t dbn)
	| Zero as bit :: tl, 0 :: tn | One _ as bit :: tl, 1 :: tn
		=> open_aux tl tn (0 :: dbn) (bit :: dral)
	| One _ as bit :: tl, 0 :: tn => open_aux tl tn (1 :: dbn) (bit :: dral)
	| Zero as bit :: tl, 1 :: tn => open_borrow tl tn (1 :: dbn) (bit :: dral)
	end
with open_borrow (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) :=
	match l, n with
	| [], _ => None
	| Zero as bit :: tl, [] => open_borrow tl [] (1 :: dbn) (bit :: dral)
	| One t :: tl, [] => Some (mkZip tl dral t dbn)
	| Zero as bit :: tl, 0 :: tn | One _ as bit :: tl, 1 :: tn
		=> open_borrow tl tn (1 :: dbn) (bit :: dral)
	| Zero as bit :: tl, 1 :: tn => open_borrow tl tn (0 :: dbn) (bit :: dral)
	| One _ as bit :: tl, 0 :: tn => open_aux tl tn (0 :: dbn) (bit :: dral)
	end.

Definition open l n := open_borrow l n [] [].

Local Lemma open_aux_valid : forall l n dbn dl zip,
		open_aux l n dbn dl = Some zip
		\/ open_borrow l n dbn dl = Some zip ->
		valid (length dbn) l -> valid_dt (length dbn) dl ->
		valid_zipper zip.
	intro l.
	{	induction l as [|bl tl HR]; intros n dbn dl zip H Hl Hdl;
			[|destruct bl; (destruct n as [|bn tn]; [|destruct bn])]; simpl in *;
			destruct H as [H|H]; inversion_clear Hl.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_intror H)); assumption.
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_introl H)); assumption.
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_intror H)); assumption.
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_intror H)); assumption.
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_intror H)); assumption.
	+	discriminate.
	+	symmetry in H; inversion_clear H.
		inversion_clear H0.
		apply valid_dt_length in Hdl as Hl.
		split; simpl; rewrite Hl; [assumption..|reflexivity].
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_introl H)); assumption.
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _(or_introl H)); assumption.
	+	{	destruct tn.
		+	symmetry in H; inversion_clear H.
			inversion_clear H0.
			apply valid_dt_length in Hdl as Hl.
			split; simpl; rewrite Hl; [assumption..|reflexivity].
		+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
			apply (HR _ _ _ _ (or_introl H)); assumption.
		}
	+	pose proof (Hd := valid_DCons _ _ _ H0 Hdl).
		apply (HR _ _ _ _ (or_intror H)); assumption.
	}
Qed.

Local Lemma open_valid : forall l n zip,
		is_valid l ->
		open l n = Some zip ->
		valid_zipper zip.
Proof.
	unfold open.
	intros l n zip Hl Hr.
	{	apply (open_aux_valid l n [] []).
	+	right.
		assumption.
	+	assumption.
	+	apply valid_DNil.
	}
Qed.

Lemma open_decomp_aux : forall l n dbn dral zip,
		(open_aux l n dbn dral = Some zip ->
		(rev_append dral l) = rev_append (zip.(zip_dl)) (One zip.(zip_tree) :: zip.(zip_tl)))
		/\ (open_borrow l n dbn dral = Some zip ->
		(rev_append dral l) = rev_append (zip.(zip_dl)) (One zip.(zip_tree) :: zip.(zip_tl))).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral zip;
			(destruct n as [|bn tn]; [|destruct bn]); simpl in *;
			(split; intro H); try discriminate.
	+	apply HR in H.
		assumption.
	+	apply HR in H.
		assumption.
	+	apply HR in H.
		assumption.
	+	apply HR in H.
		assumption.
	+	apply HR in H.
		assumption.
	+	inversion_clear H.
		reflexivity.
	+	apply HR in H.
		assumption.
	+	apply HR in H.
		assumption.
	+	{	destruct tn.
		+	inversion_clear H.
			reflexivity.
		+	apply HR in H.
			assumption.
		}
	+	apply HR in H.
		assumption.
	}
Qed.
Lemma open_zipper : forall l n zip,
	open l n = Some zip ->
	is_zipper l zip.
Proof.
	intros l n zip H.
	apply open_decomp_aux in H.
	assumption.
Qed.

Lemma open_empty : forall n, open empty n = None.
Proof.
	reflexivity.
Qed.

Lemma open_borrow_zero_None : forall l dn dl,
		is_canonical l ->
		open_borrow l [] dn dl = None ->
		l = empty.
Proof.
	intros l dn dl Hl H.
	destruct Hl as [|l Hl] using canonical_destruct; [reflexivity|].
	enough (He : open_borrow l [] dn dl <> None)
		by (apply He in H; contradiction).
	clear H.
	revert dn dl Hl.
	{	induction l as [|bl tl HR]; [|destruct bl];
			intros dn dl Hl H; inversion_clear Hl; simpl in *.
	+	apply HR in H; assumption.
	+	discriminate.
	+	discriminate.
	}
Qed.

Lemma open_zero_None : forall l,
		is_canonical l ->
		open l [] = None ->
		l = empty.
Proof.
	intros l Hl H.
	apply open_borrow_zero_None in H; assumption.
Qed.
Lemma open_borrow_zero : forall l dn dl zip,
		open_borrow l [] dn dl = Some zip ->
		zip.(zip_dl) = (repeat Zero (length zip.(zip_dl) - length dl)) ++ dl
		/\ zip.(zip_nb) = (repeat 1 (length zip.(zip_dl) - length dl)) ++ dn.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl];
			intros dn dl zip H; simpl in *.
	+	discriminate.
	+	apply HR in H.
		destruct H as [Hdl Hnb].
		pose proof(Hlen := Nat.le_sub_l (length (zip_dl zip)) (length (zip_dl zip) - length (Zero :: dl))).
		rewrite Hdl in Hlen at 1.
		rewrite app_length, repeat_length, Nat.add_comm, Nat.add_sub in Hlen.
		rewrite (app_assoc _ [Zero] dl) in Hdl; rewrite (app_assoc _ [1] dn) in Hnb.
		rewrite <- repeat_cons in Hdl, Hnb.
		assert (forall {A : Type} (e : A) n, e :: repeat e n = repeat e (S n)) by reflexivity.
		rewrite H, <- Nat.sub_succ_l in Hdl, Hnb; [|assumption..].
		simpl in Hdl, Hnb.
		split; assumption.
	+	destruct zip as [ztl zdl zt znb].
		inversion_clear H; simpl.
		rewrite Nat.sub_diag.
		split; reflexivity.
	}
Qed.

Lemma open_zero : forall l zip,
		open l [] = Some zip ->
		zip.(zip_dl) = repeat Zero (length zip.(zip_dl)) /\ zip.(zip_nb) = repeat 1 (length zip.(zip_dl)).
Proof.
	enough (Hob : forall l zip n, open_borrow l [] (repeat 1 n) (repeat Zero n) = Some zip ->
					   zip.(zip_dl) = repeat Zero (length zip.(zip_dl)) /\ zip.(zip_nb) = repeat 1 (length zip.(zip_dl)))
		by (intros l zip H; apply (Hob _ _ O) in H; assumption).
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros zip n H; simpl in *.
	+	discriminate.
	+	apply (HR _ (S n)).
		assumption.
	+	inversion_clear H; simpl.
		split; rewrite repeat_length; reflexivity.
	}
Qed.

Definition dec_zip zip :=
	match BinNat.dt_dec zip.(zip_nb) with
	| (false, r) => open_borrow zip.(zip_tl) [] (1 :: r)
									   (One zip.(zip_tree) :: zip.(zip_dl))
	| (true, r) => Some (mkZip zip.(zip_tl) zip.(zip_dl) zip.(zip_tree) r)
	end.

Lemma open_aux_borrow_inc : forall l n dbn dral,
		BinNat.is_canonical_struct n ->
		open_aux l (BinNat.inc n) dbn dral = open_borrow l n dbn dral.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral Hn;
			(destruct n as [|bn tn];
		 	 	[|destruct bn; apply BinNat.is_canonical_struct_tl in Hn as Htn]);
			try reflexivity.
	+	apply HR; assumption.
	+	destruct tn as [|bn tn]; [discriminate|].
		reflexivity.
	+	apply HR; assumption.
	}
Qed.

Lemma open_aux_dt_true : forall l n dbn dral zip dd,
		(BinNat.dt_dec dbn) = (true, dd) ->
		(open_borrow l n dbn dral = Some zip ->
			open_borrow l n dd dral = dec_zip zip)
		/\ (open_aux l n dbn dral = Some zip ->
			open_aux l n dd dral = dec_zip zip).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral zip dd Hdd;
			assert (Hsdd : forall b, BinNat.dt_dec (b :: dbn) = (true, b :: dd))
				by (intro b; simpl; rewrite Hdd; destruct b; reflexivity);
			(destruct n as [|bn tn]; [|destruct bn]); split; intro H; simpl in *;
			try discriminate.
	+	specialize (Hsdd 1).
		apply (HR [] (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	specialize (Hsdd 0).
		apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
	+	specialize (Hsdd 0).
		apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	inversion_clear H.
		unfold dec_zip; simpl.
		rewrite Hdd.
		reflexivity.
	+	specialize (Hsdd 0).
		apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	specialize (Hsdd 1).
		apply (HR _ (1 :: dbn) _ _ (1 :: dd)); assumption.
	+	{	destruct tn as [|bn tn].
		+	inversion_clear H.
			unfold dec_zip; simpl.
			rewrite Hdd.
			reflexivity.
		+	specialize (Hsdd 0).
			apply (HR _ (0 :: dbn) _ _ (0 :: dd)); assumption.
		}
	}
Qed.


Lemma open_aux_inc : forall l n dbn dral dd zip,
		BinNat.is_canonical_struct n ->
		(BinNat.dt_dec dbn) = (false, dd) ->
		(open_borrow l n dbn dral = Some zip ->
			open_borrow l (BinNat.inc n) dd dral = dec_zip zip)
		/\ (open_aux l n dbn dral = Some zip ->
			open_borrow l n dd dral = dec_zip zip).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn dral dd zip Hn Hdd;
			(destruct n as [|bn tn]; [|destruct bn;
				apply BinNat.is_canonical_struct_tl in Hn as Htn]);
			split ; intro H; simpl in *;
			assert (BinNat.dt_dec (1 :: dbn) = (true, 0 :: dd))
				by (simpl; rewrite Hdd; reflexivity);
			assert (BinNat.dt_dec (0 :: dbn) = (false, 1 :: dd))
				by (simpl; rewrite Hdd; reflexivity);
			try discriminate.
	+	apply (open_aux_dt_true tl [] (1 :: dbn)); assumption.
	+	apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	apply (HR tn (0 :: dbn)); assumption.
	+	apply (HR tn (0 :: dbn)); assumption.
	+	apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	inversion_clear H.
		unfold dec_zip; simpl.
		rewrite Hdd.
		reflexivity.
	+	apply (HR tn (0 :: dbn)); assumption.
	+	apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		apply (open_aux_dt_true tl tn (1 :: dbn)); assumption.
	+	{	destruct tn as [|bn tn].
		+	inversion_clear H.
			unfold dec_zip; simpl.
			rewrite Hdd.
			reflexivity.
		+	apply (HR (bn :: tn) (0 :: dbn)); assumption.
		}
	}
Qed.



Lemma open_aux_None : forall l n dbn1 dbn2 dral,
		(open_borrow l n dbn1 dral = None -> open_borrow l n dbn2 dral = None)
		/\ (open_aux l n dbn1 dral = None -> open_aux l n dbn2 dral = None).
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn1 dbn2 dral ;
			(destruct n as [|bn tn]; [|destruct bn]);
			split; intro H; simpl in *; try reflexivity.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	discriminate.
	+	apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	apply (HR _ (1 :: dbn1)); assumption.
	+	destruct tn; [discriminate|].
		apply (HR _ (0 :: dbn1)); assumption.
	}
Qed.

Lemma open_aux_inc_None : forall l n dbn1 dbn2 dral ,
		BinNat.is_canonical_struct n ->
		(open_borrow l n dbn1 dral = None -> open_borrow l (BinNat.inc n) dbn2 dral = None)
		/\ (n <> [] -> open_aux l n dbn1 dral = None -> open_borrow l n dbn2 dral = None).
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dbn1 dbn2 dral Hn;
			(destruct n as [|bn tn]; [|destruct bn;
				apply BinNat.is_canonical_struct_tl in Hn as Htn]);
			(split; [|intro He]; intro H); simpl in *; try reflexivity.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	contradiction.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply (HR _ (0 :: dbn1)); assumption.
	+	apply (HR tn (0 :: dbn1)); assumption.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	discriminate.
	+	contradiction.
	+	assert (tn <> []) by (destruct tn; discriminate).
		apply (HR _ (0 :: dbn1)); assumption.
	+	apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	rewrite open_aux_borrow_inc; [|assumption].
		apply (open_aux_None _ _ (1 :: dbn1)); assumption.
	+	destruct tn as [|bn tn]; [discriminate|].
		apply (HR (bn :: tn) (0 :: dbn1)); [assumption|discriminate|assumption].
	}
Qed.

Lemma open_inc : forall l n,
		BinNat.is_canonical n ->
		open l (BinNat.inc n) = option_join dec_zip (open l n).
Proof.
	intros l n Hn.
	apply BinNat.is_canonical_equiv in Hn.
	unfold open.
	pose proof (Hnone := proj1 (open_aux_inc_None l n [] [] [] Hn)).
	pose proof (Hsome := open_aux_inc l n [] [] []).
	{	destruct open_borrow as [zip|].
	+	specialize (Hsome zip Hn eq_refl).
		apply proj1 in Hsome.
		apply Hsome; reflexivity.
	+	rewrite Hnone; reflexivity.
	}
Qed.

End open.

Section drop.

Definition safe_zero l : t :=
	match l with
	| [] => []
	| _ => Zero :: l
	end.
Lemma safe_zero_valid : forall l n, valid (S n) l -> valid n (safe_zero l).
Proof.
	intros l n H.
	{	destruct l.
	+	apply valid_Nil.
	+	apply valid_zero.
		assumption.
	}
Qed.
Lemma safe_zero_canonical : forall l, is_canonical l -> is_canonical (safe_zero l).
Proof.
	intros l Hl.
	destruct Hl as [|l Hl] using canonical_destruct; [apply BinNat.canonical_0|].
	destruct l; [inversion_clear Hl|].
	apply BinNat.canonical_pos, BinNat.positive_cons.
	assumption.
Qed.

Fixpoint scatter t tl dn :=
	match dn with
	| [] => (t, tl)
	| 1 :: tn => scatter (CLBT.right t) (One (CLBT.left t) :: tl) tn
	| 0 :: tn => scatter (CLBT.left t) (safe_zero tl) tn
	end.

Definition drop l n :=
	match open l n with
	| Some zip => (uncurry cons_aux)
					(scatter zip.(zip_tree) (safe_zero zip.(zip_tl)) zip.(zip_nb))
	| _ => []
	end.

Lemma scatter_valid : forall t tl dn,
		CLBT.is_valid (length dn) t -> valid (length dn) tl ->
		CLBT.is_valid 0 (fst (scatter t tl dn)) /\ is_valid (snd (scatter t tl dn)).
Proof.
	intros t.
	{	induction t as [|l HRl r HRr]; intros tl dn Ht Htl;
		(destruct dn as [|bn tn]; [|destruct bn]); simpl.
	+	split; assumption.
	+	inversion_clear Ht.
	+	inversion_clear Ht.
	+	inversion_clear Ht.
	+	inversion_clear Ht.
		apply HRl, safe_zero_valid; assumption.
	+	inversion_clear Ht.		
		apply HRr; [assumption|].
		apply valid_one; assumption.
	}
Qed.

Lemma scatter_lookup : forall dn t tl,
		CLBT.is_valid (length dn) t ->
		fst (scatter t tl dn) = CLBT.Leaf (CLBT.lookup t (BinNat.complement dn)).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; intros t tl Ht;
			inversion_clear Ht; simpl.
	+	reflexivity.
	+	destruct bn; apply HR; assumption.
	}
Qed.
Lemma scatter_canonical : forall dn t l,
		is_canonical l ->
		is_canonical (snd (scatter t l dn)).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; [|destruct bn]; intros t l Hl; simpl in *.
	+	assumption.
	+	apply HR.
		apply safe_zero_canonical.
		assumption.
	+	apply HR, BinNat.one_canonical.
		assumption.
	}
Qed.

Lemma scatter_empty_zeroes : forall n t, snd (scatter t empty (repeat 0 n)) = empty.
Proof.
	intro n.
	{	induction n as [|n HR]; intro t; simpl.
	+	reflexivity.
	+	apply HR.
	}
Qed.
Lemma scatter_zeroes : forall n t l,
		l <> [] ->
		snd (scatter t l (repeat 0 n)) = (repeat Zero n) ++ l.
Proof.
	intro n.
	{	induction n as [|n HR]; intros t l He; simpl.
	+	reflexivity.
	+	rewrite app_comm_cons, repeat_cons, <- app_assoc.
		destruct l; [contradiction|].
		apply HR.
		discriminate.
	}
Qed.

Lemma scatter_cons_zero_aux : forall n k t l r,
		CLBT.is_valid n t ->
		cons_aux t l = (repeat Zero k) ++ r ->
		(uncurry cons_aux) (scatter t l (repeat 1 n)) = (repeat Zero (n + k)) ++ r.
Proof.
	intros n.
	{	induction n as [|n HR]; intros k t l r Ht; inversion_clear Ht; intro Hc; simpl in *.
	+	assumption.
	+	rewrite app_comm_cons, repeat_cons, <- app_assoc.
		apply HR; [assumption|].
		rewrite app_assoc, <- repeat_cons.
		simpl.
		rewrite <- Hc.
		reflexivity.
	}
Qed.
Lemma scatter_cons_zero : forall n t tl,
		CLBT.is_valid n t ->
		(uncurry cons_aux) (scatter t (safe_zero tl) (repeat 1 n)) = (repeat Zero n) ++ [One t] ++ tl.
Proof.
	intros n t tl Ht.
	rewrite (plus_n_O n) at 2.
	{	apply scatter_cons_zero_aux.
	+	assumption.
	+	destruct tl; reflexivity.
	}
Qed.

Lemma scatter_dec_aux : forall dn tl t dd,
		is_canonical tl ->
		CLBT.is_valid (length dn) t ->
		BinNat.dt_dec dn = (true, dd) ->
		tail ((uncurry cons_aux) (scatter t tl dn)) = (uncurry cons_aux) (scatter t tl dd).
Proof.
	intros dn.
	{	induction dn as [|bn tdn HR]; [|destruct bn];
			intros tl t dd Htl Ht Hdd; simpl in *.
	+	discriminate.
	+	destruct BinNat.dt_dec as [b tdd], b; [|discriminate].
		inversion_clear Hdd; simpl.
		inversion_clear Ht; simpl.
		apply safe_zero_canonical in Htl.
		apply HR; [assumption..|reflexivity].
	+	pose proof (Hz := BinNat.dt_dec_zero tdn).
		pose proof (Hl := BinNat.dt_dec_length tdn).
		apply BinNat.one_canonical in Htl.
		{	destruct BinNat.dt_dec as [b tdd], b.
		+	inversion_clear Hdd; simpl.
			inversion_clear Ht; simpl.
			apply HR; [assumption..|reflexivity].
		+	specialize (Hz _ eq_refl).
			specialize (Hl _ _ eq_refl).
			inversion_clear Hdd; simpl.
			inversion_clear Ht; simpl.
			rewrite (proj1 Hz), (proj2 Hz).
			rewrite (scatter_cons_zero (length tdd)); [|rewrite <- Hl; assumption].
			pose proof (Hzs := scatter_zeroes (length tdn) r (One l :: tl)).
			pose proof (Hc := scatter_canonical
								  (repeat 0 (length tdn)) r (One l :: tl) Htl).
			destruct scatter as [st sr]; simpl in *.
			unfold tail.
			rewrite uncons_cons, Hzs, Hl; [reflexivity|discriminate|assumption].
		}
	}
Qed.
Lemma drop_canonical : forall l n,
		is_canonical l -> is_canonical (drop l n).
Proof.
	intros l n Hl.
	unfold drop.
	pose proof (Hz := open_zipper l n).
	destruct open as [zip|]; [apply BinNat.canonical_pos|apply BinNat.canonical_0].
	specialize (Hz _ eq_refl); unfold is_zipper, is_canonical, strip in Hz, Hl.
	rewrite Hz, rev_append_rev, map_app in Hl.
	destruct zip as [tl dl t nb]; simpl in *.
	pose proof (Hs := scatter_canonical nb t (safe_zero tl)).
	destruct scatter.
	apply BinNat.is_canonical_app, BinNat.is_canonical_tl in Hl.
	apply cons_aux_inhabited, Hs, safe_zero_canonical.
	assumption.
Qed.
Lemma drop_valid : forall l n,
		is_valid l -> is_valid (drop l n).
Proof.
	intros l n Hl.
	unfold drop.
	pose proof (Hv := open_valid l n).
	destruct open as [zip|]; [|apply valid_Nil].
	destruct (Hv _ Hl eq_refl) as [Htl Hdl Ht Hlen].
	destruct zip as [tl dl t nb]; simpl in *.
	rewrite <- Hlen in Htl, Ht.
	apply safe_zero_valid in Htl.
	destruct (scatter_valid t (safe_zero tl) nb Ht Htl) as [Hst Htt].
	destruct scatter as [st tt]; simpl in *.
	apply cons_aux_valid; assumption.
Qed.

Lemma drop_zero : forall l,
		is_well_formed l ->
		drop l [] = l.
Proof.
	intros l Hl.
	destruct Hl as [Hvl Hsl].
	unfold drop.
	pose proof (Hoz := open_zero l).
	pose proof (Hv := open_valid l []).
	pose proof (Hozn := open_zero_None _ Hsl).
	pose proof (Hz := open_zipper l []).
	destruct open as [zip|]; [|rewrite Hozn; reflexivity].
	specialize (Hoz zip eq_refl).
	specialize (Hv zip Hvl eq_refl).
	specialize (Hz zip eq_refl).
	destruct Hv as [_ _ Ht _].
	unfold is_zipper in Hz.
	destruct zip as [tl dl t dn], Hoz as [Hdl Hnb]; simpl in *.
	pose proof (Hsc := scatter_cons_zero (length dl) t tl Ht).
	rewrite Hnb.
	destruct scatter as [st sl]; simpl in *.
	rewrite <- rev_repeat, <- Hdl, <- rev_append_rev, <- Hz in Hsc.
	assumption.
Qed.

Lemma drop_inc : forall l n,
		is_well_formed l -> BinNat.is_canonical n ->
		tail (drop l n) = drop l (BinNat.inc n).
Proof.
	intros l n Hl Hn.
	destruct Hl as [Hvl Hl].
	unfold drop.
	unfold is_canonical, strip in Hl.
	pose proof (Hv := open_valid l n).
	pose proof (Hi := open_inc l n Hn).
	pose proof (Hz := open_zipper l n).
	destruct (open l n) as [zip|]; rewrite Hi; [simpl|reflexivity].
	specialize (Hz _ eq_refl); unfold is_zipper in Hz.
	destruct (Hv _ Hvl eq_refl) as [Hvtl Hvdl Ht Hlen].
	destruct zip as [tl dl t nb]; simpl in *.
	rewrite <- Hlen in Ht.
	rewrite Hz, rev_append_rev, map_app in Hl.
	apply BinNat.is_canonical_app, BinNat.is_canonical_tl in Hl.
	unfold dec_zip; simpl.
	pose proof (Hsd := scatter_dec_aux nb (safe_zero tl) t).
	pose proof (Hdz := BinNat.dt_dec_zero nb).
	pose proof (Hdlen := BinNat.dt_dec_length nb).
	{	destruct BinNat.dt_dec as [b tdd], b; simpl in *.
	+	assert (Hpsl : is_canonical (safe_zero tl))
			by (apply safe_zero_canonical; assumption).
		rewrite (Hsd _ Hpsl Ht eq_refl).
		reflexivity.
	+	specialize (Hdz _ eq_refl).
		rewrite (proj1 Hdz), (proj2 Hdz).
		pose proof (Hnone := open_borrow_zero_None tl
								 (1 :: repeat 1 (length tdd)) (One t :: dl) Hl).
		pose proof (Hsome := open_borrow_zero tl (1 :: repeat 1 (length tdd)) (One t :: dl)).
		pose proof (Hzip := open_decomp_aux tl [] (1 :: repeat 1 (length tdd)) (One t :: dl)).
		pose proof (Hv2 := open_aux_valid tl [] (1 :: repeat 1 (length tdd)) (One t :: dl)).
		{	destruct open_borrow as [zip|].
		+	destruct (Hsome _ eq_refl) as [Hdl Hnb].
			specialize (Hzip zip); apply proj2 in Hzip; specialize (Hzip eq_refl).
			specialize (Hdlen _ _ eq_refl).
			simpl in Hv2.
			rewrite <- Hdlen, repeat_length in Hv2.
			destruct (Hv2 zip) as [_ _ Hvt2 Hlen2];
				[right;reflexivity|rewrite Hlen; assumption| apply valid_DCons;
				[apply valid_BIT_One; assumption|rewrite Hlen; assumption]|].				
			destruct zip as [ztl zdl zt znb]; simpl in *.
			rewrite <- (repeat_app 1 _ (S (length tdd))) in Hnb.
			apply (f_equal (@length BinNat.Bit)) in Hnb as Hnlen.
			rewrite repeat_length in Hnlen.
			rewrite Hdl, !rev_append_rev, rev_app_distr, <- app_assoc in Hzip.
			simpl in Hzip.
			rewrite <- app_assoc in Hzip.
			apply app_inv_head in Hzip.
			inversion Hzip.
			rewrite Hnb, rev_repeat.
			assert (He : repeat Zero (length zdl - S (length dl)) ++ One zt :: ztl <> [])
				by (intro H; apply eq_sym, app_cons_not_nil in H; contradiction).
			destruct (repeat Zero (length zdl - S (length dl)) ++ One zt :: ztl) eqn:Hb;
				[contradiction|simpl; rewrite <- Hb].
			pose proof (Hzeroes := scatter_zeroes (length nb) t
				(Zero :: repeat Zero (length zdl - S (length dl)) ++ One zt :: ztl)).
			destruct (scatter t _ (repeat 0 (length nb))); simpl in *.
			assert (Htl : BinNat.is_canonical (map strip_aux tl)) by assumption.
			rewrite H0, rev_repeat, map_app in Htl.
			apply BinNat.is_canonical_app in Htl.
			inversion_clear Htl.
			simpl in Hl.
			unfold tail; rewrite Hzeroes, uncons_cons;
			  [|unfold is_canonical, strip; rewrite app_comm_cons, !map_app, app_assoc; apply BinNat.canonical_pos, BinNat.app_is_positive; assumption |discriminate].
			assert (forall {A : Type} (e : A) n, e :: repeat e n = repeat e (S n)) by reflexivity.
			rewrite app_comm_cons, app_assoc, H1, <- repeat_app,
				Nat.add_comm, Nat.add_succ_comm, Hdlen.
			apply eq_sym, scatter_cons_zero.
			rewrite <- Hnlen, Hlen2.
			assumption.
		+	rewrite Hnone; [|reflexivity].
			pose proof (Hsez := scatter_empty_zeroes (length nb) t).
			destruct (scatter t (safe_zero empty)).
			simpl in *.
			rewrite Hsez.
			unfold tail; rewrite uncons_cons; [reflexivity|apply BinNat.canonical_0].
		}
	}
Qed.

Lemma drop_as_tail : forall l n,
	 	is_well_formed l ->
		BinNat.is_canonical n ->
		drop l n = fun_pow tail (BinNat.to_nat n) l.
Proof.
	intros l n Hl Hn.
	revert l Hl.
	{	induction Hn as [|n Hn HR] using BinNat.canonical_induction; intros l Hl; simpl.
	+	apply drop_zero.
		assumption.
	+	rewrite BinNat.inc_S;simpl.
		rewrite <- fun_pow_comm.
		rewrite <- HR; [|assumption].
		apply eq_sym, drop_inc; assumption.
	}
Qed.

End drop.

Definition lookup l n :=
	match open l n with
	| Some {|zip_tree := t; zip_nb := an|}
		=> Some (CLBT.lookup t (BinNat.complement an))
	| _ => None
	end.

Lemma lookup_drop : forall l n,
		is_well_formed l ->
		lookup l n = head (drop l n).
Proof.
	intros l n Hl.
	destruct Hl as [Hvl Hl].
	unfold lookup, drop.
	pose proof (Hv := open_valid l n).
	pose proof (Hz := open_zipper l n).
	destruct (open l n) as [zip|]; [|reflexivity].
	specialize (Hv zip Hvl eq_refl).
	unfold is_canonical, strip in Hl.
	rewrite (Hz _ eq_refl), rev_append_rev, map_app in Hl.
	apply BinNat.is_canonical_app, BinNat.is_canonical_tl, safe_zero_canonical in Hl.
	destruct Hv as [_ _ Ht Hlen].
	destruct zip as [tl dl t an]; simpl in *.
	rewrite <- Hlen in Ht.
	pose proof (CLBT.open_lookup t an Ht).
	destruct CLBT.open.
	pose proof (Hslcan := scatter_canonical an t (safe_zero tl) Hl).
	pose proof (Hsl := scatter_lookup an t (safe_zero tl) Ht).
	destruct scatter; simpl in *.
	rewrite Hsl.
	symmetry.
	apply head_cons.
	assumption.
Qed.

Lemma lookup_zero : forall l,
		is_well_formed l ->
		lookup l [] = head l.
Proof.
	intros l Hl.
	pose proof (BinNat.canonical_0).
	rewrite lookup_drop, drop_as_tail; [|assumption..].
	reflexivity.
Qed.

Lemma lookup_inc : forall l n,
	 	is_well_formed l ->
		BinNat.is_canonical n ->
		lookup l (BinNat.inc n) = lookup (tail l) n.
Proof.
	intros l n Hl Hn.
	apply BinNat.inc_positive in Hn as Hin.
	apply BinNat.canonical_pos in Hin.
	apply tail_well_formed in Hl as Htl.
	rewrite !lookup_drop, !drop_as_tail; [|assumption..].
	rewrite BinNat.inc_S.
	reflexivity.
Qed.
Section update.

Definition plug (l : t) (dl : dt) := rev_append dl l.

Local Lemma plug_valid : forall dl l n,
		valid n l -> valid_dt n dl ->
		is_valid (plug l dl).
Proof.
	intro dl.
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
	match open l n with
	| Some zip =>
		plug (One (CLBT.update zip.(zip_tree) (BinNat.complement zip.(zip_nb)) a)
				  :: zip.(zip_tl)) zip.(zip_dl)
	| _ => l
	end.

Lemma update_valid : forall l n a, is_valid l -> is_valid (update l n a).
Proof.
	intros l n a H.
	unfold update.
	pose proof (Hvalid := open_valid l n).
	destruct open as [zip|]; [|assumption].
	destruct (Hvalid zip) as [Htl Hdl Ht Hnb]; [assumption|reflexivity|].
	destruct zip as [tl dl t nb]; simpl in *.
	pose proof (Hop := CLBT.make_zip_valid _ _ Ht).
	rewrite <- Hnb in Hop.
	apply CLBT.open_valid in Hop.
	rewrite Hnb in Hop.
	rewrite <- BinNat.complement_length in Hnb.
	destruct CLBT.open as [ot odt], Hop as [Hot Hodt].
	apply (plug_valid _ _ (length dl)); [|assumption].
	apply valid_one; [|assumption].
	rewrite <- Hnb.
	apply CLBT.update_valid.
	rewrite Hnb.
	assumption.
Qed.

End update.

Lemma comprehension : forall l0 l1,
		is_well_formed l0 -> is_well_formed l1 ->
		(forall n, BinNat.is_canonical n -> lookup l0 n = lookup l1 n) ->
		l0 = l1.
Proof.
	intros l0 l1 Hl0.
	revert l1.
	{	induction Hl0 as [|a l0 Hl0 HR] using well_formed_induction; intros l1 Hl1 H;
			destruct Hl1 as [|b l1 Hl1] using well_formed_destruct; simpl.
	+	reflexivity.
	+	specialize (H _ BinNat.canonical_0).
		apply proj2 in Hl1 as Hsl1.
		apply (cons_well_formed b) in Hl1 as Hcl1.
		pose proof (empty_well_formed).
		rewrite !lookup_zero, head_cons in H; [|assumption..].
		discriminate.
	+	specialize (H _ BinNat.canonical_0).
		apply proj2 in Hl0 as Hsl0.
		apply (cons_well_formed a) in Hl0 as Hcl0.
		pose proof (empty_well_formed).
		rewrite !lookup_zero, head_cons in H; [|assumption..].
		discriminate.
	+	pose proof (H0 := H _ BinNat.canonical_0).
		apply proj2 in Hl0 as Hcl0.
		apply proj2 in Hl1 as hcl1.
		pose proof (cons_well_formed a _ Hl0).
		pose proof (cons_well_formed b _ Hl1).
		rewrite !lookup_zero, !head_cons in H0; [|assumption..].
		inversion_clear H0.
		f_equal.
		apply HR; [assumption|].
		intros n Hn.
		apply BinNat.inc_positive in Hn as Hin.
		apply BinNat.canonical_pos in Hin.
		specialize (H _ Hin).
		rewrite !lookup_inc in H; [|assumption..].
		rewrite !tail_cons in H; [|assumption..].
		assumption.
	}
Qed.

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
