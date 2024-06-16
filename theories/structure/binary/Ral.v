Require Import Arith Lists.List FunInd.
Require container.binary.Clbt numerical.binary.BinNat.
Require Import numerical.Num.
Require Import NumRep.utils.Utils.
Module CLBT := container.binary.Clbt.
Module BinNat := numerical.binary.BinNat.
Import BinNat.Notations.

Open Scope nat_scope.
Open Scope bin_nat_scope.
Import ListNotations.


(********************************************************************************)
(** * Random-access list

** Predicates:

- [is_valid l] <=> the cardinality of the trees corresponds to the exponentiated base
- [is_canonical l] <=> there is no trailing zeros
- [is_well_formed l] <=> [is_valid l /\ is_canonical l]

All the constructors in the file produce valid and canonical
random-access list and operations preserve validity and canonicity.

** Constructors:

- [t] == the type of random-access lists
- [empty] == empty random-access list
- [create n a] == random-access list consisting of [n] copies of [a]

** Operations:

- [card l] == compute the number of elements in the random-access list [l]
- [cons a l] == concatenate [a] to [l]
- [lookup l n] == retrieve the [n]-th element of [l]
- [update l n a] == update the [n]-th element of [l] with [a]

** Conversions:

- [to_bin l] == convert [l] to its underlying binary number

*)
(********************************************************************************)


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

(** [ArrayBit] *)

Variant ArrayBit (T: Type) :=
	| Zero : ArrayBit T
	| One : T -> ArrayBit T.

Arguments Zero {T}.
Arguments One {T} t.

(** Iterator over [ArrayBit] *)

Definition foldMap {T M} (m: Monoid M)(f: T -> M)(b: ArrayBit T): M :=
  match b with
  | Zero => m.(monoid_unit)
  | One t => f t
  end.

(** [to_bit] *)

Definition to_bit {T} (b: ArrayBit T) :=
	match b with
	| Zero => 0
	| One _ => 1
	end.

(** [ArrayList] *)

Notation Tree := (@CLBT.t A).

Definition ArrayList := Num.t (ArrayBit Tree).
Definition t := ArrayList.

(** One-hole context of [ArrayList] *)

Definition dt := list (ArrayBit Tree).

(*Fixpoint plug t (dt: dt) := 
  match dt with
  | [] => t
  | b :: dt => plug (snoc t b) dt
  end.*)

(** [to_bin] *)

Definition to_bin (l: t) := Num.map to_bit l.

Lemma to_bin_length : forall l, Num.length (to_bin l) = Num.length l.
Proof.
	apply mapi_length.
Qed.

(* XXX: delete? 
Lemma to_bin_zero_inj : forall n l, to_bin l = repeat 0 n -> l = repeat Zero n.
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
*)

(** [card] *)

Definition card (l : t) : nat :=
  Num.foldMap Monoid_nat (fun _ => foldMap Monoid_nat CLBT.card) 0 l.

(** [is_valid] *)

Definition is_valid_ArrayBit (h: nat)(b: ArrayBit Tree) :=
  foldMap Monoid_Prop (CLBT.is_valid h) b.

Definition is_valid_k (k : nat) (l: ArrayList) :=
  Num.foldMap Monoid_Prop is_valid_ArrayBit k l.
Definition is_valid := is_valid_k 0.

Inductive is_validP (h: nat)(l: ArrayList): Prop := 
  (* XXX: equivalent, inductive formulation of [is_valid] *).

Inductive is_dvalid : nat -> dt -> Prop :=
	| valid_DNil : is_dvalid 0 []
	| valid_DCons : forall n b dl,
		is_valid_ArrayBit n b ->
                is_dvalid n dl ->
                is_dvalid (S n) (b :: dl).

Theorem to_bin_card_valid : forall (l : t), is_valid l -> BinNat.to_nat (to_bin l) = card l.
Proof.
	intros l H.
	enough (He : forall (k : nat), is_valid_k k l ->
		Num.foldMap Monoid_nat BinNat.bit_to_nat k (to_bin l) =
		Num.foldMap Monoid_nat (fun _ => foldMap Monoid_nat CLBT.card) k l) by
	  (apply He in H; assumption).
	clear H.
	{	induction l as [|tl HR bl]; [|destruct bl]; simpl;
			intros k Hn; destruct Hn as [Htn H].
	+	reflexivity.
	+	unfold to_bin.
		rewrite map_snoc.
		cbn [Num.foldMap foldM mapi Monoid_nat monoid_plus].
		cbn [to_bit BinNat.bit_to_nat foldMap monoid_unit Monoid_nat].
		rewrite <- !plus_n_O.
		apply HR.
		assumption.
	+	unfold to_bin, Num.foldMap in *.
		rewrite map_snoc.
		simpl in H.
		cbn [foldM mapi Monoid_nat monoid_plus].
		cbn [to_bit BinNat.bit_to_nat foldMap monoid_unit Monoid_nat].
		rewrite (CLBT.valid_card k), (HR (S k)); [|assumption..].
		reflexivity.
	}
Qed.
(*
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
*)

(* XXX: delete?
Lemma is_dvalid_length : forall n dt, is_dvalid n dt -> List.length dt = n.
Proof.
	intro n.
	{	induction n as [|n HR]; intros dt H; inversion_clear H; simpl.
	+	reflexivity.
	+	rewrite (HR dl); [reflexivity | assumption].
	}
Qed.
*)

Local Lemma is_valid_plug : forall dl l n,
		is_validP n l -> is_dvalid n dl ->
		is_valid (plug l dl).
Admitted.
(*
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
Qed. *)

(** [is_canonical] *)

Definition is_canonical (l: t) := BinNat.is_canonical (to_bin l).

(** [is_well_formed] *)

Record is_well_formed (l: t) := {
    wf_valid: is_valid l ;
    wf_canonical : is_canonical l
  }.

(** [empty] *)

Definition empty : t := Ob.

Lemma empty_valid : is_valid empty.
Proof. constructor. Qed.

Lemma empty_canonical : is_canonical empty.
Proof. apply BinNat.is_Ob. Qed.

Lemma empty_well_formed : is_well_formed empty.
Proof. constructor; auto using empty_canonical, empty_valid. Qed.

(** [create] *)

Section create.

Definition create_ArrayBit (a: A) (h: nat) (b: BinNat.Bit) := 
  match b with
  | 0 => Zero
  | 1 => One (CLBT.create a h)
  end.

Definition create_spec n a :=
  Num.mapi (create_ArrayBit a) n.

(** This implementation accumulates [t] along so as to be more
efficient than the one presented in the paper. *)

Fixpoint create_aux n (t: Tree) :=
	match n with
	| Ob => Ob
	| snoc tn 0 => snoc (create_aux tn (CLBT.Node t t)) Zero
	| snoc tn 1 => snoc (create_aux tn (CLBT.Node t t)) (One t)
	end.

Functional Scheme create_aux_ind := Induction for create_aux Sort Prop.

Definition create n a := create_aux n (CLBT.singleton a).

Lemma create_meets_spec: forall n a, create n a = create_spec n a.
Admitted.

Lemma create_valid : forall n a, is_valid (create n a).
Admitted.
(*
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
Qed. *)

Lemma create_canonical : forall n (a : A),
		BinNat.is_canonical n ->
		is_canonical (create n a).
Admitted.
(*
Proof.
	intros n a Hn.
	apply RAL.is_canonical_struct_equiv.
	apply BinNat.is_canonical_struct_equiv in Hn.
	{	split.
	+	apply RAL.create_valid.
	+	unfold RAL.is_precanonical.
		rewrite create_strip.
		assumption.
	}
Qed. *)

Lemma create_well_formed : forall n a, BinNat.is_canonical n -> is_well_formed (create n a).
Proof. constructor; auto using create_canonical, create_valid. Qed.

Theorem create_to_bin : forall n (a : A), to_bin (create n a) = n.
Admitted.
(*
Proof.
	intros n a.
	unfold RAL.create.
	{	induction n, (CLBT.singleton a), (RAL.create_aux n (CLBT.singleton a))
			using RAL.create_aux_ind
			; simpl in *.
	+	reflexivity.
	+	rewrite IHl.
		reflexivity.
	+	rewrite IHl.
		reflexivity.
	}
Qed.
*)

End create.

(** [cons] *)

Section cons.

Local Fixpoint cons_tree (clbt : CLBT.t) (l : t) : t :=
	match l with
	| Ob => snoc Ob (One clbt)
	| snoc t Zero => snoc t (One clbt)
	| snoc t (One e) => snoc (cons_tree (CLBT.Node e clbt) t) Zero
	end.

Definition cons (a : A) (l : t) := cons_tree (CLBT.singleton a) l.

Functional Scheme cons_tree_ind := Induction for cons_tree Sort Prop.

(* 
Lemma cons_tree_valid : forall  (l : t) (clbt : CLBT.t) {n : nat},
	valid n l -> CLBT.is_valid n clbt ->
	valid n (cons_tree clbt l).
Proof.
	intros clbt l.
	{	functional induction (cons_tree l clbt); intros n Hl Hclbt.
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
*)

Lemma cons_valid : forall (a : A) (l : t),
	is_valid l -> is_valid (cons a l).
Admitted.
(*
Proof.
	intros a l H.
	{	apply cons_tree_valid.
	+	exact H.
	+	apply CLBT.singleton_valid.
	}
Qed. *)

(* XXX: delete? 
Local Lemma cons_tree_non_empty : forall (l : t) (clbt : CLBT),
	exists b tl, b :: tl = cons_tree clbt l.
Proof.
	intros l clbt.
	{	destruct l as [|b tl]; [|destruct b].
	+	exists (One clbt), []; reflexivity.
	+	exists (One clbt), tl; reflexivity.
	+	exists Zero, (cons_tree (CLBT.Node t0 clbt) tl).
		reflexivity.
	}
Qed.
*)

Local Lemma cons_tree_inc : forall (l : t) (clbt : CLBT.t),
	to_bin (cons_tree clbt l) = BinNat.inc (to_bin l).
Admitted.
(*
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
*)

Theorem cons_inc : forall (l : t) (a : A),
	to_bin (cons a l) = BinNat.inc (to_bin l).
Proof. intros; eauto using cons_tree_inc. Qed.

Theorem ral_ind : forall (P: t -> Prop),
    P Ob ->
    (forall a l, is_well_formed l -> P l -> P (cons a l)) ->
    forall l, is_well_formed l -> P l.
Admitted.
    

(* XXX: delete? 
Lemma cons_tree_empty : forall a l, cons_tree a l <> [].
Proof.
	intros a l H.
	apply (f_equal strip), (f_equal BinNat.to_nat) in H.
	rewrite cons_tree_inc_strip, BinNat.inc_S in H.
	discriminate.
Qed. *)

End cons.

(* XXX: delete?
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
*)

(** [uncons], [hd], [tl] *)

Section Uncons.

Fixpoint uncons (l : t) : option (CLBT.t * t) :=
	match l with
	| Ob => None
	| snoc Ob (One clbt) => Some (clbt, Ob)
	| snoc t (One clbt) => Some (clbt, snoc t Zero)
	| snoc t Zero =>
            option_bind (uncons t) (fun '(clbt, r) => 
            match clbt with
            | CLBT.Leaf _ => None
            | CLBT.Node lt rt => Some (rt, snoc r (One lt))
            end)
	end.

(* Functional Scheme uncons_ind := Induction for uncons Sort Prop. *)

(* XXX: delete?
Definition uncons_map_trim : option (CLBT * t) -> option (CLBT * t) :=
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
Qed.
*)

(*
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
*)

Theorem uncons_valid : forall l t r,
		is_valid l ->
		Some (t, r) = uncons l ->
		CLBT.is_valid 0 t /\ is_valid r.
Admitted.

Theorem uncons_dec : forall l,
	is_canonical l ->
        option_map (fun p => to_bin (snd p)) (uncons l)
        = BinNat.dec (to_bin l).
Admitted.
(*
Proof.
	intros l Hl.
	{	destruct Hl.
	+	reflexivity.
	+	rewrite RAL.cons_tail, RAL.cons_inc_strip; [|assumption].
		apply strip_canonical in Hl.
		rewrite BinNat.inc_dec; [|assumption].
		reflexivity.
	}
Qed.
*)

Definition hd (l : t) : option A := 
  option_bind (uncons l) (fun t =>
  match t with 
  | (CLBT.Leaf a, _) => Some a
  | _ => (* Impossible if [is_well_formed l] ! *) None
  end).


Definition tl (l : t) : option t := option_map snd (uncons l).

Lemma tl_valid : forall (l : t),
	is_valid l -> option_lift is_valid (tl l).
Admitted.
(*
Proof.
	intros l H.
	unfold tail.
	pose proof (Hu := uncons_valid l 0).
	destruct uncons as [p|]; [destruct p|apply valid_Nil].
	destruct (Hu _ _ H eq_refl).
	assumption.
Qed.
*)

(* XXX: delete? 
Lemma trim_tail : forall l, trim (tail l) = tail (trim l).
Proof.
	intro l.
	unfold tail.
	pose proof (trim_uncons l).
	destruct uncons as [p0|], uncons as [p1|]; [|discriminate..|reflexivity].
	destruct p0, p1; simpl in *.
	inversion_clear H.
	reflexivity.
Qed.
*)

(* XXX: delete?
Lemma cons_uncons : forall (l : t) (clbt : CLBT),
	is_precanonical l -> uncons (cons_tree clbt l) = Some (clbt, l).
Proof.
	intros l clbt Hcl.
	{	functional induction (cons_tree clbt l); intros .
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
	apply is_canonical_struct_equiv in H.
	destruct H as [_ H].
	pose proof (HR := cons_uncons _ (CLBT.singleton a) H).
	unfold tail, cons.
	rewrite HR.
	reflexivity.
Qed.

Lemma precanonical_uncons : forall l t r,
		is_precanonical l ->
		uncons l = Some (t, r) ->
		is_precanonical r.
Proof.
	intros l t r Hl H.
	unfold is_precanonical in *.
	enough (He : forall b, BinNat.is_canonical_struct_fix b (strip l) = true ->
					  is_precanonical r)
		by (apply He in Hl; assumption).
	revert t r H.
	clear Hl.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros t r H b Hl; simpl in *.
	+	discriminate.
	+	destruct uncons; [destruct p|discriminate]; simpl.
		inversion_clear H; simpl.
		apply (HR _ _ eq_refl) in Hl.
		assumption.
	+	destruct tl; inversion_clear H; [reflexivity|].
		destruct b0; assumption.
	}
Qed.

Lemma precanonical_tail : forall l,
		is_precanonical l ->
		is_precanonical (tail l).
Proof.
	intros l Hl.
	unfold tail.
	pose proof (precanonical_uncons l).
	destruct uncons; [destruct p|reflexivity].
	apply (H _ _ Hl eq_refl).
Qed.
*)

Lemma tl_canonical : forall l,
		is_canonical l ->
		option_lift is_canonical (tl l).
Admitted.
(*
Proof.
	intros l Hl.
	apply is_canonical_struct_equiv in Hl.
	destruct Hl as [Hvl Hl].
	apply is_canonical_struct_equiv.
	{	split.
	+	apply tail_valid.
		assumption.
	+	apply precanonical_tail.
		assumption.
	}
Qed. *)

Theorem tl_well_formed: forall l, is_well_formed l -> option_lift is_well_formed (tl l).
Admitted.


End Uncons.

(* XXX: delete

Section Canonical.

Definition is_precanonical l := (BinNat.is_canonical_struct (strip l)).
Definition is_canonical_struct n l := valid n l /\ is_precanonical l.

Lemma precanonical_cons_tree : forall l t, is_precanonical l -> is_precanonical (cons_tree t l).
Proof.
	intros l t H.
	unfold is_precanonical.
	enough (BinNat.is_canonical_struct_fix false (strip (cons_tree t l)) = true)
		by (apply BinNat.is_canonical_struct_false; assumption).
	revert t H.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros t H; simpl in *.
	+	reflexivity.
	+	apply BinNat.is_canonical_struct_tl in H.
		assumption.
	+	apply HR.
		assumption.
	}
Qed.

Lemma is_canonical_struct_tl : forall n b l,
	  is_canonical_struct n (b :: l) -> is_canonical_struct (S n) l.
Proof.
	intros n b l H.
	destruct H as [Hv Hs].
	inversion_clear Hv.
	split; [assumption|].
	destruct l as [|bl tl]; [reflexivity|].
	destruct b, bl; assumption.
Qed.

Lemma is_canonical_aux_to_struct : forall n l, is_canonical_aux n l -> is_canonical_struct n l.
Proof.
	intros n l H.
	{	induction H as [| l t Hl HR Ht].
	+	split; [apply valid_Nil| reflexivity].
	+	destruct HR as [Hvl Hs].
		split; [apply cons_tree_valid; assumption|].
		enough (forall b, BinNat.is_canonical_struct_fix b (strip (cons_tree t l)) = true);
			[apply H|].
		clear Hl Ht Hvl.
		{	functional induction (cons_tree t l); intro b; simpl in *.
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

Local Lemma trim_cons_tree : forall l a, trim (cons_tree a l) = cons_tree a (trim l).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intro a; simpl.
	+	reflexivity.
	+	destruct trim; reflexivity.
	+	pose proof (cons_tree_empty (CLBT.Node t0 a) (trim tl)).
		rewrite HR.
		destruct cons_tree; [contradiction|].
		reflexivity.
	}
Qed.

Lemma trim_cons : forall l a, trim (cons a l) = cons a (trim l).
Proof.
	intros l a.
	apply trim_cons_tree.
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

End canonical.

Section cons_canonical.

Lemma cons_propagate : forall (l : t) a t rt n,
		BinNat.is_canonical (strip l) ->
		cons_tree a l = (repeat Zero n) ++ [One rt] ->
		cons_tree a (l ++ [One t]) = (repeat Zero n) ++ [Zero; One (CLBT.Node t rt)].
Proof.
	intros l a t rt n Hl.
	apply BinNat.is_canonical_struct_equiv in Hl.
	revert a t rt n Hl.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros a clbt rt n Hl H; simpl in *.
	+	destruct n; [|discriminate].
		inversion_clear H.
		reflexivity.
	+	destruct n; [|discriminate].
		apply (f_equal (@List.tl BIT)) in H.
		simpl in H.
		rewrite H in Hl.
		discriminate.
	+	destruct n; [discriminate|].
		apply (f_equal (@List.tl BIT)) in H.
		apply BinNat.is_canonical_struct_tl in Hl.
		simpl in H.
		specialize (HR _ clbt _ _ Hl H).
		rewrite HR.
		reflexivity.
	}
Qed.

Lemma cons_struct_tl : forall l a r,
	  	strip l = (repeat 1 (length l)) ->
		cons_tree a (l ++ Zero :: r) = cons_tree a l ++ r.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl];
			intros a r Hl; simpl in *.
	+	reflexivity.
	+	discriminate.
	+	f_equal.
		apply HR.
		inversion_clear Hl.
		reflexivity.
	}
Qed.

End cons_canonical.

Fixpoint head (l : t) : option A :=
match l with
| [] => None
| Zero :: t => head t
| One clbt :: _ => Some (CLBT.head clbt)
end.

Local Lemma head_cons_tree : forall l t, head (cons_tree t l) = Some (CLBT.head t).
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intro t; simpl.
	+	reflexivity.
	+	reflexivity.
	+	replace (CLBT.head t) with (CLBT.head (CLBT.Node t0 t)) by reflexivity.
		apply HR.
	}
Qed.
Lemma head_cons : forall l a, head (cons a l) = Some a.
Proof.
	intros l a.
	apply head_cons_tree.
Qed.
Lemma head_trim : forall l, head (trim l) = head l.
Proof.
	intros l.
	{	induction l as [|bl tl HR]; [|destruct bl]; simpl.
	+	reflexivity.
	+	destruct (trim tl);	assumption.
	+	reflexivity.
	}
Qed.
*)

(** [open] *)

Section open.

Record zipper := mkZip
{
	z_suffix : t;
	z_tree : Tree;
	z_prefix : dt;
	z_idx : BinNat.dt;
}.

(* XXX: delete? 
Definition is_zipper l zip :=
	l = rev_append zip.(zip_dl) (One zip.(zip_tree) :: zip.(zip_tl)).
*)

Record is_zvalid (z : zipper) :=
{
	dec_rtl : is_validP (S (List.length z.(z_idx))) z.(z_suffix);
	dec_rdl : is_dvalid (List.length z.(z_idx)) z.(z_prefix);
	dec_rt : CLBT.is_valid (List.length z.(z_idx)) z.(z_tree);
	del_rn : List.length z.(z_prefix) = List.length z.(z_idx);
}.

Fixpoint open_aux (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) :=
	match l, n with
	| Ob, _ => None
	| _, Ob => (* Impossible if [is_canonical n] *) None
	| snoc tl (One t), snoc Ob 1 => Some (mkZip tl t dral dbn)
	| snoc tl (Zero as bit), snoc tn 0
        | snoc tl (One _ as bit), snoc tn 1 =>
            open_aux tl tn (0 :: dbn) (bit :: dral)
	| snoc tl (One _ as bit), snoc tn 0 =>
            open_aux tl tn (1 :: dbn) (bit :: dral)
	| snoc tl (Zero as bit), snoc tn 1 =>
            open_borrow tl tn (1 :: dbn) (bit :: dral)
	end
with open_borrow (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) :=
	match l, n with
	| Ob, _ => None
	| snoc tl (Zero as bit), Ob =>
            open_borrow tl Ob (1 :: dbn) (bit :: dral)
	| snoc tl (One t), Ob => Some (mkZip tl t dral dbn)
	| snoc tl (Zero as bit), snoc tn 0
        | snoc tl (One _ as bit), snoc tn 1 =>
            open_borrow tl tn (1 :: dbn) (bit :: dral)
	| snoc tl (Zero as bit), snoc tn 1 =>
            open_borrow tl tn (0 :: dbn) (bit :: dral)
	| snoc tl (One _ as bit), snoc tn 0 =>
            open_aux tl tn (0 :: dbn) (bit :: dral)
	end.

Definition open l n := open_borrow l n [] [].


Local Lemma open_aux_valid : forall l n dbn dl zip,
		open_aux l n dbn dl = Some zip ->
		is_validP (List.length dbn) l -> is_dvalid (List.length dbn) dl ->
		is_zvalid zip
with open_borrow_valid: forall l n dbn dl zip, open_borrow l n dbn dl = Some zip ->
		is_validP (List.length dbn) l -> is_dvalid (List.length dbn) dl ->
		is_zvalid zip.
Admitted.
(*
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
*)

Theorem open_valid : forall l n zip,
		is_valid l ->
		open l n = Some zip ->
		is_zvalid zip.
Admitted.
(*
Proof.
	unfold open.
	intros l n zip Hl Hr.
	{	apply (open_borrow_valid l n [] []).
	+	assumption.
	+	assumption.
	+	apply valid_DNil.
	}
Qed. *)

(*

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
		is_precanonical l ->
		open_borrow l [] dn dl = None ->
		l = empty.
Proof.
	intros l dn dl Hl H.
	destruct l; [reflexivity|].
	enough (He : BinNat.is_canonical_struct (strip (b :: l)) -> open_borrow (b :: l) [] dn dl <> None)
		by (apply He in H; [contradiction|assumption]).
	clear Hl H.
	revert dn dl.
	{	induction l as [|bl tl HR]; intros dn dl Hl H;
			[|destruct bl; apply BinNat.is_canonical_struct_tl in Hl]; destruct b;
			 simpl in *.
	+	discriminate.
	+	discriminate.
	+	apply HR in H; assumption.
	+	discriminate.
	+	discriminate.
	+	discriminate.
	}
Qed.

Lemma open_zero_None : forall l,
		is_precanonical l ->
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
		BinNat.is_canonical_struct n ->
		open l (BinNat.inc n) = option_join dec_zip (open l n).
Proof.
	intros l n Hn.
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
*)

Definition forget_zipper :=
	option_map (fun z =>
                      BinNat.mkZip (to_bin z.(z_suffix))
				   (List.map to_bit z.(z_prefix))
                                   z.(z_idx)).

(*
Lemma open_gtb_aux : forall l n dl dn,
		open_forget (RAL.open_aux l n dn dl)
			= BinNat.gtb_decomp_aux (RAL.strip l) n (RAL.strip dl) dn
		/\ open_forget (RAL.open_borrow l n dn dl)
			= BinNat.gtb_decomp_borrow (RAL.strip l) n (RAL.strip dl) dn.
Proof.
	intro l.
	{	induction l as [|bl tl HR]; [|destruct bl]; intros n dl dn;
			(destruct n as [|bn tn]; [|destruct bn]); split; simpl; try reflexivity.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	apply HR.
	+	destruct tn; [reflexivity|].
		apply HR.
	+	apply HR.
	}
Qed.
*)

Theorem open_gt : forall l n,
    forget_zipper (open l n) = BinNat.gt (to_bin l) n.
Admitted.
(*
Proof.
	intros l n.
	apply open_gtb_aux.
Qed. *)


(* XXX: delete?

Lemma plug_strip : forall dl (l : @RAL.t A),
	  RAL.strip (RAL.plug l dl) = rev_append (RAL.strip dl) (RAL.strip l).
Proof.
	intro dl.
	{	induction dl as [|bl tdl HR]; [|destruct bl]; intro l; simpl.
	+	reflexivity.
	+	apply HR.
	+	apply HR.
	}
Qed.
*)

End open.

(** [lookup] *)

Section lookup.

Definition lookup l n :=
  match open l n with
  | Some {| z_tree := t; z_idx := idx |} =>
      CLBT.lookup t idx
  | _ => None
  end.

(*
Theorem lookup_none : forall (l : @RAL.t A) n,
		RAL.is_canonical l -> BinNat.is_canonical n ->
		(RAL.strip l) >? n = false -> RAL.lookup l n = None.
Proof.
	intros l n Hl Hn H.
	unfold RAL.lookup in *.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply RAL.is_canonical_struct_equiv in Hl.
	destruct Hl as [_ Hl].
	pose proof (Hgs := BinNat.gtb_decomp_equiv (RAL.strip l) n Hl Hn).
	pose proof (Hco := open_gtb l n).
	{	destruct RAL.open, (BinNat.gtb_decomp (RAL.strip l) n).
	+	rewrite H in Hgs.
		discriminate.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	}
Qed.
*)
End lookup.

(** [update] *)

Section update.

Definition update l n a :=
	match open l n with
	| Some z =>
            option_bind (CLBT.update z.(z_tree) z.(z_idx) a) (fun t' =>
	    Some (plug (snoc z.(z_suffix) (One t')) z.(z_prefix)))
	| _ => None
	end.

Lemma is_valid_update : forall l n a, is_valid l -> option_lift is_valid (update l n a).
Admitted.
(*
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
*)

Lemma is_canonical_update : forall l n a, is_canonical l -> option_lift is_canonical (update l n a).
Admitted.
(*
Proof.
	intros l n a Hl Hn.
	apply RAL.canonical_valid in Hl as Hvl.
	apply strip_canonical in Hl as Hsl.
	apply BinNat.is_canonical_struct_equiv in Hsl.
	apply RAL.is_canonical_struct_equiv.
	split; [apply RAL.update_valid; assumption|].
	unfold RAL.is_precanonical.
	rewrite update_strip; assumption.
Qed. *)

Theorem is_well_formed_update : forall l n a, is_well_formed l -> option_lift is_well_formed (update l n a).
Admitted.

Theorem update_to_bin : forall l n a,
		is_well_formed l -> BinNat.is_canonical n ->
		option_lift (fun l' => to_bin l' = to_bin l) (update l n a).
Admitted.
(*
Proof.
	intros l n a Hl Hn.
	unfold RAL.update.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply strip_canonical in Hl as Hsl.
	pose proof (Hoc := open_gtb l n).
	pose proof (Hcomp := BinNat.gtb_decomp_is_decomp (RAL.strip l) n).
	{	destruct RAL.open as [zip|], BinNat.gtb_decomp as [decomp|];
			try discriminate.
	+	specialize (Hcomp decomp Hn eq_refl).
		destruct zip as [tl dl t nb], decomp as [rtn rdn ran]; simpl in *.
		destruct Hcomp as [Hln Hz Hval].
		rewrite plug_strip, Hz.
		inversion_clear Hoc.
		reflexivity.
	+	reflexivity.
	}
Qed.
*)

Theorem update_failure : forall l n (a : A),
		is_well_formed l -> BinNat.is_canonical n ->
		(to_bin l) >? n = false -> update l n a = None.
Admitted.
(*
Proof.
	intros l n a Hl Hn H.
	unfold RAL.update in *.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply RAL.is_canonical_struct_equiv in Hl.
	destruct Hl as [_ Hl].
	pose proof (Hgs := BinNat.gtb_decomp_equiv (RAL.strip l) n Hl Hn).
	pose proof (Hco := open_gtb l n).
	{	destruct RAL.open, (BinNat.gtb_decomp (RAL.strip l) n).
	+	rewrite H in Hgs.
		discriminate.
	+	discriminate.
	+	discriminate.
	+	reflexivity.
	}
Qed.
*)

End update.

(** [drop] *)

Section drop.

Fixpoint scatter t dn: option (A * list (ArrayBit Tree)) :=
	match t, dn with
	| CLBT.Leaf a, [] => Some (a, [])
	| CLBT.Node lt rt, 1 :: tn =>
            option_bind (scatter rt tn) (fun '(a, p) =>
            Some (a, One lt :: p))
	| CLBT.Node lt _, 0 :: tn => 
            option_bind (scatter lt tn) (fun '(a, p) =>
            Some (a, Zero :: p))
        | _, _ => (* Impossible if [t] and [dn] are coherent *) None
	end.

Definition drop l n :=
	match open l n with
	| Some z =>
            option_bind (scatter z.(z_tree) z.(z_idx)) (fun '(a, p) =>
            Some (cons a (plug (snoc z.(z_suffix) Zero) p)))
	| _ => None
	end.

Lemma drop_canonical : forall l n,
		is_canonical l -> option_lift is_canonical (drop l n).
Admitted.
(*
Proof.
	intros l n Hl.
	apply is_canonical_struct_equiv in Hl.
	destruct Hl as [Hl Hcl].
	unfold drop.
	pose proof (Hvalid := open_valid l n).
	pose proof (Hzip := open_zipper l n).
	destruct open as [zip|]; [|apply canonical_Empty].
	apply is_canonical_struct_equiv.
	destruct (Hvalid zip Hl eq_refl) as [Htl Hdl Ht Hnb].
	specialize (Hzip _ eq_refl); unfold is_zipper in Hzip.
	destruct zip as [tl dl t nb]; simpl in *.
	{	split.
	+	rewrite <- Hnb in Ht, Htl.
		apply valid_safe_zero in Htl.
		pose proof (Hs := scatter_valid t (safe_zero tl) nb Ht Htl).
		destruct scatter, Hs.
		apply cons_tree_valid; assumption.
	+	pose proof (Hs := scatter_precanonical nb t (safe_zero tl)).
		rewrite Hzip, rev_append_rev in Hcl.
		unfold is_precanonical, strip in Hcl.
		rewrite map_app in Hcl.
		apply -> (BinNat.is_canonical_struct_app (strip (rev dl))) in Hcl; [|discriminate].
		destruct scatter as [st sr].
		apply precanonical_cons_tree, Hs, canonical_safe_zero.
		assumption.
	}
Qed.
*)

(* XXX: delete
Definition safe_zero l : t :=
	match l with
	| [] => []
	| _ => Zero :: l
	end.
Lemma valid_safe_zero : forall l n, valid (S n) l -> valid n (safe_zero l).
Proof.
	intros l n H.
	{	destruct l.
	+	apply valid_Nil.
	+	apply valid_zero.
		assumption.
	}
Qed.
Lemma canonical_safe_zero : forall l, is_precanonical l -> is_precanonical (safe_zero l).
Proof.
	intros l H.
	{	destruct l as [|bl tl].
	+	reflexivity.
	+	assumption.
	}
Qed.
*)

(*
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
		apply HRl, valid_safe_zero; assumption.
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

Lemma scatter_precanonical : forall dn t l,
		is_precanonical l ->
		is_precanonical (snd (scatter t l dn)).
Proof.
	intro dn.
	{	induction dn as [|bn tn HR]; [|destruct bn]; intros t l Hl; simpl in *.
	+	assumption.
	+	apply HR.
		apply canonical_safe_zero.
		assumption.
	+	apply HR.
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
		cons_tree t l = (repeat Zero k) ++ r ->
		(uncurry cons_tree) (scatter t l (repeat 1 n)) = (repeat Zero (n + k)) ++ r.
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
		(uncurry cons_tree) (scatter t (safe_zero tl) (repeat 1 n)) = (repeat Zero n) ++ [One t] ++ tl.
Proof.
	intros n t tl Ht.
	rewrite (plus_n_O n) at 2.
	{	apply scatter_cons_zero_aux.
	+	assumption.
	+	destruct tl; reflexivity.
	}
Qed.

Lemma scatter_dec_aux : forall dn tl t dd,
		is_precanonical tl ->
		CLBT.is_valid (length dn) t ->
		BinNat.dt_dec dn = (true, dd) ->
		tail ((uncurry cons_tree) (scatter t tl dn)) = (uncurry cons_tree) (scatter t tl dd).
Proof.
	intros dn.
	{	induction dn as [|bn tdn HR]; [|destruct bn];
			intros tl t dd Htl Ht Hdd; simpl in *.
	+	discriminate.
	+	destruct BinNat.dt_dec as [b tdd], b; [|discriminate].
		inversion_clear Hdd; simpl.
		inversion_clear Ht; simpl.
		apply canonical_safe_zero in Htl.
		apply HR; [assumption..|reflexivity].
	+	pose proof (Hz := BinNat.dt_dec_zero tdn).
		pose proof (Hl := BinNat.dt_dec_length tdn).
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
			pose proof (Hc := scatter_precanonical
								  (repeat 0 (length tdn)) r (One l :: tl) Htl).
			destruct scatter as [st sr]; simpl in *.
			unfold tail.
			rewrite cons_uncons, Hzs, Hl; [reflexivity|discriminate|assumption].
		}
	}
Qed.

Lemma drop_zero : forall l,
		is_canonical l ->
		drop l [] = l.
Proof.
	intros l Hl.
	apply is_canonical_struct_equiv in Hl as Hsl.
	destruct Hsl as [_ Hsl].
	unfold drop.
	pose proof (Hoz := open_zero l).
	pose proof (Hv := open_valid l []).
	pose proof (Hozn := open_zero_None _ Hsl).
	pose proof (Hz := open_zipper l []).
	destruct open as [zip|]; [|rewrite Hozn; reflexivity].
	specialize (Hoz zip eq_refl).
	specialize (Hv zip (canonical_valid _ Hl) eq_refl).
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
		is_canonical_struct 0 l -> BinNat.is_canonical_struct n ->
		tail (drop l n) = drop l (BinNat.inc n).
Proof.
	intros l n Hl Hn.
	destruct Hl as [Hvl Hl].
	unfold drop.
	unfold is_precanonical, strip in Hl.
	pose proof (Hv := open_valid l n).
	pose proof (Hi := open_inc l n Hn).
	pose proof (Hz := open_zipper l n).
	destruct (open l n) as [zip|]; rewrite Hi; [simpl|reflexivity].
	specialize (Hz _ eq_refl); unfold is_zipper in Hz.
	destruct (Hv _ Hvl eq_refl) as [Hvtl Hvdl Ht Hlen].
	destruct zip as [tl dl t nb]; simpl in *.
	rewrite <- Hlen in Ht.
	rewrite Hz, rev_append_rev, map_app in Hl.
	apply -> BinNat.is_canonical_struct_app in Hl; [|discriminate].
	unfold dec_zip; simpl.
	pose proof (Hsd := scatter_dec_aux nb (safe_zero tl) t).
	pose proof (Hdz := BinNat.dt_dec_zero nb).
	pose proof (Hdlen := BinNat.dt_dec_length nb).
	{	destruct BinNat.dt_dec as [b tdd], b; simpl in *.
	+	assert (Hpsl : is_precanonical (safe_zero tl))
			by (apply canonical_safe_zero; assumption).
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
			rewrite H0, rev_repeat, map_app in Hl.
			apply -> BinNat.is_canonical_struct_app in Hl; [|discriminate].
			simpl in Hl.
			unfold tail; rewrite Hzeroes, cons_uncons;
			  [|unfold is_precanonical, strip; rewrite app_comm_cons, !map_app, app_assoc; apply BinNat.is_canonical_struct_app; [discriminate|assumption] |discriminate].
			assert (forall {A : Type} (e : A) n, e :: repeat e n = repeat e (S n)) by reflexivity.
			rewrite app_comm_cons, app_assoc, H, <- repeat_app,
				Nat.add_comm, Nat.add_succ_comm, Hdlen.
			apply eq_sym, scatter_cons_zero.
			rewrite <- Hnlen, Hlen2.
			assumption.
		+	rewrite Hnone; [|reflexivity].
			pose proof (Hsez := scatter_empty_zeroes (length nb) t).
			destruct (scatter t (safe_zero empty)).
			simpl in *.
			rewrite Hsez.
			unfold tail; rewrite cons_uncons; reflexivity.
		}
	}
Qed.

Lemma drop_as_tail : forall l n,
	 	is_canonical_struct 0 l ->
		BinNat.is_canonical_struct n ->
		drop l n = fun_pow tail (BinNat.to_nat n) l.
Proof.
	intros l n Hl Hn.
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply is_canonical_struct_equiv in Hl.
	revert l Hl.
	{	induction Hn as [|n Hn HR]; intros l Hl; simpl.
	+	apply drop_zero.
		assumption.
	+	rewrite BinNat.inc_S;simpl.
		rewrite <- fun_pow_comm.
		rewrite <- HR; [|assumption].
		apply BinNat.is_canonical_struct_equiv in Hn.
		apply is_canonical_struct_equiv in Hl.
		apply eq_sym, drop_inc; assumption.
	}
Qed.

*)

End drop.
(*

Lemma lookup_drop : forall l n,
		is_valid l ->
		lookup l n = head (drop l n).
Proof.
	intros l n Hl.
	unfold lookup, drop.
	pose proof (Hv := open_valid l n).
	destruct (open l n) as [zip|]; [|reflexivity].
	specialize (Hv zip Hl eq_refl).
	destruct Hv as [_ _ Ht Hlen].
	destruct zip as [tl dl t an]; simpl in *.
	rewrite <- Hlen in Ht.
	pose proof (CLBT.open_lookup t an Ht).
	destruct CLBT.open.
	pose proof (Hsl := scatter_lookup an t (safe_zero tl) Ht).
	destruct scatter; simpl in *.
	rewrite Hsl.
	symmetry.
	apply head_cons.
Qed.

Lemma lookup_zero : forall l,
		is_canonical l ->
		lookup l [] = head l.
Proof.
	intros l Hl.
	apply canonical_valid in Hl as Hvl.
	apply is_canonical_struct_equiv in Hl.
	rewrite lookup_drop, drop_as_tail; [|assumption|reflexivity|assumption].
	reflexivity.
Qed.
Lemma lookup_inc : forall l n,
	 	is_canonical l ->
		BinNat.is_canonical n ->
		lookup l (BinNat.inc n) = lookup (tail l) n.
Proof.
	intros l n Hl Hn.
	apply canonical_valid in Hl as Hvl.
	apply tail_valid in Hvl as Hvtl.
	apply is_canonical_struct_equiv in Hl as Hl2.
	apply canonical_tail in Hl as Htl.
	apply is_canonical_struct_equiv in Htl.
	apply BinNat.is_canonical_struct_equiv in Hn as Hn2.
	apply BinNat.canonical_inc in Hn as Hin.
	apply BinNat.is_canonical_struct_equiv in Hin.
	rewrite !lookup_drop, !drop_as_tail; [|assumption..].
	rewrite BinNat.inc_S.
	reflexivity.
Qed.

Lemma comprehension : forall l0 l1,
		is_canonical l0 -> is_canonical l1 ->
		(forall n, BinNat.is_canonical n -> lookup l0 n = lookup l1 n) ->
		l0 = l1.
Proof.
	intros l0 l1 Hl0.
	revert l1.
	{	induction Hl0 as [|l0 a Hl0 HR]; intros l1 Hl1 H;
			destruct Hl1 as [|l1 b Hl1]; simpl.
	+	reflexivity.
	+	specialize (H _ BinNat.canonical_0).
		rewrite !lookup_zero, head_cons in H;
			[|apply canonical_Cons; assumption|apply canonical_Empty].
		discriminate.
	+	specialize (H _ BinNat.canonical_0).
		rewrite !lookup_zero, head_cons in H;
			[|apply canonical_Empty|apply canonical_Cons; assumption].
		discriminate.
	+	pose proof (H0 := H _ BinNat.canonical_0).
		pose proof (canonical_Cons _ a Hl0).
		pose proof (canonical_Cons _ b Hl1).
		rewrite !lookup_zero, !head_cons in H0; [|assumption..].
		inversion_clear H0.
		f_equal.
		apply HR; [assumption|].
		intros n Hn.
		specialize (H _ (BinNat.canonical_inc _ Hn)).
		rewrite !lookup_inc in H; [|assumption..].
		rewrite !cons_tail in H; [|assumption..].
		assumption.
	}
Qed.

*)

Section Theory.

Theorem lookup_update_eq : forall l n a,
		is_well_formed l ->
                BinNat.is_canonical n ->
		(to_bin l) >? n = true ->
		option_bind (update l n a) (fun l => lookup l n)
                = Some a.
Admitted.
(*
Proof.
	intros l n a Hl Hn H.

	(* hypothèses utiles *)
	pose proof (Hlookup := open_gtb (RAL.update l n a) n).
	rewrite update_strip in Hlookup; [|assumption..].
	apply RAL.canonical_valid in Hl as Hvl.
	pose proof (Hu := update_canonical _ _ a Hl Hn).
	apply BinNat.is_canonical_struct_equiv in Hn.
	apply RAL.is_canonical_struct_equiv in Hl, Hu.
	destruct Hl as [_ Hl], Hu as [_ Hu].
	pose proof (Hgs := BinNat.gtb_decomp_equiv (RAL.strip l) n Hl Hn).
	rewrite H in Hgs.
	pose proof (Hzlookup := RAL.open_zipper (RAL.update l n a) n).
	assert (Hvupdate : forall zip,
			RAL.open l n = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	pose proof (Hupdate := open_gtb l n).
	destruct BinNat.gtb_decomp as [decomp|]; [|discriminate].
	destruct decomp as [tn dn an].

	(* élimination des cas impossibles *)
	unfold RAL.lookup, RAL.update in *.
	destruct (RAL.open l n) as [zip1|], RAL.open as [zip2|] eqn:Hz2; [|discriminate..].
	specialize (Hzlookup zip2 eq_refl).
	specialize (Hvupdate zip1 eq_refl).
	destruct zip1 as [tl1 dl1 t1 nb1], zip2 as [tl2 dl2 t2 nb2].
	unfold RAL.is_zipper, RAL.plug in *.
	simpl in *.

	(* décomposition *)
	inversion Hupdate as [(Htl1, Hdl1, Hnb1)].
	inversion Hlookup as [(Htl2, Hdl2, Hnb2)].
	apply (f_equal (@length BinNat.Bit)) in Hdl1, Hdl2, Htl1, Htl2.
	rewrite !RAL.strip_length, !rev_append_rev in *.
	apply (f_equal (fun l => nth (length (rev dl1)) l RAL.Zero)) in Hzlookup.
	rewrite nth_middle, rev_length, Hdl1, <- Hdl2, <- rev_length, nth_middle in Hzlookup.
	inversion Hzlookup as [Ht2].
	f_equal.
	rewrite Hnb1.
	apply CLBT.lookup_update_eq.
	destruct Hvupdate as [_ _ Ht Hlen]; simpl in Ht, Hlen.
	rewrite <- Hlen, Hnb1 in Ht.
	rewrite BinNat.complement_length.
	assumption.
Qed. *)

Theorem lookup_update_neq : forall l n m a,
		is_well_formed l ->
                BinNat.is_canonical n ->
                BinNat.is_canonical m ->
		n <> m ->
                option_bind (RAL.update l n a) (fun l =>
                RAL.lookup l m) = RAL.lookup l m.
Admitted.
(*
Proof.
	intros l n m a Hl Hn Hm H.
	apply RAL.canonical_valid in Hl as Hvl.
	apply strip_canonical in Hl as Hsl.
	pose proof (Hzupdate := RAL.open_zipper l n).
	pose proof (Hzlookup1 := RAL.open_zipper (RAL.update l n a) m).
	pose proof (Hzlookup2 := RAL.open_zipper l m).
	assert (Hvupdate : forall zip,
			RAL.open l n = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	assert (Hvlookup2 : forall zip,
			RAL.open l m = Some zip -> RAL.valid_zipper zip)
		by (intro zip; apply RAL.open_valid; assumption).
	pose proof (Hupdate := open_gtb l n).
	pose proof (Hlookup1 := open_gtb (RAL.update l n a) m).
	pose proof (Hlookup2 := open_gtb l m).
	pose proof (Hcgt := BinNat.gtb_decomp_neq (RAL.strip l) _ _ H).
	rewrite update_strip, <- Hlookup2 in Hlookup1; [|assumption..].
	unfold RAL.lookup, RAL.update in *.
	destruct (RAL.open l n) as [zip|]; [|reflexivity].
	destruct (BinNat.gtb_decomp (RAL.strip l) n) as [decompn|]; [|discriminate].
	destruct (BinNat.gtb_decomp (RAL.strip l) m) as [decompm|],
		(RAL.open _ m) as [zipl1|], (RAL.open l m) as [zipl2|];
		try discriminate; [|reflexivity].
	specialize (Hvupdate zip eq_refl).
	specialize (Hzupdate zip eq_refl).
	specialize (Hzlookup1 zipl1 eq_refl).
	specialize (Hzlookup2 zipl2 eq_refl).
	specialize (Hvlookup2 zipl2 eq_refl).
	specialize (Hcgt decompn decompm Hsl Hn Hm eq_refl eq_refl).
	destruct zip as [tl dl t nb], zipl1 as [tl1 dl1 t1 nb1], zipl2 as [tl2 dl2 t2 nb2],
		decompn as [tn dn an], decompm as [tm dm am].
	f_equal.
	unfold RAL.is_zipper, RAL.plug in *.
	simpl in *.
	inversion Hlookup1 as [(Htl, Hdl, Hnb)].
	destruct Hvupdate as [_ _ Ht Hlnl]; simpl in Ht, Hlnl.
	destruct Hvlookup2 as [_ _ _ Hlnl2]; simpl in Hlnl2.
	apply (f_equal (@length BinNat.Bit)) in Hdl.
	rewrite !RAL.strip_length in Hdl.
	rewrite !rev_append_rev in *.
	{	destruct (PeanoNat.Nat.eq_dec (length dl) (length dl1)) as [Hlen|Hlen].
	+	rewrite <- Hlen in Hdl.
		pose proof (Hldl_copy := Hdl).
		rewrite <- (rev_length dl1), <- (rev_length dl) in Hlen.
		rewrite <- (rev_length dl2), <- (rev_length dl) in Hdl.
		apply (f_equal (fun l => nth (length (rev dl)) l RAL.Zero)) in Hzlookup1.
		rewrite nth_middle, Hlen, nth_middle in Hzlookup1.
		inversion_clear Hzlookup1.
		rewrite Hzlookup2 in Hzupdate.
		apply (f_equal (fun l => nth (length (rev dl)) l RAL.Zero)) in Hzupdate.
		rewrite nth_middle, Hdl, nth_middle in Hzupdate.
		inversion_clear Hzupdate.
		{	apply CLBT.lookup_update_neq.
		+	rewrite !BinNat.complement_length, Hlnl2, Hlnl.
			assumption.
		+	inversion_clear Hupdate.
			inversion_clear Hlookup2.
			intro Hc.
			apply BinNat.complement_inj in Hc.
			contradiction.
		+	rewrite BinNat.complement_length, Hlnl.
			assumption.
		}
	+	apply (f_equal (fun l => nth (length (rev dl1)) l (RAL.One t))) in Hzlookup1.
		rewrite nth_middle in Hzlookup1.
		{	rewrite (list_select_neq _ (rev dl) tl _
						 (RAL.One (RAL.CLBT.update t (BinNat.complement nb) a)))
				in Hzlookup1.
		+	simpl in Hzlookup1.
			rewrite <- (rev_length dl2), <- (rev_length dl1) in Hdl.
			rewrite <- Hzupdate, Hzlookup2, Hdl, nth_middle in Hzlookup1.
			inversion_clear Hzlookup1.
			reflexivity.
		+	rewrite !rev_length.
			symmetry.
			assumption.
		}
	}
Qed.
*)

End Theory.

End RAL.

