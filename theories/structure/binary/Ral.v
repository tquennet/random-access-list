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
Definition dto_bin (l : dt) := List.map to_bit l.

Lemma to_bin_snoc : forall l b, to_bin (snoc l b) = snoc (to_bin l) (to_bit b).
Proof.
	apply map_snoc.
Qed.
Lemma to_bin_length : forall l, Num.length (to_bin l) = Num.length l.
Proof.
	apply mapi_length.
Qed.
Lemma to_bin_plug : forall l dl, to_bin (plug l dl) = plug (to_bin l) (dto_bin dl).
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intro l.
	+	reflexivity.
	+	cbn [plug gplug].
		rewrite HR, to_bin_snoc.
		reflexivity.
	}
Qed.

(** [card] *)

Definition card (l : t) : nat :=
  Num.foldMap Monoid_nat (fun _ => foldMap Monoid_nat CLBT.card) 0 l.

(** [is_valid] *)

Definition is_valid_ArrayBit (h: nat)(b: ArrayBit Tree) :=
  foldMap Monoid_Prop (CLBT.is_valid h) b.

Definition is_valid_k (k : nat) (l: ArrayList) :=
  Num.foldMap Monoid_Prop is_valid_ArrayBit k l.
Definition is_valid := is_valid_k 0.

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
	{	induction l as [|tl HR bl]; intros k Hn;
			[|destruct bl; destruct Hn as [Htn H]]; simpl.
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

Lemma is_dvalid_length : forall n dt, is_dvalid n dt -> List.length dt = n.
Proof.
	intro n.
	{	induction n as [|n HR]; intros dt H; inversion_clear H; simpl.
	+	reflexivity.
	+	rewrite (HR dl); [reflexivity | assumption].
	}
Qed.

Lemma is_valid_plug : forall dl l n,
		is_valid_k n l -> is_dvalid n dl ->
		is_valid (plug l dl).
Proof.
	intros dl l n.
	revert dl l.
	{	induction n as [|n HR]; intros dl l Hl Hdl.
	+	inversion_clear Hdl.
		assumption.
	+	inversion_clear Hdl as [|? b tdl Hb Htdl].
		cbn [plug gplug].
		apply HR; [|assumption].
		split; [assumption|].
		destruct b; assumption.
	}
Qed.

(** [is_canonical] *)

Definition is_canonical (l: t) := BinNat.is_canonical (to_bin l).

Lemma is_canonical_tl : forall l b, is_canonical (snoc l b) -> is_canonical l.
Proof.
	intros l b Hl.
	unfold is_canonical, to_bin in *.
	rewrite map_snoc in Hl.
	apply BinNat.is_canonical_tl in Hl.
	assumption.
Qed.

Definition ssnoc (l : t) (b : ArrayBit Tree) :=
	match l, b with
	| Ob, Zero => Ob
	| _, _ => snoc l b
	end.

Definition splug := gplug ssnoc.

Lemma ssnoc_to_bin : forall (l : t) b, to_bin (ssnoc l b) = BinNat.ssnoc (to_bin l) (to_bit b).
Proof.
	intros l b.
	unfold to_bin.
	{	destruct l; simpl.
	+	destruct b; reflexivity.
	+	destruct b; rewrite map_snoc; reflexivity.
	}
Qed.

Lemma ssnoc_valid : forall (l : t) b k,
		is_valid_k (S k) l -> is_valid_ArrayBit k b -> is_valid_k k (ssnoc l b).
Proof.
	intros l b k Hl Hb.
	destruct l, b; [apply I|..]; split; assumption.
Qed.

Lemma ssnoc_canonical : forall l b, is_canonical l -> is_canonical (ssnoc l b).
Proof.
	intros l b Hl.
	unfold is_canonical in *.
	rewrite ssnoc_to_bin.
	apply BinNat.is_canonical_ssnoc.
	assumption.
Qed.

Lemma splug_valid : forall l dl k, is_valid_k k l -> is_dvalid k dl -> is_valid (splug l dl).
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intros l k Hl Hdl; cbn [splug gplug].
	+	apply is_dvalid_length in Hdl; simpl in Hdl.
		rewrite <- Hdl in Hl.
		assumption.
	+	revert Hl; inversion_clear Hdl as [| k' ? ? Hbl Htl]; intro Hl.
		apply (HR _ k'); [|assumption].
		apply ssnoc_valid; assumption.
	}
Qed.

Lemma splug_canonical : forall l dl, is_canonical l -> is_canonical (splug l dl).
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intros l Hl; cbn [splug gplug].
	+	assumption.
	+	apply HR, ssnoc_canonical.
		assumption.
	}
Qed.

Lemma splug_to_bin : forall l dl, to_bin (splug l dl) = BinNat.splug (to_bin l) (dto_bin dl).
Proof.
	intros l dl.
	revert l.
	{	induction dl as [|bl tl HR]; intro l; cbn [splug gplug]; simpl.
	+	reflexivity.
	+	rewrite HR.
		cbn [BinNat.splug gplug].
		rewrite ssnoc_to_bin.
		reflexivity.
	}
Qed.

(** [is_well_formed] *)

Lemma plug_eq_splug : forall l dl, is_canonical (plug l dl) -> plug l dl = splug l dl.
Proof.
	{	assert (Ha : forall dl l, l <> Ob -> plug l dl = splug l dl).
	+	intro dl.
		{	induction dl as [|bl tl HR]; intros l H.
		+	reflexivity.
		+	destruct l; [contradiction|].
			destruct bl; cbn [plug splug gplug]; (rewrite HR; [reflexivity|discriminate]).
		}
	+	intros l dl H.
		destruct l as [|bl tl]; [|apply Ha; discriminate].
		destruct dl as [|bl tl]; [reflexivity|].
		destruct bl; [|apply (Ha tl); discriminate].
		unfold is_canonical in H.
		rewrite (to_bin_plug Ob) in H; simpl in H.
		apply BinNat.non_canonical_rev in H.
		contradiction.
	}
Qed.

Record is_well_formed (l: t) := mk_wf {
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
	Num.mapi (create_ArrayBit a) O n.

(** This implementation accumulates [t] along so as to be more
efficient than the one presented in the paper. *)

Fixpoint create_aux n (t: Tree) :=
	match n with
	| Ob => Ob
	| snoc tn 0 => snoc (create_aux tn (CLBT.Node t t)) Zero
	| snoc tn 1 => snoc (create_aux tn (CLBT.Node t t)) (One t)
	end.

Definition create n a := create_aux n (CLBT.singleton a).

Lemma create_meets_spec: forall n a, create n a = create_spec n a.
Proof.
	intros n a.
	enough (H : forall k t,
		t = CLBT.create a k -> create_aux n t = Num.mapi (create_ArrayBit a) k n)
		by (apply H; reflexivity).
	{	induction n as [|tn HR bn]; [|destruct bn]; intros k t Ht; simpl.
	+	reflexivity.
	+	specialize (HR (S k) (CLBT.Node t t)).
		rewrite HR; [reflexivity|].
		rewrite Ht.
		reflexivity.
	+	specialize (HR (S k) (CLBT.Node t t)).
		rewrite HR, Ht; [reflexivity|].
		rewrite Ht.
		reflexivity.
	}
Qed.

Lemma create_valid : forall n a, is_valid (create n a).
	intros n a.
	rewrite create_meets_spec.
	enough (H : forall k, is_valid_k k (Num.mapi (create_ArrayBit a) k n)) by (apply H).
	{	induction n as [|tn HR bn]; [|destruct bn]; intro k.
	+	apply I.
	+	split; [apply HR | apply I].
	+	split; [apply HR | apply CLBT.create_valid].
	}
Qed.

Theorem to_bin_create : forall n a, to_bin (create n a) = n.
Proof.
	intros n a.
	enough (H : forall t, to_bin (create_aux n t) = n) by (apply H).
	unfold to_bin.
	{	induction n as [|tn HR bn]; simpl; intro t.
	+	reflexivity.
	+	destruct bn; rewrite map_snoc, HR; reflexivity.
	}
Qed.

Lemma create_canonical : forall n (a : A),
		BinNat.is_canonical n ->
		is_canonical (create n a).
Proof.
	intros n a H.
	unfold is_canonical.
	rewrite to_bin_create.
	assumption.
Qed.

Lemma create_well_formed : forall n a, BinNat.is_canonical n -> is_well_formed (create n a).
Proof. constructor; auto using create_canonical, create_valid. Qed.

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

Lemma cons_tree_valid : forall (l : t) (clbt : CLBT.t) {n : nat},
	is_valid_k n l -> CLBT.is_valid n clbt ->
	is_valid_k n (cons_tree clbt l).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [|t]];
			simpl; intros clbt n Hl Hclbt.
	+	split; assumption.
	+	destruct Hl as [Htl Hbl].
		split; assumption.
	+	destruct Hl as [Htl Hbl].
		split; [|apply I].
		pose proof (CLBT.valid_Node _ _ Hbl Hclbt).
		apply HR; assumption.
	}
Qed.

Lemma cons_valid : forall (a : A) (l : t),
	is_valid l -> is_valid (cons a l).
Proof.
Proof.
	intros a l H.
	{	apply cons_tree_valid.
	+	exact H.
	+	apply CLBT.singleton_valid.
	}
Qed.


Lemma cons_tree_inc : forall (l : t) (clbt : CLBT.t),
	to_bin (cons_tree clbt l) = BinNat.inc (to_bin l).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl].
	+	reflexivity.
	+	reflexivity.
	+	intro clbt.
		rewrite to_bin_snoc.
		simpl.
		rewrite to_bin_snoc, HR.
		reflexivity.
	}
Qed.

Theorem cons_inc : forall (l : t) (a : A),
	to_bin (cons a l) = BinNat.inc (to_bin l).
Proof. intros; eauto using cons_tree_inc. Qed.

End cons.

(** [uncons], [hd], [tl] *)

Section Uncons.

Fixpoint uncons (l : t) : option (CLBT.t * t) :=
	match l with
	| Ob => None
	| snoc t (One clbt) => Some (clbt, ssnoc t Zero)
	| snoc t Zero =>
            option_bind (uncons t) (fun '(clbt, r) => 
            match clbt with
            | CLBT.Leaf _ => None
            | CLBT.Node lt rt => Some (rt, snoc r (One lt))
            end)
	end.

Lemma uncons_valid_k : forall l k, is_valid_k k l ->
		option_lift (fun p => CLBT.is_valid k (fst p) /\ is_valid_k k (snd p)) (uncons l).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [|t]]; intros k Hl; simpl.
	+	apply I.
	+	destruct Hl as [Htl Hbl].
		eapply lift_bind_conseq; [|apply HR, Htl].
		intros x Hx.
		destruct x as [t r], Hx as [Ht Hr]; simpl in *.
		inversion_clear Ht as [| ? lt rt Hlt Hrt]; simpl.
		split; [|split]; assumption.
	+	destruct Hl as [Htl Hbl].
		split; [assumption|].
		apply ssnoc_valid; [assumption|apply I].
	}
Qed.
Theorem uncons_valid : forall l, is_valid l ->
		option_lift (fun p => CLBT.is_valid 0 (fst p) /\ is_valid (snd p)) (uncons l).
Proof.
	intros l Hl.
	apply uncons_valid_k.
	assumption.
Qed.

Lemma uncons_positive : forall l k,
		is_valid_k k l ->
		BinNat.is_positive (to_bin l) ->
		exists a r, uncons l = Some (a, r).
Proof.
	intros l.
	{	induction l as [|tl HR bl]; intros k Hv Hp;
			[|destruct bl; rewrite to_bin_snoc in Hp];
			inversion_clear Hp as [|? Htp |? Htp]; simpl.
	+	destruct Hv as [Hv _].
		apply uncons_valid_k in Hv as Hrv.
		destruct (HR _ Hv Htp) as [t H], H as [r H].
		rewrite H in *; simpl in *.
		destruct Hrv as [Hrv _].
		inversion_clear Hrv.
		eexists; eexists; reflexivity.
	+	eexists; eexists; reflexivity.
	+	eexists; eexists; reflexivity.
	}
Qed.

Theorem uncons_dec : forall l, is_valid l ->
    	option_map (fun p => to_bin (snd p)) (uncons l) = BinNat.dec (to_bin l).
Proof.
	intro l.
	enough (H : forall k, is_valid_k k l ->
    	option_map (fun p => to_bin (snd p)) (uncons l) = BinNat.dec (to_bin l))
		by (apply H).
	{	induction l as [|tl HR bl]; [|destruct bl]; intros k Hl.
	+	reflexivity.
	+	rewrite to_bin_snoc; simpl.
		destruct Hl as [Htl Hbl].
		rewrite <- (HR _ Htl).
		apply uncons_valid_k in Htl.
		destruct (uncons tl) as [p|]; [destruct p as [t r]|reflexivity]; simpl in *.
		destruct Htl as [Ht Hr].
		inversion_clear Ht; simpl.
		rewrite to_bin_snoc.
		reflexivity.
	+	rewrite to_bin_snoc; simpl.
		rewrite ssnoc_to_bin.
		reflexivity.
	}
Qed.

Theorem uncons_canonical : forall l, is_well_formed l ->
		option_lift (fun r => is_canonical (snd r)) (uncons l).
Proof.
	intros l Hl.
	destruct Hl as [Hvl Hcl].
	unfold is_canonical.
	rewrite <- lift_map, uncons_dec; [|assumption].
	apply BinNat.dec_canonical.
	assumption.
Qed.

Definition hd (l : t) : option A := 
  option_bind (uncons l) (fun t =>
  match t with 
  | (CLBT.Leaf a, _) => Some a
  | _ => (* Impossible if [is_well_formed l] ! *) None
  end).


Definition tl (l : t) : option t := option_map snd (uncons l).

Lemma tl_valid : forall (l : t),
	is_valid l -> option_lift is_valid (tl l).
Proof.
	intros l Hl.
	unfold tl.
	eapply lift_map_conseq, uncons_valid; [|assumption]; simpl.
	intro x.
	apply proj2.
Qed.

Lemma tl_canonical : forall l,
		is_well_formed l ->
		option_lift is_canonical (tl l).
Proof.
	intros l Hl.
	unfold tl.
	eapply lift_map_conseq, uncons_canonical; [|assumption]; simpl.
	intros x Hx.
	assumption.
Qed.

Theorem tl_well_formed: forall l, is_well_formed l -> option_lift is_well_formed (tl l).
Proof.
	intros l Hl.
	pose proof (Hv := tl_valid _ (wf_valid _ Hl)).
	pose proof (Hc := tl_canonical _ Hl).
	unfold tl in *.
	destruct (uncons l); [|apply I].
	split; assumption.
Qed.

End Uncons.

(** [open] *)

Section open.

Record zipper := mkZip
{
	z_suffix : t;
	z_tree : Tree;
	z_prefix : dt;
	z_idx : BinNat.dt;
}.

Definition is_zipper l zip := l = plug zip.(z_suffix) (One zip.(z_tree) :: zip.(z_prefix)).

Record is_zvalid (z : zipper) :=
{
	dec_rtl : is_valid_k (S (List.length z.(z_idx))) z.(z_suffix);
	dec_rdl : is_dvalid (List.length z.(z_idx)) z.(z_prefix);
	dec_rt : CLBT.is_valid (List.length z.(z_idx)) z.(z_tree);
	del_rn : List.length z.(z_prefix) = List.length z.(z_idx);
}.

Fixpoint open_aux (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) :=
	match l, n with
	| Ob, _ => None
	| _, Ob => (* Impossible if [is_positive n] *) None
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

Fixpoint open_eq (l : t) (n : BinNat.t) (dbn : BinNat.dt) (dral : dt) :=
	match l, n with
	| Ob, Ob => Some None
	| Ob, _ => None
	| snoc tl (Zero as bit), Ob =>
            option_map Some (open_borrow tl Ob (1 :: dbn) (bit :: dral))
	| snoc tl (One t), Ob => Some (Some (mkZip tl t dral dbn))
	| snoc tl (Zero as bit), snoc tn 0 | snoc tl (One _ as bit), snoc tn 1 =>
		open_eq tl tn (1 :: dbn) (bit :: dral)
	| snoc tl (Zero as bit), snoc tn 1 =>
		option_map Some (open_borrow tl tn (0 :: dbn) (bit :: dral))
	| snoc tl (One _ as bit), snoc tn 0 =>
		option_map Some (open_aux tl tn (0 :: dbn) (bit :: dral))
	end.

Definition open l n := open_eq l n [] [].

Definition dec_zip zip :=
	match BinNat.dt_dec zip.(z_idx) with
	| (false, r) => open_eq zip.(z_suffix) Ob (1 :: r)
									   (One zip.(z_tree) :: zip.(z_prefix))
	| (true, r) => Some (Some (mkZip zip.(z_suffix) zip.(z_tree) zip.(z_prefix) r))
	end.

Lemma open_aux_valid : forall (l : t) n dbn dl,
		is_valid_k (List.length dbn) l -> is_dvalid (List.length dbn) dl ->
		option_lift is_zvalid (open_aux l n dbn dl)
with open_borrow_valid: forall (l : t) n dbn dl,
		is_valid_k (List.length dbn) l -> is_dvalid (List.length dbn) dl ->
		option_lift is_zvalid (open_borrow l n dbn dl).
Proof.
		all : intros l n dbn dl Hl Hdl;
			(destruct l as [|tl bl]; [|destruct bl as [|t];
				destruct Hl as [Htl Hbl]; pose proof(H := valid_DCons _ _ _ Hbl Hdl)]);
			(destruct n as [|tn bn]; [|destruct bn]);
			simpl in *; try apply I.
	+	apply open_aux_valid; assumption.
	+	apply open_borrow_valid; assumption.
	+	destruct tn; apply open_aux_valid; assumption.
	+	destruct tn; [|apply open_aux_valid; assumption]; simpl.
		apply is_dvalid_length in Hdl as Hl.
		split; assumption.
	+	apply open_borrow_valid; assumption.
	+	apply open_borrow_valid; assumption.
	+	apply open_borrow_valid; assumption.
	+	apply is_dvalid_length in Hdl as Hl.
		split; assumption.
	+	apply open_aux_valid; assumption.
	+	apply open_borrow_valid; assumption.
Qed.

Lemma open_eq_valid : forall l n dbn dl,
		is_valid_k (List.length dbn) l -> is_dvalid (List.length dbn) dl ->
		option_lift (option_lift is_zvalid) (open_eq l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; intros n dbn dl Hl Hdl; [|destruct bl as [|t];
			destruct Hl as [Htl Hbl]; pose proof(H := valid_DCons _ _ _ Hbl Hdl)];
			(destruct n as [|tn bn]; [|destruct bn]); simpl in *; try apply I.
	+	eapply lift_map_conseq, open_borrow_valid; [trivial|assumption..].
	+	apply HR; assumption.
	+	eapply lift_map_conseq, open_borrow_valid; [trivial|assumption..].
	+	apply is_dvalid_length in Hdl as Hl.
		split; assumption.
	+	eapply lift_map_conseq, open_aux_valid; [trivial|assumption..].
	+	apply HR; assumption.
	}
Qed.		

Theorem open_valid : forall l n,
		is_valid l ->
		option_lift (option_lift is_zvalid) (open l n).
Proof.
	intros l n Hl.
	apply open_eq_valid; [assumption|apply valid_DNil].
Qed.


Lemma open_zipper_aux : forall l n dbn dl,
		option_lift (is_zipper (plug l dl)) (open_aux l n dbn dl)
with open_zipper_borrow : forall l n dbn dl,
		option_lift (is_zipper (plug l dl)) (open_borrow l n dbn dl).
Proof.
	all: intro l; destruct l as [|tl bl]; [|destruct bl as [|t]]; intros n dbn dl;
		(destruct n as [|tn bn]; [|destruct bn]); try apply I; simpl in *.
	+	apply (open_zipper_aux tl).
	+	apply (open_zipper_borrow tl).
	+	destruct tn; apply (open_zipper_aux tl).
	+	destruct tn; [reflexivity|apply (open_zipper_aux tl)].
	+	apply (open_zipper_borrow tl).
	+	apply (open_zipper_borrow tl).
	+	apply (open_zipper_borrow tl).
	+	reflexivity.
	+	apply (open_zipper_aux tl).
	+	apply (open_zipper_borrow tl).
Qed.

Lemma open_zipper_eq : forall l n dbn dl,
		option_lift (option_lift (is_zipper (plug l dl))) (open_eq l n dbn dl).
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [|t]]; intros n dbn dl;
		(destruct n as [|tn bn]; [|destruct bn]); try apply I; simpl in *.
	+	eapply lift_map_conseq, open_zipper_borrow; trivial.
	+	apply HR.
	+	eapply lift_map_conseq, open_zipper_borrow; trivial.
	+	reflexivity.
	+	eapply lift_map_conseq, open_zipper_aux; trivial.
	+	apply HR.
	}
Qed.
Lemma open_zipper : forall l n, option_lift (option_lift (is_zipper l)) (open l n).
Proof.
	intros l n.
	apply open_zipper_eq.
Qed.


Let __forget_zipper :=
	option_map (fun z => BinNat.mkZip (to_bin z.(z_suffix))
		(dto_bin z.(z_prefix)) z.(z_idx)).
Definition forget_zipper :=
	option_map __forget_zipper.



Lemma open_gt_aux : forall l n (dl : dt) dn,
		__forget_zipper (open_aux l n dn dl)
			= BinNat.gt_aux (to_bin l) n (dto_bin dl) dn
with open_gt_borrow : forall l n dl dn,
		__forget_zipper (open_borrow l n dn dl)
			= BinNat.gt_borrow (to_bin l) n (dto_bin dl) dn.
Proof.
		all : intros l n dbn dl;
			(destruct l as [|tl bl]; [|destruct bl as [|t]]);
			(destruct n as [|tn bn]; [|destruct bn]);
			try rewrite to_bin_snoc; try reflexivity; simpl in *.
	+	apply open_gt_aux.
	+	apply open_gt_borrow.
	+	destruct tn; apply open_gt_aux.
	+	destruct tn; [reflexivity|apply open_gt_aux].
	+	apply open_gt_borrow.
	+	apply open_gt_borrow.
	+	apply open_gt_borrow.
	+	apply open_gt_aux.
	+	apply open_gt_borrow.
Qed.

Lemma open_gt_eq : forall (l : t) n (dl : dt) dn,
		forget_zipper (open_eq l n dn dl)
			= BinNat.gt_eq (to_bin l) n (dto_bin dl) dn.
Proof.
	intro l.
	{	induction l as [|tl HR bl]; [|destruct bl as [|t]]; intros n dl dn;
		(destruct n as [|tn bn]; [|destruct bn]);
			try rewrite to_bin_snoc; simpl in *; try reflexivity; unfold forget_zipper.
	+	pose proof (H := open_gt_borrow tl Ob (Zero :: dl) (1 :: dn)).		
		destruct BinNat.gt_borrow, open_borrow; simpl;
			[rewrite <- H|discriminate..|]; reflexivity.
	+	apply HR.
	+	pose proof (H := open_gt_borrow tl tn (Zero :: dl) (0 :: dn)).		
		destruct BinNat.gt_borrow, open_borrow; simpl;
			[rewrite <- H|discriminate..|]; reflexivity.
	+	pose proof (H := open_gt_aux tl tn ((One t) :: dl) (0 :: dn)).
		destruct BinNat.gt_aux, open_aux; simpl;
			[rewrite <- H|discriminate..|]; reflexivity.
	+	apply HR.
	}
Qed.

Theorem open_gt : forall l n,
    forget_zipper (open l n) = BinNat.gt (to_bin l) n.
Proof.
	intros l n.
	apply open_gt_eq.
Qed.

End open.

(** [lookup] *)

Section lookup.

Definition lookup l n :=
  match open l n with
  | Some {| z_tree := t; z_idx := idx |} =>
      CLBT.lookup t idx
  | _ => None
  end.
End lookup.

(** [update] *)

Section update.

Definition update l n a :=
	option_bind (open l n) (fun z => option_bind (CLBT.update z.(z_tree) z.(z_idx) a)
		(fun t => Some (plug (snoc z.(z_suffix) (One t)) z.(z_prefix)))).

Lemma is_valid_update : forall l n a, is_valid l -> option_lift is_valid (update l n a).
Proof.
	intros l n a Hl.
	unfold update.
	pose proof (Hv := open_valid l n Hl).
	eapply lift_bind_conseq, Hv.
	intros z Hz.
	destruct z as [tl dl t idx], Hz as [Htl Hdl Ht Hlen]; simpl in *.
	eapply lift_bind_conseq, CLBT.update_valid; [|assumption]; simpl.
	intros t' Ht'.
	apply (is_valid_plug _ _ (List.length idx)); [split|]; assumption.
Qed.

Lemma update_to_bin : forall l n a,
		option_lift (fun u => to_bin u = to_bin l) (update l n a).
Proof.
	intros l n a.
	unfold update.
	pose proof (H := open_zipper l n).
	eapply lift_bind_conseq, H.
	intros z Hz; unfold is_zipper in Hz.
	apply lift_bind; intro t; simpl; cbn [plug gplug] in Hz.
	apply (f_equal to_bin) in Hz.
	rewrite Hz, !to_bin_plug, !to_bin_snoc; simpl in *.
	reflexivity.
Qed.
Lemma is_canonical_update : forall l n a,
		is_canonical l -> option_lift is_canonical (update l n a).
Proof.
	intros l n a Hl.
	pose proof (H := update_to_bin l n a).
	eapply lift_conseq, H; simpl.
	intros x Hx.
	unfold is_canonical.
	rewrite Hx.
	assumption.
Qed.

Theorem is_well_formed_update : forall l n a, is_well_formed l -> option_lift is_well_formed (update l n a).
Proof.
	intros l n a H.
	pose proof (Hv := is_valid_update l n a (wf_valid _ H)).
	pose proof (Hc := is_canonical_update l n a (wf_canonical _ H)).
	destruct update; [split; assumption|apply I].
Qed.

End update.

(** [drop] *)

Section drop.

Fixpoint scatter t dn: option (A * list (ArrayBit Tree)) :=
	match t, dn with
	| CLBT.Leaf a, [] => Some (a, [])
	| CLBT.Node lt rt, 1 :: tn =>
            option_map (fun '(a, p) => (a, One lt :: p)) (scatter rt tn)
	| CLBT.Node lt _, 0 :: tn => 
            option_map (fun '(a, p) => (a, Zero :: p))  (scatter lt tn)
        | _, _ => (* Impossible if [t] and [dn] are coherent *) None
	end.

Lemma scatter_to_bin : forall (t : Tree) dn, CLBT.is_valid_idx dn t ->
		option_map (fun p => dto_bin (snd p)) (scatter t dn) = Some dn.
Proof.
	intros t dn.
	revert t.
	{	induction dn as [|bn tn HR]; intros t Ht;
			inversion_clear Ht as [a|? l r Hl Hr]; simpl.
	+	reflexivity.
	+	destruct bn; [pose proof (H := (HR _ Hl))|pose proof (H := (HR _ Hr))];
			(destruct scatter as [p|]; [destruct p as [a dl]|discriminate]); simpl in *;
			inversion_clear H; reflexivity.
	}
Qed.
Definition drop l n :=
	option_bind (open l n) (fun z => option_bind (scatter z.(z_tree) z.(z_idx))
		(fun '(a, p) => Some (cons a (splug z.(z_suffix) (Zero :: p))))).

Lemma drop_sub : forall l n, is_valid l ->
		option_map to_bin (drop l n) = (to_bin l) - n.
Proof.
	intros l n Hl.
	pose proof (Hv := open_valid l n Hl).
	pose proof (H := open_gt l n).
	unfold drop, BinNat.sub.
	rewrite <- H.
	destruct open as [z|]; [|reflexivity]; simpl in *.
	destruct z as [tl t dl idx], Hv as [_ _ Ht _]; simpl in *.
	pose proof (Hs := scatter_to_bin t idx Ht).
	destruct scatter as [s|]; [destruct s as [sa sdl]|discriminate]; simpl in *.
	rewrite cons_inc, splug_to_bin.
	cbn [dto_bin List.map to_bit].
	inversion_clear Hs.
	reflexivity.
Qed.
Lemma drop_canonical : forall l n,
		is_well_formed l -> BinNat.is_canonical n -> option_lift is_canonical (drop l n).
Proof.
	intros l n Hl Hn.
	destruct Hl as [Hv Hc].
	pose proof (Hds := drop_sub l n Hv).
	pose proof (Hs := BinNat.sub_canonical (to_bin l) n Hc Hn).
	rewrite <- Hds, lift_map in Hs.
	eapply lift_conseq, Hs; simpl.
	intros x Hx.
	assumption.
Qed.


Lemma scatter_valid : forall t dn, CLBT.is_valid_idx dn t -> 
		option_lift (fun p => is_dvalid (List.length dn) (snd p)) (scatter t dn).
Proof.
	intros t dn.
	revert t.
	{	induction dn as [|bn tn HR]; intros t Ht;
			inversion_clear Ht as [a|? l r Hl Hr]; simpl.
	+	apply valid_DNil.
	+	pose proof (I).
		destruct bn;
		(eapply lift_map_conseq, HR; [|assumption]); simpl;
		intros x Hx; destruct x as [a p];
		apply valid_DCons; assumption.
	}
Qed.

Lemma drop_valid : forall l n, is_valid l -> option_lift is_valid (drop l n).
Proof.
	intros l n Hl.
	unfold drop.
	eapply lift_bind_conseq, open_valid; [|assumption].
	intros x Hx.
	destruct x as [tl t dl idx], Hx as [Htl _ Ht _]; simpl in *.
	eapply lift_bind_conseq, scatter_valid; [|assumption]; simpl.
	intros x Hx.
	destruct x as [a p]; simpl in Hx.
	apply (valid_DCons _ Zero) in Hx; [|apply I].
	apply cons_valid, (splug_valid _ _ (S (List.length idx))); assumption.
Qed.

Lemma is_well_formed_drop : forall l n,
		is_well_formed l -> BinNat.is_canonical n -> option_lift is_well_formed (drop l n).
Proof.
	intros l n Hl Hn.
	pose proof (Hc := drop_canonical l n Hl Hn).
	pose proof (Hdv := drop_valid l n (wf_valid _ Hl)).
	destruct drop; [|apply I].
	split; assumption.
Qed.

End drop.

End RAL.

