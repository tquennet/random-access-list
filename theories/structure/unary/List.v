Require Import NumRep.numerical.unary.Nat.

Open Scope unary_nat_scope.
Declare Scope unary_list_scope.
Open Scope unary_list_scope.

Inductive List (A : Type) : Type :=
| Nil : List A
| Cons : A -> List A -> List A.
	
Notation "[]" := (Nil _) : unary_list_scope.
Notation "h :: t" := (Cons _ h t) : unary_list_scope.
Notation "[ a ]" := (a :: Nil _) : unary_nat_scope.
	
Fixpoint length {A : Type} (l : List A) : Nat :=
	match l with
	| [] => 0
	| _ :: t => Su (length t)
	end.

Reserved Notation "# l" (at level 25, no associativity).
Reserved Notation "l @ r" (at level 60, right associativity).
Notation "# l" := (length l) : unary_list_scope.

Section List.
	
	Context {A : Type}.

	Notation List := (List A).

	Definition tail (l : List) :=
		match l with
		| [] => []
		| _ :: t => t
		end.
	
	Fixpoint append left right : List :=
	match left with
	| [] => right
	| x :: tleft => x :: (append tleft right)
	end.

	Fixpoint rev_append left right : List :=
	match left with
	| [] => right
	| x :: t => rev_append t (x :: right)
	end.

End List.

Notation "l @ r" := (append l r) : unary_list_scope.