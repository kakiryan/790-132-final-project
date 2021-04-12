From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope list_scope.
From LF Require Import Maps.
From Coq Require Import Lists.List.
Import ListNotations.

(** TODO: 
    - rest of statements: while loops
    - Finish a program eval function 
    - Make notation for new concepts
    - proofs!
*)

(* 4/12/21 -- What I tried to do w/ the second half of class
  - Started towards what you had suggested with a more assembly style approach
  - Now there is just a conditonal statement type that takes in a condition and two nats. 
  These are supposed to be the location of the start of the then block vs else block. 
  (or the start of the loop body / end).
  - Problem: having trouble finding a good way to get this index from a statement. Started a function 
   to go through the program statement list to find the one that matches but this a bad approach bc there is no reason
  that you cant have the same statement twice. also couldn't get it to compile so its just a dummy for now.
  - In the notation section: had to set meaningless defaults to get it to compile. (see the empty program `p` 
    or the default end index for loops just being 0.)
  - also how to account for needing to recompute the conditon every time for loops with this strategy?
  - my thought is a lot of these issues will be fixed by maybe making a program a list of statements
  and a program counter? Just not sure how to best reflect this global pc so that we can jump around.
*)

Declare Custom Entry com.
Declare Scope com_scope.

Inductive IntExp : Type :=
| IntLit (n : Z)
| IntAdd (n1 n2: IntExp)
| IntSub (n1 n2: IntExp)
| IntMult (n1 n2: IntExp)
| IntId (x : string).

Inductive BoolExp : Type :=
  | BTrue
  | BFalse
  | Band (b1 : BoolExp) (b2 : BoolExp)
  | Bor (b1 : BoolExp) (b2 : BoolExp)
  | Bnot (b : BoolExp)
  | Bge0 (n : IntExp).

Definition state := total_map IntExp.

  (** TODO: We want a path condition to be a list of conditions on
    symbolic variables, which isn't reflected here. *)
Inductive Pathcond : Type :=
| none
| Pand (be : BoolExp) (p : Pathcond).


(** A TreeNode represents one node of our symbolic execution tree.
    It contains a program state, path condition, and an index
    into the program. The index points to a particular instruction.
*)
Inductive TreeNode : Type :=
  | Node (s : state) (pc : Pathcond) (index : nat).

(** Getters to extract information from the TreeNode object. *)

Definition extractState (n : TreeNode) : state :=
  match n with 
  | Node s _ _ => s
  end.

Definition extractIndex (n : TreeNode) : nat :=
  match n with 
  | Node _ _ i => i
  end.

Definition extractPathcond (n : TreeNode) : Pathcond :=
  match n with 
  | Node _ pc _ => pc
  end.

(** An ExecutionTree is either empty or a recursive structure
  of nodes.
  TODO: I don't think this definition is actually correct, because
  it'll only go one level deep. *)
Inductive ExecutionTree : Type :=
  | empty
  | Tr (n : TreeNode) (children : list ExecutionTree).

(** One basic instruction in the Integer language. This differs from
    the Imp implementation in Imp.v, because we don't have a
    statement of the form [stmt1 ; stmt2]. Instead, we maintain
    an ordering of statements in a list, called a Program. *)
Inductive Statement := 
  | Assignment (x: string) (a: IntExp) (* made up of a LHS loc and a RHS expr to evaluated*)
  (*TODO: once we finish the statements in the then block, how do we know to skip else? *)
  | Cond (b: BoolExp)(then_idx: nat) (else_idx: nat)  
  | Go_To (idx: nat). 

Definition Program := list Statement.

Fixpoint findStatement (prog : Program) (i : nat) : Statement :=
  match i with 
  | O => match prog with 
    | nil => Go_To 0
    | h :: t => h
  end
  | S i' => match prog with 
    | nil => Go_To 0
    | h :: t => findStatement t i'
  end
  end.


(* This is wrong, just used to get notation & eval below to work *)
Fixpoint findStatementIndex (prog: Program) (s: Statement) (start: nat) : nat :=
  match prog with
  | nil => start
  | h :: t => match s with
    | h => start 

  end
end.

(* TODO: Find somewhere to put this (can we make a notation file?) *)
Coercion IntId : string >-> IntExp.
Coercion IntLit : Z >-> IntExp.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (IntAdd x y)
  (in custom com at level 50, left associativity).
Notation "x - y" := (IntSub x y)
  (in custom com at level 50, left associativity).
Notation "x * y" := (IntMult x y)
  (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x >= 0" := (Bge0 x) (in custom com at level 70, no associativity).
Notation "x && y" := (Band x y)
  (in custom com at level 80, left associativity).
Notation "x || y" := (Bor x y)
  (in custom com at level 80, left associativity).
Notation "'~' b"  := (Bnot b)
  (in custom com at level 75, right associativity).
Notation "x := y" :=
         (Assignment x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.

Definition p: Program := []. 
Notation "'if' x 'then' y 'else' z 'end'" :=  
         (Cond x (findStatementIndex p y 0)(findStatementIndex p z 0))  (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.

(*TODO: how to compute the else index for a while loop*)
Notation "'while' x 'do' y 'end'" :=
         (Cond x (findStatementIndex p y 0) 0 )
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Open Scope com_scope. 

Fixpoint inteval (s : state) (ie : IntExp) : IntExp :=
  match ie with
  | IntLit n => IntLit n
  | <{n1 + n2}> =>  <{(inteval s n1) + (inteval s n2)}>
  | <{n1 - n2}> => <{(inteval s n1) - (inteval s n2)}>
  | <{n1 * n2}> =>  <{(inteval s n1) * (inteval s n2)}>
  | IntId n => s n
  end.

(* TODO : Add other instruction types *)
Inductive node_eval : Program -> TreeNode -> ExecutionTree -> Prop :=
  | E_Assign : forall prog node x ie1 ie2 st n pc,
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{x := ie1}> ->
    inteval st ie1 = ie2 ->
    node_eval prog node (Tr node [Tr (Node (x !-> ie2 ; st) pc (n+1)) nil])
  | E_If : forall prog node be stmt1 stmt2 idx1 idx2 st n pc,
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{if be then stmt1 else stmt2 end}> ->
    node_eval prog node (Tr node [ Tr (Node st (Pand be pc) (idx1)) nil  ;
                          Tr (Node st (Pand (Bnot be) pc) (idx2)) nil ])
  | E_GoTo: forall prog node i st n pc,
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = Go_To i ->
    node_eval prog node (Tr node [ Tr (Node st pc i) nil ])
  | E_While: forall prog node be stmt idx1 idx2 st n pc,
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{while be do stmt end}> ->
    node_eval prog node (Tr node [ Tr (Node st (Pand be pc) (idx1)) nil  ;
                          Tr (Node st (Pand (Bnot be) pc) (idx2)) nil ]).

(* TODO : Add tree evaluation relation *)

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).
