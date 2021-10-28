From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope list_scope.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Structures.OrderedTypeEx.
Import ListNotations.

Open Scope string_scope.

Declare Custom Entry com.
(* Declare Scope com_scope *)

(* ============= Start: Definition of Symbolic Execution Concepts. =============== *)

(** Inspired by the AExp from the Imp chapter. The only difference is that 
    we are using the built-in integer type, Z. The Integer language as defined in
    the King paper only provides support for addition, subtraction and
    multiplcation, similar to Imp. *)
Inductive IntExp : Type :=
  | IntLit (n : Z)
  | IntAdd (n1 n2: IntExp)
  | IntSub (n1 n2: IntExp)
  | IntMult (n1 n2: IntExp)
  | IntId (x : string).

(** The state of a program during symbolic execution is represtented by a total map
    of symbolic expressions. The symbolic expressions themselves are integer
    expressions with symbolic variables. *)
Inductive SymbolicExp : Type :=
  | Symbol (s: string)
  | SymAdd (s1 s2: SymbolicExp)
  | SymSub (s1 s2: SymbolicExp)
  | SymMult (s1 s2: SymbolicExp)
  | Constant (n : Z).

(** Also inspired by the BExp from Imp. The only boolean expression allowed in the 
    King paper is the check that something is >=, so we only provide support for that
    case and negation.*)
Inductive BoolExp : Type :=
  | BTrue
  | BFalse
  | Bnot (b : BoolExp)
  | Bge0 (n : IntExp).

Inductive SBoolExp : Type :=
  | SBTrue
  | SBFalse
  | SBnot (b : SBoolExp)
  | SBge0 (n : SymbolicExp).

(** We represent a symbolic program state as a total map of symbolic expressions
    and the concrete state is a total map of Integers. *)
Definition state := list (string * SymbolicExp).
Definition concreteState := list (string * Z).

(** Determine whether a given symbolic state is empty. *)
Fixpoint isEmpty (s : state) : bool :=
  match s with
  | nil => true 
  | (k, v) :: s' =>
    match v with
    | Symbol _ => isEmpty s'
    | _ => false
    end 
  end.

Fixpoint applyState (s : state) (x : string) : SymbolicExp :=
  match s with
  | nil => Constant 0
  | (k, v) :: s' =>
    if (string_dec k x) then v else (applyState s' x)
  end.

Fixpoint applyCState (s : concreteState) (x : string) : Z :=
  match s with
  | nil => 0
  | (k, v) :: s' =>
    if (string_dec k x) then v else (applyCState s' x)
  end.

(** A path condition is a list of boolean expressions connected by conjunction. *)
Definition PathCond  := list SBoolExp.
            
(** This function is used to resolve a symbolic expression to an integer, given
    a concrete state. *)
Fixpoint substituteInt (se: SymbolicExp) (mappings: concreteState): Z  :=
  match se with
  | Symbol s => applyCState mappings s
  | SymAdd s1 s2 => (substituteInt s1 mappings) + (substituteInt s2 mappings)
  | SymSub s1 s2 => (substituteInt s1 mappings) - (substituteInt s2 mappings)
  | SymMult s1 s2 => (substituteInt s1 mappings) * (substituteInt s2 mappings)
  | Constant n => n
  end.

Fixpoint substituteBool (sb: SBoolExp) (mappings: concreteState) : bool :=
  match sb with
  | SBTrue => true 
  | SBFalse => false 
  | SBnot b => negb (substituteBool b mappings)
  | SBge0 se => 0 <=? (substituteInt se mappings)
  end.

(** This function is used to evaluate an integer expression, similar to Imp but taking
    into account our symbolic notion of program state. *)
Fixpoint inteval (ie: IntExp) (mappings: concreteState) : Z :=
  match ie with 
  | IntLit n => n
  | IntAdd n1 n2 => (inteval n1 mappings) + (inteval n2 mappings)
  | IntSub n1 n2 => (inteval n1 mappings) - (inteval n2 mappings)
  | IntMult n1 n2 => (inteval n1 mappings) * (inteval n2 mappings)
  | IntId x => applyCState mappings x
end.
    
    
(** This function is used to evaluate a boolean expression, similar to Imp but taking
    into account our notion of program state. *)
Fixpoint beval (b : BoolExp) (mappings: concreteState) : bool :=
  match b with
  | BTrue  => true
  | BFalse => false
  | Bnot b => negb (beval b mappings)
  | Bge0 n => 0 <=? inteval n mappings
  end.

(** This function is used to evaluate a path condition given a concrete state. *)
Fixpoint eval_pc (pc: PathCond) (mappings: concreteState) : bool :=
  match pc with 
  | nil => true
  | h :: t => (substituteBool h mappings) && (eval_pc t mappings)
  end.


(** For simplicity, any program we work with will have up to three parameters
    and three local variables, called A, B, C and X, Y, Z, respectively.
    The values sA, sB, and sC are the symbolic variables which replace
    A, B, and C when creating the symbolic expressions. *)
Definition A: string := "A".
Definition sA: SymbolicExp := Symbol A.
Definition B: string := "B".
Definition sB: SymbolicExp := Symbol B.
Definition C: string := "C".
Definition sC: SymbolicExp := Symbol C.
Definition X: string := "X".
Definition Y: string := "Y".
Definition Z: string := "Z".

(** The empty state will map each parameter to its symbolic variable, and
    each local variable to the default value of 0. *)
Definition empty_st := [(A, sA); (B, sB); (C, sC)].

(** SAT is a property of any given path condition, saying that there exist concrete 
    values which make it satisfiable. *)
Definition SAT (pc: PathCond) := exists (cs: concreteState), eval_pc pc cs = true.

(** For example, The trivial path condition 'true' is satisfiable by the
    map that takes each symbolic variable to 0. *)
Definition ex_pc := [SBTrue].
Example ex_pc_sat : SAT ex_pc.
Proof.
  unfold SAT. exists nil. simpl. reflexivity.
Qed.

(** When we evaluate ex_pc with this trivial path condition, we get the boolean
    true. *)
Definition SAT_assign_ex_1: concreteState := 
  [(A, 1); (B, 2); (C, 1); (X, 3); (Y, 3); (Z, 4)].
Compute eval_pc ex_pc SAT_assign_ex_1.


(** For another example, we prove that the path condition
    sA >= 0
    is satisfiable by the map that takes sA to 1 and all other symbolic
    variables to 0. *)
Definition ex_pc_2 := [ SBTrue; (SBge0 (Symbol A))].
Definition SAT_assign_ex_2: concreteState := [(A, 1)].
Compute eval_pc ex_pc SAT_assign_ex_2.
Example ex_pc_sat_2 : SAT ex_pc_2.
Proof.
  unfold SAT. exists SAT_assign_ex_2. simpl. reflexivity.
Qed.

(** A TreeNode represents one node of our symbolic execution tree.
    It contains a program state, path condition, and an index
    into the program. The index points to a particular statement in the program. *)
Inductive TreeNode : Type :=
  | Node (s : state) (pc : PathCond) (index : nat).
  
Notation "<< s , pc , i >>" := (Node s pc i).

Definition empty_node := <<nil, nil, 0>>.

(** Getters to extract information from the TreeNode object. *)

Definition extractState (n : TreeNode) : state :=
  match n with 
  | <<s, _, _>> => s
  end.

Definition extractIndex (n : TreeNode) : nat :=
  match n with 
  | <<_, _, i>> => i
  end.

Definition extractPathCond (n : TreeNode) : PathCond :=
  match n with 
  | <<_, pc, _>> => pc
  end.

(** An ExecutionTree is either empty or a root node with left and right
    child trees. *)
Inductive ExecutionTree : Type :=
  | empty
  | Tr (n : TreeNode) (l : ExecutionTree) (r : ExecutionTree).
  
(** Now we define a basic instruction in the Integer language. This differs from
    the Imp implementation in Imp.v, because we don't have a
    statement of the form [stmt1 ; stmt2]. Instead, we maintain
    an ordering of statements in a list, called a Program. 

    In addition to basic assignment, we provide support for the same control 
    flow structures as in the King paper -- if/else, while loops,
    and function calls modeled by go_tos.

    - Assignment statements require a variable name (string) and an integer
      expression. The value of this variable is updated in the program state.

    - If statements are represented by a boolean expression for the condition,
      a then_block and an else_block. Both of these blocks contain a list of
      statements.

    - While loops are similarlly reprsented by a boolean expression and a
      list of body statements.

    - Go_To statements contain the index of the statement we would like to jump to.

    - Finish statements indicate the end of a program. These aren't in the origininal
      paper, but make some of our computations easier. *)

Inductive Statement := 
| Assignment (x: string) (a: IntExp)
| Seq (s1 s2: Statement)
| If (b: BoolExp) (then_block: Statement) (else_then: Statement)
| While (b: BoolExp) (body: Statement)
| Go_To (idx: nat).

Inductive Program := 
  | P (stmt: Statement) (params: list string).

Definition stmts (prog: Program) :=
  match prog with
  | P stmt params => stmt
  end.

Open Scope string_scope.

Fixpoint paramsToEmptySt (params: list string) : state :=
  match params with
  | nil => nil
  | h :: t => (h, Symbol("s" ++ h)) :: (paramsToEmptySt t)
  end.

Definition emptySt (prog: Program) : state :=
  match prog with
  | P stmt params => paramsToEmptySt params
  end.

(** This function is used to compute the length of a program. The gas parameter is
    needed so that Coq can verify that our recursion is decreasing. *)

Fixpoint progLength (prog: Statement) : nat :=
  match prog with
  | Assignment _ _ => 1
  | Seq p1 p2 => (progLength p1) + (progLength p2)
  | If _ t e => 1 + (progLength t) + (progLength e)
  | While b body => 1 + (progLength body)
  | Go_To _ => 1
  end.
  
(** Since our Node data structure and the Go_To statement constructor reference an
    instruction by its index, we need a way to assign a unique index number to each
    statement in a program.
    
    The findStatement function takes in a program and an index. This index
    is the location of the statement in our program that we would like to execute
    next.
    
    If the index parameter is 0, we can just return what is at the head of our list.
    If the index is not 0, we must recursively traverse our program until we arrive
    at the desired location, and return that statement.

    The Assignment and Go_To statements have no nested structure, so this is
    straightforward.

    For conditonal statements, If and While, the calculation is a bit more involved. 
    The key to being able to make this work for a hierarchical program of nested
    lists of statements is traversing the program as if the lists were flattened. 
    So for example, if our program has an If statement at index 2 with two
    statements in the then block and two in the else block, the indices of the
    then block would be 3, 4, and those of the else block would be 5, 6.

    Under this model, we can calculate the offsets into our 'then' (th) and 'else' (e) 
    lists by simple operations over the lengths of the lists. For example, if the desired 
    index is greater than the length of the then block, we know the desired statement is 
    either in the else block or outside of the if/else statement entirely. *)
Open Scope nat.
Fixpoint findStatement (prog: Statement) (i: nat) : Statement :=
  match i with
  | O => match prog with 
    | Seq p1 p2 => findStatement p1 O
    | _ => prog
    end
  | S i' => match prog with
    | Assignment x ie => Assignment x ie
    | Seq p1 p2 =>
      if (i <? (progLength p1)) then (findStatement p1 i)
        else (findStatement p2 (i - (progLength p1)))
    | If b t e =>
      if (progLength t <=? i') then (findStatement t i')
        else (findStatement e (i' - (progLength t)))
    | While b body => findStatement body i'
    | Go_To n => Go_To n 
    end
  end.

(** This logic only matters when i points to an assignment. Otherwise
    we're able to compute the next instruction pointer directly. *)
Fixpoint nextInstruction (prog: Statement) (i: nat) : nat :=
  match prog with 
  | Assignment x ie => 1
  | Seq p1 p2 => if ((progLength p1) <=? i+1) then (nextInstruction p1 i)
                   else (progLength p1) + (nextInstruction p2 (i - (progLength p1)))
  | If b t e => if ((progLength t) =? (i-2)) then (progLength prog)
                  else i+1
  | While b body => if ((progLength body) =? (i-2)) then 0
                      else i+1
  | Go_To n => 1
  end.

Close Scope nat.
  
(** The following notation is inspired by the Imp chapter,
    with some minor modifications. *)
Coercion IntId : string >-> IntExp.
Coercion Symbol : string >-> SymbolicExp.
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
Notation "'~' b"  := (Bnot b)
  (in custom com at level 75, right associativity).

Declare Custom Entry sym.

Notation "<[ e ]>" := e (at level 0, e custom sym at level 99) : sym_scope.
Notation "( x )" := x (in custom sym, x at level 99) : sym_scope.
Notation "x" := x (in custom sym at level 0, x constr at level 0) : sym_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom sym at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : sym_scope.
Notation "x + y" := (SymAdd x y)
  (in custom sym at level 50, left associativity).
Notation "x - y" := (SymSub x y)
  (in custom sym at level 50, left associativity).
Notation "x * y" := (SymMult x y)
  (in custom sym at level 40, left associativity).
Notation "'true'"  := SBTrue (in custom sym at level 0).
Notation "'false'"  := SBFalse (in custom sym at level 0).
Notation "x >= 0" := (SBge0 x) (in custom sym at level 70, no associativity).
Notation "'~' b"  := (SBnot b)
  (in custom sym at level 75, right associativity).


Notation "x := y" :=
          (Assignment x  y)
            (in custom com at level 0, x constr at level 0,
              y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' b 'then' then_body 'else' else_body 'end'" :=
          (If b then_body else_body)
            (in custom com at level 89, b at level 99,
            then_body at level 99, else_body at level 99) : com_scope.
Notation "'while' b 'do' body 'end'" :=
          (While b body)
            (in custom com at level 89, b at level 99, body at level 99) : com_scope.
Notation "'go_to' x" := (Go_To x) (in custom com at level 89, x at level 99) : com_scope.


Open Scope com_scope.
Open Scope sym_scope.

(** Inspired by Imp's aeval. This will convert an IntExp into a SymbolicExp. *)
Fixpoint makeSymbolicInt (s : state) (ie : IntExp) : SymbolicExp :=
  match ie with
  | IntLit n => Constant n
  | <{n1 + n2}> =>  <[(makeSymbolicInt s n1) + (makeSymbolicInt s n2)]>
  | <{n1 - n2}> =>  <[(makeSymbolicInt s n1) - (makeSymbolicInt s n2)]>
  | <{n1 * n2}> =>  <[(makeSymbolicInt s n1) * (makeSymbolicInt s n2)]>
  | IntId n => applyState s n
  end.

Fixpoint makeSymbolicBool (s : state) (be : BoolExp) : SBoolExp :=
  match be with
  | BTrue => SBTrue
  | BFalse => SBFalse
  | Bnot b => <[~ (makeSymbolicBool s b)]>
  | Bge0 ie => <[(makeSymbolicInt s ie) >= 0]>
  end.