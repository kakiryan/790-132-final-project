From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope list_scope.
From LF Require Import Maps.
From Coq Require Import Lists.List.
Import ListNotations.

(** TODO: 
    - Finish a program eval function 
    - comments
    - add some examples (perhaps from paper)
    - proofs!!!!!!!
*)


Declare Custom Entry com.
Declare Scope com_scope.

(** Inspired by the AExp from the Imp chapter. The only difference is that 
we are using the built-in integer type, Z. The Integer language as defined in
the King paper only provides support for addition, subtraction and multiplcation, too.
*)
Inductive IntExp : Type :=
| IntLit (n : Z)
| IntAdd (n1 n2: IntExp)
| IntSub (n1 n2: IntExp)
| IntMult (n1 n2: IntExp)
| IntId (x : string).

(* Also inspired by the BExp from Imp.*)
Inductive BoolExp : Type :=
  | BTrue
  | BFalse
  | Band (b1 : BoolExp) (b2 : BoolExp)
  | Bor (b1 : BoolExp) (b2 : BoolExp)
  | Bnot (b : BoolExp)
  | Bge0 (n : IntExp).

(* We represent a program state as a map of integer expressions and symbolic values. *)
Definition state := total_map IntExp.

(* A path condition is built up of a series of boolean expressions. *)
Inductive Pathcond : Type :=
| none
| Pand (be : BoolExp) (p : Pathcond).


(** A TreeNode represents one node of our symbolic execution tree.
    It contains a program state, path condition, and an index
    into the program. The index points to a particular statement.
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
    an ordering of statements in a list, called a Program. 

    In addition to basic assignment, we provide support for the same control 
    flow structures as in the original paper -- if/else, while loops, and function calls modeled by
    go_tos.

    -`Assignment` statements require a variable name (string) and an integer expression.
    The value of this variable is updated in the program state.

    -`If` statements are presented by a boolean expression for the condition
    and a then_block and an else_block. Both of these blocks are represented as lists of statements.

    -`While` loops are similarlly reprsented by a boolean expression and a list of body statements.

    -`Go_To` statements contain the index of the statement we would like to jump to.
*)
Inductive Statement := 
  | Assignment (x: string) (a: IntExp) 
  | If (b: BoolExp) (then_block: list Statement) (else_then: list Statement)
  | While (b: BoolExp) (body: list Statement)
  | Go_To (idx: nat)
  | Finish.


(** As mentioned above, each program is represented as a list of statements. **)
Definition Program := list Statement.

(** From any point in our program, we need to know where to go next, or what 
    statement is the next to be executed. This is useful in the node_eval relation 
    below. 
    
    This function takes in a program, or list of statements, and an index. This index
    is the location of the statement in our program that we would like to execute next.
    
    If the index parameter is 0, we can just return what is at the head of our list. We 
    just want to execute the current statement. If the index is not 0, we must recursively
    traverse our program until we arrive at the desired location, and return that statement.

    For Assignment statements and Go_Tos, this is straightforward.

    For conditonal statements, If and While, the calculation is a bit more involved. 
    The key to being able to make this work for a hierarchical program of nested lists of statements
    is traversing the program as if the lists were flattened. 
    So for example, if our program has an If statement at index 2 with two statements in the then block 
    and two in the else block, the indices of the then block would be 3, 4 and the else block would be 5, 6.

    Under this model, we can calculate the offsets into our `then` (th) and `else` (e) lists by simple operations
    over the lengths of the lists. For example, if the desired index is greater than the length of the then block,
    we know the desired statement is either in the else block or outside of the if/else statement entirely.
*)
Fixpoint findStatement (prog : Program) (i : nat) : Statement :=
  match i with 
  | O => match prog with 
    | nil => Go_To 0
    | h :: t => h
  end
  | S i' => match prog with 
    | nil => Go_To 0
    | h :: t => match h with
      | Assignment x a => findStatement t i'
      | If b th e => match leb (length th) i' with
         | true => match leb ((length th) + (length e)) i' with
           | true => findStatement t (i' - (length th) - (length e))
           | false => findStatement e (i' - (length th))
           end 
         | false => findStatement th i'
        end
      | While b body => match leb (length body) i' with
         | true => findStatement t (i' - (length body))
         | false => findStatement body i'
        end
      | Go_To j => findStatement t i'
      | Finish => Finish (* bogus *)
    end
  end
end.


(* The following notation is inspired by Imp with some minor modifications.*)
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
Notation "'if' b 'then' then_body 'else' else_body 'end'" :=
         (If b then_body else_body)
           (in custom com at level 89, b at level 99,
            then_body at level 99, else_body at level 99) : com_scope.
Notation "'while' b 'do' body 'end'" :=
         (While b body)
            (in custom com at level 89, b at level 99, body at level 99) : com_scope.
Notation "'go_to' x" := (Go_To x) (in custom com at level 89, x at level 99) : com_scope.
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Definition empty_st := (_ !-> (IntLit 0)).

(* Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100). *)
Open Scope com_scope. 

(* Inspired by Imp's aeval. *)
Fixpoint inteval (s : state) (ie : IntExp) : IntExp :=
  match ie with
  | IntLit n => IntLit n
  | <{n1 + n2}> =>  <{(inteval s n1) + (inteval s n2)}>
  | <{n1 - n2}> => <{(inteval s n1) - (inteval s n2)}>
  | <{n1 * n2}> =>  <{(inteval s n1) * (inteval s n2)}>
  | IntId n => s n
  end.

(** The following relates our representation of a program, individual nodes and full execution trees.
    We will explain case by case what is happening below:

    E_Assign: Given some assignment statement and tree node with some state, pc and index, 
    The resultant ExecutionTree is a single node with an updated state to reflect the assingment operation.
    The index is incremented by one since there is no branching happening at this step.

    E_If: Given some if statement and tree node with some state, pc and index, the resultant ExecutionTree is 
    a made up of two nodes, one for the case the boolean condition is true and the other for false. 
    In the true case, we add that condition to the path condition and the index increase by one to enter the then block's
    list of statements. 
    In the false case, we add the negation of the boolean condition and the index is the current index + the length of
    the then block's list of statements. We are able to compute the indices this way because of how we have implemented
    findStatment above.

    E_GoTo: Given some index, the resultant tree is a single node whose index is specified by the argument given to the 
    Go_To constructor.

    E_While: Similar to the If statement, the resultant ExecutionTree has two nodes. One for the case that the boolean
    condition is true and one for if it is false.
*)
Inductive node_eval : Program -> TreeNode -> ExecutionTree -> Prop :=
  | E_Assign : forall prog node x ie1 ie2 st n pc tree',
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{x := ie1}> ->
    inteval st ie1 = ie2 ->
    node_eval prog (Node (x !-> ie2 ; st) pc (n+1)) tree' ->
    node_eval prog node (Tr node [tree'])
  | E_If : forall prog node be then_body else_body st n pc tree1' tree2',
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    node_eval prog (Node st (Pand be pc) (n+1)) tree1' ->
    node_eval prog (Node st (Pand (Bnot be) pc) (n + (length then_body))) tree2' ->
    node_eval prog node (Tr node [tree1' ; tree2'])
  | E_GoTo: forall prog node i st n pc tree',
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{go_to i}> ->
    node_eval prog (Node st pc i) tree' ->
    node_eval prog node (Tr node [tree'])
  | E_While: forall prog node be body st n pc tree1' tree2',
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = <{while be do body end}> ->
    node_eval prog (Node st (Pand be pc) (n + 1)) tree1' ->
    node_eval prog (Node st (Pand (Bnot be) pc) (n + (length body))) tree1' ->
    node_eval prog node (Tr node [tree1' ; tree2'])
  | E_Finish: forall prog node st n pc,
    extractState node = st ->
    extractIndex node = n ->
    extractPathcond node = pc ->
    (findStatement prog n) = Finish ->
    node_eval prog node (Tr node [empty]).

(* TODO : Add tree evaluation relation *)

(** See figure 1 of King paper. This is the sum procedure. Question -- do we want a return statement?*)
Definition A: string := "A".
Definition B: string := "B".
Definition C: string := "C".
Definition X: string := "X".
Definition Y: string := "Y".
Definition Z: string := "Z".
Definition prog_1 := [<{X := A + B}>; 
                      <{Y := B + C}>; 
                      <{Z := X + Y - B}>;
                      Finish].

Example prog_1_eval :
  node_eval prog_1 (Node empty_st none 0)
    (Tr (Node empty_st none 0) [(
      Tr (Node (X !-> <{A + B}> ; empty_st) none 1) [(
        Tr (Node (Y !-> <{B + C}> ; X !-> <{A + B}> ; empty_st) none 2) [(
          Tr (Node (Z !-> <{X + Y - B}> ; Y !-> <{B + C}> ;
                    X !-> <{A + B}> ; empty_st) none 3) nil
    )])])]).
Proof.
  apply E_Assign with (x := X) (ie1 := <{A + B}>) (ie2 := <{A + B}>)
                      (st := empty_st) (n := O) (pc := none); try reflexivity.
  - simpl.
  

Definition stmt1 := findStatement prog_1 0.
Compute stmt1.
Definition stmt2 := findStatement prog_1 1.
Compute stmt2.

Definition starting_node := Node empty_st none 1. 
Check node_eval prog_1 starting_node.

(** Not in paper, but just trying some simple if/else. *)
Definition prog_2 := [<{X := 2}>; 
                      <{if X >= 0
                        then [<{X := 3}>;
                              <{Y := 4}>]
                        else [<{X := 4}>;
                              <{Y := 5}>]
                        end}>].

Definition stmt2_1 := findStatement prog_2 0.
Compute stmt2_1.
Definition stmt2_then := findStatement prog_2 2.
Compute stmt2_then.
Definition stmt2_else := findStatement prog_2 5.
Compute stmt2_else.

