From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope list_scope.
From LF Require Import Maps.
From Coq Require Import Lists.List.
Import ListNotations.

(** TODO: 
    - comments
    - add some examples (perhaps from paper)
    - clean up/standardize notation
    - flesh out if example/update
    - simple while example
    - property 1
      * general proof -- induction on eval fn
      * or show for every path for every example
    - property 2
    - try commutativity    
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

Inductive SymbolicExp : Type :=
  | Symbol (s: string)
  | SymAdd (s1 s2: SymbolicExp)
  | SymSub (s1 s2: SymbolicExp)
  | SymMult (s1 s2: SymbolicExp)
  | Constant (n : Z).

(* Also inspired by the BExp from Imp.*)
Inductive BoolExp : Type :=
  | BTrue
  | BFalse
  | Bnot (b : BoolExp)
  | Bge0 (n : SymbolicExp).

(* We represent a program state as a map of integer expressions and symbolic values. *)
Definition state := total_map SymbolicExp.
Definition concreteState := total_map Z.

(* A path condition is built up of a series of boolean expressions. *)
Inductive PathCond : Type :=
| none
| Pand (be : BoolExp) (p : PathCond).
            
Fixpoint substitute (se: SymbolicExp) (mappings: concreteState): Z  :=
  match se with
  | Symbol s => mappings s
  | SymAdd s1 s2 => (substitute s1 mappings) + (substitute s2 mappings)
  | SymSub s1 s2 => (substitute s1 mappings) - (substitute s2 mappings)
  | SymMult s1 s2 => (substitute s1 mappings) * (substitute s2 mappings)
  | Constant n => n
  end.

Fixpoint inteval (ie: IntExp) (s: state) (mappings:  concreteState) : Z :=
  match ie with 
  | IntLit n => n
  | IntAdd n1 n2 => (inteval n1 s mappings) + (inteval n2 s mappings)
  | IntSub n1 n2 => (inteval n1 s mappings) - (inteval n2 s mappings)
  | IntMult n1 n2 => (inteval n1 s mappings) * (inteval n2 s mappings)
  | IntId x => substitute (s x) mappings
end.

Fixpoint beval (b : BoolExp) (mappings: concreteState) : bool :=
  match b with
  | BTrue   => true
  | BFalse => false
  | Bnot b => negb (beval b mappings)
  | Bge0 n => 0 <=? substitute n mappings
  end.

Fixpoint eval_pc (pc: PathCond) (mappings: concreteState ) : bool :=
  match pc with 
  | none => true
  | Pand be p => match be with
                | BTrue => eval_pc p mappings
                | BFalse => false
                | Bge0 n => (0 <=? substitute n mappings) && eval_pc p mappings
                | Bnot b => (negb (beval b mappings)) && eval_pc p mappings
                end
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
Definition empty_st := ( A !-> sA; B !-> sB; C !-> sC; _ !-> (Constant 0)).
Definition SAT_assign: concreteState := ( A !-> 0; B !-> 0; C !-> 0; _ !-> ( 0)).

(** SAT is a property of any given pc, saying that there exist concrete values
    which make it satisfiable. *)
Definition SAT (pc: PathCond) := exists (cs: concreteState), eval_pc pc cs = true.

(** For example, The trivial path condition 'true' is satisfiable by the
    map that takes each symbolic variable to 0. *)
Definition ex_pc := Pand BTrue none.
Definition SAT_assign_ex_1: concreteState := ( _ !-> 0).

(** When we evaluate ex_pc with this map, we get the boolean true. *)
Compute eval_pc ex_pc SAT_assign_ex_1.
Example ex_pc_sat : SAT ex_pc.
Proof.
  unfold SAT. exists (( _ !-> ( 0))). simpl. reflexivity.
Qed.

(** For another example, we prove that the path condition
    sA >= 0
    is satisfiable by the map that takes sA to 1 and all other symbolic
    variables to 0. *)
Definition ex_pc_2 := Pand BTrue (Pand (Bge0 sA) none).
Definition SAT_assign_ex_2: concreteState := ( A !-> 1; _ !-> ( 0)).
Compute eval_pc ex_pc SAT_assign_ex_2.
Example ex_pc_sat_2 : SAT ex_pc_2.
Proof.
  unfold SAT. exists (A !-> 1; ( _ !-> ( 0))). simpl. reflexivity.
Qed.


(** A TreeNode represents one node of our symbolic execution tree.
    It contains a program state, path condition, and an index
    into the program. The index points to a particular statement in the program.
*)
Inductive TreeNode : Type :=
  | Node (s : state) (pc : PathCond) (index : nat).

(** Getters to extract information from the TreeNode object. *)

Definition extractState (n : TreeNode) : state :=
  match n with 
  | Node s _ _ => s
  end.

Definition extractIndex (n : TreeNode) : nat :=
  match n with 
  | Node _ _ i => i
  end.

Definition extractPathCond (n : TreeNode) : PathCond :=
  match n with 
  | Node _ pc _ => pc
  end.

(** An ExecutionTree is either empty or a root node with a list of
    child trees. *)
Inductive ExecutionTree : Type :=
  | empty
  | Tr (n : TreeNode) (children : list ExecutionTree).

(** Now we define a basic instruction in the Integer language. This differs from
    the Imp implementation in Imp.v, because we don't have a
    statement of the form [stmt1 ; stmt2]. Instead, we maintain
    an ordering of statements in a list, called a Program. 

    In addition to basic assignment, we provide support for the same control 
    flow structures as in the original paper -- if/else, while loops,
    and function calls modeled by go_tos.

    - Assignment statements require a variable name (string) and an integer expression.
    The value of this variable is updated in the program state.

    - If statements are represented by a boolean expression for the condition,
    a then_block and an else_block. Both of these blocks contain a list of
    statements.

    - While loops are similarlly reprsented by a boolean expression and a
    list of body statements.

    - Go_To statements contain the index of the statement we would like to jump to.

    - Finish statements indicate the end of a program. These aren't in the origininal
    paper, but make some of our computations easier.
*)
Inductive Statement := 
  | Assignment (x: string) (a: IntExp) 
  | If (b: BoolExp) (then_block: list Statement) (else_then: list Statement)
  | While (b: BoolExp) (body: list Statement)
  | Go_To (idx: nat)
  | Finish.

(** As mentioned above, each program is represented as a list of statements. *)
Definition Program := list Statement.

(** Since our Node data structure and the Go_To statement constructor reference an
    instruction by its index, we need a way to assign a unique index number to each
    statement in a program.
    
    The findStatement function takes in a program and an index. This index
    is the location of the statement in our program that we would like to execute next.
    
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
    then block would be 3, 4 and the else block would be 5, 6.

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
      (* For If statements, we need to recursively flatten the structure
      within the 'then' and 'else' blocks. *)
      | If b th e => match leb (length th) i' with
         | true => match leb ((length th) + (length e)) i' with
           | true => findStatement t (i' - (length th) - (length e))
           | false => findStatement e (i' - (length th))
           end 
         | false => findStatement th i'
        end
      (* Similarly, for While statements, we must recursively flatten the
      structure within the loop body. *)
      | While b body => match leb (length body) i' with
         | true => findStatement t (i' - (length body))
         | false => findStatement body i'
        end
      | Go_To j => findStatement t i'
      (* If we reach this constructor, then we're looking for an instructon
      past the end of the program. This case isn't valid. *)
      | Finish => Finish
    end
  end
end.


(** The following notation is inspired by the Imp chapter,
    with some minor modifications.*)
Coercion IntId : string >-> IntExp.
(*Coercion IntLit : Z >-> IntExp.*)
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
Notation "x s+ y" := (SymAdd x y)
  (in custom com at level 50, left associativity).
Notation "x s- y" := (SymSub x y)
  (in custom com at level 50, left associativity).
Notation "x s* y" := (SymMult x y)
  (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x >= 0" := (Bge0 x) (in custom com at level 70, no associativity).
(*Notation "x && y" := (Band x y)
  (in custom com at level 80, left associativity).
Notation "x || y" := (Bor x y)
  (in custom com at level 80, left associativity). *)
Notation "'~' b"  := (Bnot b)
  (in custom com at level 75, right associativity).
Notation "x := y" :=
         (Assignment x  y)
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

(* Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100). *)
Open Scope com_scope. 

(* Inspired by Imp's aeval. This will convert an IntExp into a SymbolicExp. *)
Fixpoint makeSymbolic (s : state) (ie : IntExp) : SymbolicExp :=
  match ie with
  | IntLit n => Constant n
  | <{n1 + n2}> =>  SymAdd (makeSymbolic s n1) (makeSymbolic s n2)
  | <{n1 - n2}> => SymSub (makeSymbolic s n1) (makeSymbolic s n2)
  | <{n1 * n2}> =>  SymMult (makeSymbolic s n1) (makeSymbolic s n2)
  | IntId n => s n
  end.

(** The following relation is our representation of symbolic execution of a program.
    It relates a given program, and a node corresponding to a particular statement,
    to a resultant execution tree. As defined here, the relation will generate 
    nodes for unsatisfiable path conditions (i.e. false path conditions) but
    will not progress execution past these nodes. *)

Inductive node_eval : Program -> TreeNode -> ExecutionTree -> Prop :=
(** Given some node pointing to an assignment statement, with a given state and
    path condition, the resultant ExecutionTree is a single node with an updated
    state to reflect the assingment operation. The index is incremented by one in
    the child node, since there is no branching happening at this step. *)
  | E_Assign : forall prog node x ie se st n pc tree',
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = <{x := ie}> ->
    (makeSymbolic st ie) = se ->
    node_eval prog (Node (x !-> se ; st) pc (n+1)) tree' ->
    node_eval prog node (Tr node [tree'])

(** Given some node pointing to an if statement, with a given state and path
    condition, the resultant ExecutionTree depends on whether the boolean check is
    satisfiable or not.

    If so, it branches into two nodes: one where the condition is true and one where
    the condition is false. In these cases, we respectively add the condition and its
    negation to the path condition in the child nodes, and then update the index to
    point to the next executable instruction. *)
  | E_IfSAT : forall prog node be then_body else_body st n pc tree1' tree2',
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (SAT pc) -> 
    node_eval prog (Node st (Pand be pc) (n+1)) tree1' ->
    node_eval prog (Node st (Pand (Bnot be) pc) (n + (length then_body))) tree2' ->
    node_eval prog node (Tr node [tree1' ; tree2'])

(** If the boolean in the path condition is unsatisfiable, then we will only
    extend the execution tree along the 'else' branch. *)
  | E_IfUnSAT : forall prog node be then_body else_body st n pc tree,
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (SAT (Pand (Bnot be) pc)) ->
    node_eval prog (Node st (Pand (Bnot be) pc) (n + (length then_body))) tree ->
    node_eval prog node (Tr node [tree])

(** Go_To statements have no branching structure involved. There is just one child
    node, which has an index pointing to the statement specified by the Go_To. *)
  | E_GoTo: forall prog node i st n pc tree',
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = <{go_to i}> ->
    node_eval prog (Node st pc i) tree' ->
    node_eval prog node (Tr node [tree'])

(** While statements are similar to If statements, in that we have to consider
    whether the boolean expression is satisfiable or not. If so, we make two
    branches: one going into the loop body, and another skipping the loop. The
    next executable instruction is pointed to by separate indices in each case. We
    add the boolean condition to the branch that executes the loop body, and its
    negation to the branch that skips the loop. *)
  | E_WhileSAT: forall prog node be body st n pc tree1' tree2',
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (SAT pc) ->
    node_eval prog (Node st (Pand be pc) (n + 1)) tree1' ->
    node_eval prog (Node st (Pand (Bnot be) pc) (n + (length body))) tree1' ->
    node_eval prog node (Tr node [tree1' ; tree2'])

(** If the path condition is unsatisfiable, we unconditionally skip the loop body,
    and just have one child node representing this case. This child node has an
    updated index and path condition. *)
  | E_WhileUnSAT: forall prog node be body st n pc tree,
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (SAT (Pand (Bnot be) pc)) ->
    node_eval prog (Node st (Pand (Bnot be) pc) (n + (length body))) tree ->
    node_eval prog node (Tr node [tree])

(** When the Finish statement is evaluated, it generates no child nodes. *)
  | E_Finish: forall prog node st n pc,
    extractState node = st ->
    extractIndex node = n ->
    extractPathCond node = pc ->
    (findStatement prog n) = Finish ->
    node_eval prog node (Tr node []).

Inductive tree_eval : ExecutionTree -> list ExecutionTree -> Prop :=
  | E_empty: tree_eval empty []
  | E_Tr: forall (tree: ExecutionTree) children root,
    tree_eval (Tr root children) children.

(** The following is our execution of the program shown in Figure 1 of King's
    paper. We supply the symbolic execution tree corresponding to this program
    (which is just a simple list of nodes, with no branching), and prove that
    this is indeed the correct tree. *)

Definition prog_1 := [<{X := A + B}>; 
                      <{Y := B + C}>; 
                      <{Z := X + Y - B}>;
                      Finish].

Example prog_1_eval :
  node_eval prog_1 (Node empty_st none 0)
    (Tr (Node empty_st none 0) [(
      Tr (Node (X !-> <{sA s+ sB}> ; empty_st) none 1) [(
        Tr (Node (Y !-> <{sB s+ sC}> ; X !-> <{sA s+ sB}> ; empty_st) none 2) [(
          Tr (Node (Z !-> <{(sA s+ sB) s+ (sB s+ sC) s- sB}> ; Y !-> <{sB s+ sC}> ;
                    X !-> <{sA s+ sB}> ; empty_st) none 3) nil
    )])])]).
Proof.
  apply E_Assign with (x := X) (ie := <{A + B}>) (se := <{A s+ B}>)
                      (st := empty_st) (n := O) (pc := none); try reflexivity.
  apply E_Assign with (x := Y) (ie := <{B + C}>) (se := <{B s+ C}>)
                      (st := X !-> <{ A s+ B }>; empty_st)
                      (n := S O) (pc := none); try reflexivity.
  apply E_Assign with (x := Z ) (ie := <{X + Y - B}>)
                      (se := <{(sA s+ sB) s+ (sB s+ sC) s- sB}>)
                      (st := Y !-> <{sB s+ sC}> ; X !-> <{sA s+ sB}> ; empty_st)
                      (n := S (S O)) (pc := none); try reflexivity.
  apply E_Finish with (st := Z !-> <{(sA s+ sB) s+ (sB s+ sC) s- sB}> ;
                             Y !-> <{sB s+ sC}> ; X !-> <{sA s+ sB}> ; empty_st)
                      (n := S (S (S O))) (pc := none); try reflexivity.
Qed.

(* hypothesis: prog , node, tree in node_eval relation...; 
  for all of those things & more, if extract pc from node == pc and this pc is from a node in this relation*)

  
Definition tree_1 := 
  (Tr (Node empty_st none 0) [(
    Tr (Node (X !-> <{sA s+ sB}> ; empty_st) none 1) [(
      Tr (Node (Y !-> <{sB s+ sC}> ; X !-> <{sA s+ sB}> ; empty_st) none 2) [(
        Tr (Node (Z !-> <{(sA s+ sB) s+ (sB s+ sC) s- sB}> ; Y !-> <{sB s+ sC}> ;
                  X !-> <{sA s+ sB}> ; empty_st) none 3) nil
  )])])]).

Definition extractNode (tr : ExecutionTree) : TreeNode :=
  match tr with 
  | empty => (Node empty_st none 0)
  | Tr n _  => n
  end.

(* probs Dont want to do this manually*)
Definition node_1 := extractNode tree_1.
Definition node_2 := (Node (Y !-> <{sB s+ sC}> ; X !-> <{sA s+ sB}> ; empty_st) none 2).
Definition node_3 := (Node (Z !-> <{(sA s+ sB) s+ (sB s+ sC) s- sB}> ;
                            Y !-> <{sB s+ sC}> ;
                            X !-> <{sA s+ sB}> ; empty_st) none 3).

Definition Path := list TreeNode.

Definition path_1 := [node_1; node_2; node_3].

Theorem prog_1_path_1_prop_1 : forall (n: TreeNode),
In n path_1 -> SAT (extractPathCond n).
Proof.
unfold path_1. simpl. intros. destruct H as [H1 | [H2 | [H3 | H4]]].
  - rewrite <- H1. simpl. unfold SAT. simpl. exists SAT_assign_ex_1. reflexivity.
  - rewrite <- H2. simpl. unfold SAT. simpl. exists SAT_assign_ex_1. reflexivity.
  - rewrite <- H3. simpl. unfold SAT. simpl. exists SAT_assign_ex_1. reflexivity.
  - destruct H4.
Qed.

Definition not_finish (s: Statement) : bool  :=
 match s with 
  | Finish => false  
  | _ => true
end.

Axiom superset_SAT : forall (p: PathCond) (be : BoolExp),
 SAT (Pand be p) -> SAT p.

Axiom Finish_unSAT : forall (p: Program)(i: nat),
 (findStatement p i) = Finish ->
  False.

Theorem property_1 : forall (prog: Program) (node: TreeNode) (tr : ExecutionTree),
 node_eval prog node tr ->
 SAT (extractPathCond node).
Proof. 
intros. induction H. 
  (* E_Assign *)
  - simpl in IHnode_eval. rewrite H1. apply IHnode_eval. 
  (* E_IFSat *)
  - simpl in IHnode_eval1. inversion H1. rewrite H1. apply H3. 
  (* E_IFUnSAT *)
   - simpl in IHnode_eval. rewrite H1. apply superset_SAT in IHnode_eval. apply IHnode_eval.  
  (* E_GoTo *)
  - simpl in IHnode_eval. rewrite H1. apply IHnode_eval.
  (* E_WhileSAT *)
  - simpl in IHnode_eval1. inversion H1. rewrite H1. apply H3. 
  (* E_WhileUnSAT *)
  - simpl in IHnode_eval. rewrite H1. apply superset_SAT in IHnode_eval. apply IHnode_eval. 
  (* E_Finish *)
   - apply Finish_unSAT in H2. destruct H2. 
Qed.
  
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

