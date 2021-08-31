From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope list_scope.
(** From LF Require Import Maps. *)
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Structures.OrderedTypeEx.
From SE Require Export Helpers.
Import ListNotations.

Open Scope string_scope.

(** Link to our repo: 
https://github.com/kakiryan/790-132-final-project *)

(** Table of Contents:
  - Definition Symbolic Execution Concepts (Minimum goal)
  - General Proof of Property 1 (Standard Goal)
  - Proof of Property 2 for:  (Standard Goal)
      * Figure 1 in King Paper
      * Modified Figure 2 in King Paper
      * While loop example
  - Proof of Property 2 for: (Reach Goal)
      * Figure 1 in King Paper
      * Modified Figure 2 in King Paper
      * While loop example

    Property 1: Path condition is never identically false. 
    Property 2: All leaf nodes in a symbolic execution tree are distinct. 
    Property 3: Symbolic execution is commutative. *)

(* Declare Custom Entry com. *)

Lemma treeDiffAddNode : forall tr (i: nat) node,
  ~(Nat.lt i 0) -> (Nat.lt i (treeSize tr)) ->
  treeDiff tr (addNode tr i node) = [node].
Proof.
  intros. induction tr.
  - destruct i. inversion H0. inversion H0.
  - 
(** The following relation is our representation of symbolic execution of a program.
    It relates a given program, and a node corresponding to a particular statement,
    to a resultant execution tree. As defined here, the relation will generate 
    nodes for unsatisfiable path conditions (i.e. false path conditions) but
    will not progress execution past these nodes. *)

Inductive node_eval: Program -> ExecutionTree -> nat -> TreeNode -> ExecutionTree -> Prop :=
 | E_Empty: forall prog st,
   (isEmpty st) = true -> 
   node_eval prog empty 0 <<st, nil, 0>> (Tr <<st, nil, 0>> empty empty)
  
  | E_Assign : forall prog i node x ie se st n pc node' tree,
    ~(tree = empty) ->
    (isLeaf tree i) = true ->
    node = findNode tree i ->
    node_unpack node st n pc ->
    (findStatement prog n) = <{x := ie}> ->
    (makeSymbolicInt st ie) = se ->
    node' = <<(x, se) :: st, pc, n+1>> ->
    node_eval prog tree i node (addNode tree i node')

  | E_IfBoth : forall prog i node be sbe then_body else_body st n pc tree node1' node2',
    ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
     node_unpack node st n pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (sbe::pc)) ->
    (SAT (<[~sbe]>::pc)) ->
    node1' = << st, sbe::pc,  (n+1)>> ->
    node2' = << st, (<[~sbe]>)::pc, (n + (progLength then_body 1000%nat))>> ->
    node_eval prog tree i node (addNode (addNode tree i node1') i node2')

   | E_IfThen : forall prog i node be sbe then_body else_body st n pc tree node',
   ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
     node_unpack node st n pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (sbe::pc)) ->
    node' = << st, sbe::pc,  (n+1)>> ->
    node_eval prog tree i node (addNode tree i node')

  | E_IfElse : forall prog i node be sbe then_body else_body st n pc tree node',
  ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
     node_unpack node st n pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (<[~sbe]>::pc)) ->
    node' = << st, (<[~sbe]>)::pc, (n + (progLength then_body 1000%nat))>> ->
    node_eval prog tree i node (addNode tree i node')

   | E_GoTo: forall prog i node pos st n pc tree node',
   ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
    node_unpack node st n pc ->
    (findStatement prog n) = <{go_to pos}> ->
    node' = << st, pc, pos>> ->
    node_eval prog tree i node (addNode tree i node')

  | E_WhileBoth: forall prog i node be sbe body st n pc tree node1' node2',
  ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
    node_unpack node st n pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (sbe:: pc)) ->
    (SAT (<[~sbe]>:: pc)) ->
    node1' = << st,  sbe::pc, (n + 1) >> ->
    node2' = << st,  (<[~sbe]>:: pc), (n + (progLength body 1000%nat)+ 1)>> -> 
    node_eval prog tree i node (addNode (addNode tree i node1') i node2')

  | E_WhileBody: forall prog i node be sbe body st n pc tree node',
  ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
    node_unpack node st n pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (sbe:: pc)) ->
    node' = << st,  sbe::pc, (n + 1) >> ->
    node_eval prog tree i node (addNode tree i node')

 | E_WhileSkip: forall prog i node be sbe body st n pc tree node',
 ~(tree = empty) ->
     (isLeaf tree i) = true ->
     node = findNode tree i ->
    node_unpack node st n pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (<[~sbe]>:: pc)) ->
    node' = << st,  (<[~sbe]>:: pc), (n + (progLength body 1000%nat)+ 1)>> ->
    node_eval prog tree i node (addNode tree i node').


(** This should be provable, but we'll skip it in the interest of time. It is stating
    that if a superset of a condition is satisfiable, then the condition itself is 
    satisfiable. *)
Theorem superset_SAT : forall (p: PathCond) (sbe : SBoolExp),
  SAT (sbe::p) -> SAT p.
Proof. intros. destruct H. unfold SAT. exists x. simpl in H. destruct (eval_pc p x). 
 - reflexivity.
 - simpl in H. rewrite andb_comm in H. simpl in H. apply H.
Qed.

Inductive SAT_tree: ExecutionTree -> Prop :=
 | SAT_empty: SAT_tree empty

 | SAT_tr: forall node tr1 tr2,
   SAT (extractPathCond node) ->
   SAT_tree tr1 -> SAT_tree tr2 ->
   SAT_tree (Tr node tr1 tr2).

(* ================== End: Definition Symbolic Execution Concepts. ==================*)

(* ========================= Start: Proof of Property 1. ============================*)

(** A general proof of property 1 from the King paper, that the 
    path condition never becomes identically false. 

    hypothesis: (prog, node, tree) is in node_eval relation; 
    for all of those things & more, if extract pc from node == pc and this pc is from
    a node in this relation *)
Theorem property_1 : forall prog tr i node tr',
  SAT_tree tr ->
  node_eval prog tr i node tr' ->
  SAT_tree tr'.
Proof.
  intros. induction H.
  - inversion H0; try (destruct H; reflexivity).
    + apply (SAT_tr <<st, [], 0>> empty empty); try apply SAT_empty.
      exists nil. reflexivity.
  - inversion H0.
    + subst i0. destruct i.
      -- simpl. admit.
      -- simpl.
  (* E_Empty *)
  - simpl. destruct i. unfold SAT. exists nil. reflexivity. simpl. exists nil. reflexivity.
  (* E_Assign *)
  - 
  (* E_IFBoth *)
  - 
  (* E_IFThen *)
  - simpl in IHnode_eval. unfold node_unpack in H. destruct H as [H4 [H5  H6]]. rewrite H6. apply superset_SAT in IHnode_eval.
  apply IHnode_eval.  
  (* E_IFElse *)
  - simpl in IHnode_eval. unfold node_unpack in H. destruct H as [H4 [H5  H6]]. rewrite H6. apply superset_SAT in IHnode_eval.
    apply IHnode_eval.  
  (* E_GoTo *)
  - simpl in IHnode_eval. unfold node_unpack in H. destruct H as [H2 [H3  H4]]. rewrite H4. apply IHnode_eval.
  (* E_WhileBoth *)
  - simpl in IHnode_eval1. unfold node_unpack in H. destruct H as [H6 [H7  H8]]. rewrite H8. 
  apply superset_SAT in IHnode_eval1. apply IHnode_eval1.  
  (* E_WhileBody *)
  - simpl in IHnode_eval. unfold node_unpack in H. destruct H as [H4 [H5  H6]]. rewrite H6. 
  apply superset_SAT in IHnode_eval. apply IHnode_eval.
  (* E_WhileSkip *)
  - simpl in IHnode_eval.  destruct H as [H4 [H5  H6]]. rewrite H6. 
  apply superset_SAT in IHnode_eval. apply IHnode_eval.
  (* E_Finish *)
  - unfold node_unpack in H.  destruct H as [H2 [H3  H4]]. rewrite H4. apply H0.
Qed.

(* ========================= End: Proof of Property 1. ================================*)

(* ====================== Start: Proof of Property 2 for Program 1. ===================*)

(** The following is our execution of the program shown in Figure 1 of King's
    paper. We supply the symbolic execution tree corresponding to this program
    (which is just a simple list of nodes, with no branching), and prove that
    this is indeed the correct tree. *)

Definition prog_1 := [<{X := A + B}>; 
                      <{Y := B + C}>; 
                      <{Z := X + Y - B}>;
                      Finish].

Example prog_1_eval :
  node_eval prog_1 <<empty_st, nil, 0>>
    (Tr  << empty_st, nil, 0>> [(
      Tr <<(X !-> <[sA + sB]> ; empty_st), nil, 1>> [(
        Tr <<(Y !-> <[sB + sC]> ; X !-> <[sA + sB]> ; empty_st), nil, 2>> [(
          Tr <<(Z !-> <[(sA + sB) + (sB + sC) - sB]> ; Y !-> <[sB + sC]> ;
                    X !-> <[sA + sB]> ; empty_st), nil, 3>> nil
    )])])]).
Proof.
  (* X := A + B *)
  apply E_Assign with (x := X) (ie := <{A + B}>) (se := <[A + B]>)
                      (st := empty_st) (n := O) (pc := nil); try reflexivity.
    unfold SAT. exists SAT_assign_ex_1. simpl. reflexivity. 
  (* Y := B + C *)
  apply E_Assign with (x := Y) (ie := <{B + C}>) (se := <[B + C]>)
                      (st := X !-> <[A + B]>; empty_st)
                      (n := S O) (pc := nil); try reflexivity.
    unfold SAT. exists SAT_assign_ex_1. simpl. reflexivity.
 (* Z := X + Y  - B *)  
  apply E_Assign with (x := Z ) (ie := <{X + Y - B}>)
                      (se := <[(sA + sB) + (sB + sC) - sB]>)
                      (st := Y !-> <[sB + sC]> ; X !-> <[sA + sB]> ; empty_st)
                      (n := S (S O)) (pc := nil); try reflexivity.
    unfold SAT. exists SAT_assign_ex_1. simpl. reflexivity.
  apply E_Finish with (st := Z !-> <[(sA + sB) + (sB + sC) - sB]> ;
                             Y !-> <[sB + sC]> ; X !-> <[sA + sB]> ; empty_st)
                      (n := S (S (S O))) (pc := nil); try reflexivity.
    unfold SAT. exists SAT_assign_ex_1. simpl. reflexivity.
Qed.

(** Now that we have proven that this is the correct symbolic execution tree for the 
    program, we will refer to it as tree_1. *)
Definition tree_1 := 
    (Tr  << empty_st, nil, 0>> [(
      Tr <<(X !-> <[sA + sB]> ; empty_st), nil, 1>> [(
        Tr <<(Y !-> <[sB + sC]> ; X !-> <[sA + sB]> ; empty_st), nil, 2>> [(
          Tr <<(Z !-> <[(sA + sB) + (sB + sC) - sB]> ; Y !-> <[sB + sC]> ;
                    X !-> <[sA + sB]> ; empty_st), nil, 3>> nil
    )])])]).

(** Property 2 from the paper is that every leaf node is distinct, or in other words,
    no two leaves have the same path condition. We represent the leaves as a list of
    the different path conditions for each example and prove that there are no
    duplicates for each. *)
Definition leaves := list PathCond.
Definition prog_1_leaves: list PathCond := [nil].

Definition get_head_pc (p : leaves) : PathCond :=
 match p with
  | [] => nil
  | h :: t => h
 end.

(** The proof of this property for the first example is trivial, as there is no 
    branching or control flow.*)

Theorem property_2_ex_1 : forall (pc: PathCond),
  (get_head_pc prog_1_leaves) = pc -> ~ (In pc (tl prog_1_leaves)).
Proof.
  intros. unfold not. unfold prog_1_leaves. simpl. intros. destruct H0.
Qed.

(* ==================== End: Proof of Property 2 for Program 1. ===================== *)

(* ==================== Start: Proof of Property 2 for Program 2. =================== *)

(* Setting up new variable names for example 2. *)
Definition J: string := "J".
Definition sJ := Constant 1.
Definition sY := Symbol Y.
Definition sZ2 := Constant 1.
Definition sX := Symbol X.


(** The following program is slightly modified from the program in figure 2 of the King
    paper. Instead of Y >= J, we have Y >=0 since the paper claims that their only
    boolean operation is >= 0. *)
Definition prog_2 := [<{Z := IntLit 1}>; 
                      <{J := IntLit 1}>;
                      <{if Y >= 0
                        then [<{Z := Z * X }>;
                              <{Y := Y - J}>;
                                Go_To 2;
                                Finish]
                        else [Finish]
                        end}>;
                        Finish].

(* A satisfying assignment for taking the true branch *)
Definition SAT_assign_prog_2_true_branch: concreteState := (X !-> 1; Y !-> 0 ; _ !-> 0).

(* A satisfying assignment for taking the true branch *)
Definition SAT_assign_prog_2_false_branch: concreteState :=
  (X !-> 1 ; Y !-> -2; _ !-> 0).

(* Starting symbolic state for this example.*)
Definition empty_st_2 := (A !-> sA; B !-> sB; C !-> sC; J !-> sJ; Z !-> sZ2; Y !-> sY; 
  X !-> sX; _ !-> (Constant 0)). 


(** This is the tree for the case that the loop (made up of an if/then + go_to) only
    executes once. We prove that is a correct tree for the above prog_2. *)
Example prog_2_eval :
  node_eval prog_2  <<empty_st_2, nil, 0>>
    (Tr <<empty_st_2, nil, 0>> [
      Tr <<(Z !-> (Constant 1) ; empty_st_2), nil, 1>> [
        Tr <<(J !-> (Constant 1) ; Z !-> (Constant 1) ; empty_st_2), nil, 2>> [
          Tr <<(J !-> (Constant 1) ; Z !-> (Constant 1) ; empty_st_2),
              [SBge0 sY], 3>> [
            Tr <<(Z !-> <[sZ2 * sX]>; J !-> (Constant 1) ; Z !-> (Constant 1) ;
                empty_st_2), [SBge0 sY], 4>> [
              Tr <<(Y !-> <[sY - sJ]>; Z !-> <[sZ2 * sX]>; J !-> (Constant 1) ;
                  Z !-> (Constant 1) ; empty_st_2), [<[sY >= 0]>], 5>> [
                Tr <<(Y !-> <[sY - sJ]>; Z !-> <[sZ2 * sX]>; J !-> (Constant 1) ;
                   Z !-> (Constant 1) ; empty_st_2), [<[sY >= 0]>], 2>> [
                  Tr <<(Y !-> <[sY - sJ]>; Z !-> <[sZ2 * sX]>;J !-> (Constant 1) ;
                      Z !-> (Constant 1) ; empty_st_2), [<[~(sY - sJ >= 0)]>;
                      <[sY >= 0]>], 6>> nil
          ]]]];
          Tr << J !-> (Constant 1) ; Z !-> (Constant 1) ; empty_st_2,
             [<[~(sY >= 0)]>], 6>> nil
    ]]]).
Proof.
  (* Z := 1 *)
  apply E_Assign with (x := Z) (ie := <{IntLit 1}>) (se := <{Constant 1}>)
                      (st := empty_st_2) (n := O) (pc := nil);
  try reflexivity.
  unfold SAT. exists SAT_assign_prog_2_true_branch. simpl. reflexivity.
  (* J := 1 *)
  apply E_Assign with (x := J) (ie := <{IntLit 1}>) (se := <{Constant 1}>)
                      (st := Z !-> (Constant 1) ; empty_st_2) (n := S O) (pc := nil);
  try reflexivity.
  unfold SAT. exists SAT_assign_prog_2_true_branch. simpl. reflexivity. 
  (* if Y >= 0. This is true for the first iteration. *)
  apply E_IfBoth with (be := Bge0 Y) (sbe := SBge0 sY) (then_body := [<{Z := Z * X }>;
                                                    <{Y := Y - J}>;
                                                    Go_To 2;
                                                    Finish])
                      (else_body := [Finish])
                      (st := J !-> (Constant 1); Z !-> (Constant 1) ; empty_st_2)
                      (n := S (S O)) (pc := nil);
  try reflexivity.
  unfold SAT. exists SAT_assign_prog_2_true_branch. simpl. reflexivity.
  unfold SAT. exists SAT_assign_prog_2_false_branch. simpl. reflexivity. 
  (* Z := Z * X  *)
  apply E_Assign with (x := Z) (ie := <{Z * X}>) (se := <[sZ2 * sX]>)
                      (st := J !-> (Constant 1); Z !-> (Constant 1) ; empty_st_2)
                      (n := S (S (S O))) (pc := [<[sY >= 0]>]);
  try reflexivity.
  unfold SAT. exists SAT_assign_prog_2_true_branch. simpl. reflexivity. 
  (* Y := Y - J  *)
  apply E_Assign with (x := Y) (ie := <{Y - J}>) (se := <[sY - sJ]>)
                      (st := Z !-> <[sZ2 * sX]>; J !-> (Constant 1);
                      Z !-> (Constant 1) ; empty_st_2) (n := S (S (S (S O))))
                      (pc := [<[sY >= 0]>]);
  try reflexivity.
  unfold SAT. exists SAT_assign_prog_2_true_branch. simpl. reflexivity.
  (* Go_To 2. Jump back up to if statement *)
  apply E_GoTo with (i := S (S O)) (st := Y !-> <[sY - sJ]>; Z !-> <[sZ2 * sX]>; 
                    J !-> (Constant 1); Z !-> (Constant 1) ; empty_st_2) 
                    (n := S (S (S (S (S O))))) (pc := [<[sY >= 0]>]);
  try reflexivity.
  unfold SAT. exists SAT_assign_prog_2_true_branch. simpl. reflexivity.
  (* If Y >= 0. This is not true anymore. Have to use the above axiom for this case,
     since now Y has been updated to be the symbol sY - sJ, but the condition is only
     checking sY >=0. *)
  apply E_IfElse with (be := <{Y >= 0}>) (sbe := <[(sY - sJ) >= 0]>)
                       (then_body := [<{Z := Z * X }>;
                                      <{Y := Y - J}>;
                                      Go_To 2;
                                      Finish])
                        (else_body := [Finish]) (st := Y !-> <[sY - sJ]>;
                        Z !-> <[sZ2 * sX]>; J !-> (Constant 1);
                        Z !-> (Constant 1) ; empty_st_2) 
  (n := S(S O)) (pc := [<[sY >= 0]>]);
  try reflexivity. exists SAT_assign_prog_2_true_branch. simpl. reflexivity.
  (* Finish. This is the end of the road for the original true branch. *)  
  apply E_Finish with (st := Y !-> <[sY - sJ]>; Z !-> <[sZ2 * sX]>;
                      J !-> (Constant 1); Z !-> (Constant 1) ; empty_st_2) 
                      (n := 6%nat)
                      (pc := [<[~((sY - sJ) >= 0)]>; <[sY >= 0]>]); 
  try reflexivity.
  exists SAT_assign_prog_2_true_branch. simpl. reflexivity.
  (* Finish. This is the end of the road for the original else branch. *)  
  apply E_Finish with (st := J !-> (Constant 1); Z !-> (Constant 1) ; empty_st_2) 
                      (n := 6%nat) (pc := [<[~(sY >= 0)]>]);
  try reflexivity.
  exists SAT_assign_prog_2_false_branch. simpl. reflexivity.
Qed.

(** This symbolic execution tree ends with two leaves. *)
Definition prog_2_leaves :=
  [ Pand (SBnot (SBge0 <{sY s- sJ}>)) (Pand (SBge0 sY) nil); Pand (SBnot (SBge0 sY)) nil ].

(** This proves that the first leaf node does not appear later in the  list of
    leaves. This is sufficient for this case where we just have two leaves, but the
    idea of the proof would be the same for more leaves, just having to repeat for
    the subsequent sublists of leaves.*)
Theorem property_2_ex_2 : forall (pc : PathCond), 
  (get_head_pc prog_2_leaves) = pc -> ~ (In pc (tl prog_2_leaves)).
Proof.
  intros. unfold not. unfold prog_2_leaves. intros. inversion H0. simpl in H. 
  rewrite <- H in H1. discriminate H1. simpl in H1. destruct H1.
Qed.

(* ===================  End:  Proof of Property 2 for Program 2. ==================== *)


(* ===================  Start: Proof of Property 2 for Program 3. =================== *)

(** Figure 3 from the King paper did not give a specific program, so we came up with
    our own simple while loop example. *)
Definition prog_3 := [<{X := A}>;
                      <{while X >= 0 do
                        [<{X := X - (IntLit 1)}>; Go_To 1; Finish] end}>;
                      Finish].

Definition empty_st_3 := (A !-> sA; _ !-> (Constant 0)).

(** SAT assign for iterating once and stopping *)
Definition SAT_assignment_3_1: concreteState := (X !-> 0; A !-> 0; _ !-> 0).
(** SAT assign for never looping *)
Definition SAT_assignment_3_2: concreteState := (X !-> -1; A !-> -1; _ !-> 0).

(* This axiom is needed for the same reason as stated above.*)
Axiom prog3_after_1_iteration :
  findStatement prog_3 1 =
  <{while sX s- (Constant 1) >= 0 do
    [<{ X := X - (IntLit 1) }>; Go_To 1; Finish] end }>.

(** Now we provide the symbolic execution tree for this example in the case that the 
    loop iterates at most once and prove it is correct. The 'true' branch is the
    case that the loop executes and the `false` branch is when it does not. *)
Example prog_3_eval :
  node_eval prog_3 (Node empty_st_3 nil 0)
  (Tr (Node empty_st_3 nil 0) [(
    Tr (Node (X !-> A ; empty_st_3) nil 1) [(
    Tr (Node (X !-> A ; empty_st_3) (Pand <{X >= 0}> nil) 2) [(
      Tr (Node (X !-> <{A s- Constant 1}> ; X !-> A; empty_st_3)
        (Pand <{X >= 0}> nil) 3) [(
        Tr (Node (X !-> <{A s- Constant 1}> ; X !-> A; empty_st_3)
           (Pand <{X >= 0}> nil) 1) [(
          Tr (Node (X !-> <{A s- Constant 1}> ; X !-> A; empty_st_3)
             (Pand <{ ~ sX s- (Constant 1) >= 0 }> (Pand <{ X >= 0 }> nil)) 5) nil
    )])])]);  
      Tr (Node (X !-> A ; empty_st_3)  (Pand  <{ ~X >= 0}> nil) 5) nil 
  ])]).
Proof. 
  (* X := A *)
  apply E_Assign with (x := X) (ie := <{IntId A}>) (se := sA)
                      (st := empty_st_3) (n := O) (pc := nil); try reflexivity.
  unfold SAT. exists SAT_assignment_3_1. reflexivity.
  (* While X >= 0 *)
  apply E_WhileSAT with (be := Bge0 sX)
                        (body := [<{X := X - (IntLit 1)}>; Go_To 1; Finish])
                        (st := X !-> A;  empty_st_3) (n := S O) (pc := nil);
  try reflexivity.
  unfold SAT. exists SAT_assignment_3_1. reflexivity.
  (* X := X - 1 *)
  apply E_Assign with (x := X) (ie := <{X - IntLit 1}>) (se := <{A s- Constant 1}>)
                      (st :=  X !-> A; empty_st_3) (n := S (S O))
                      (pc := Pand <{X >= 0}> nil); 
  try reflexivity.
  unfold SAT. exists SAT_assignment_3_1. simpl. reflexivity. 
  (* GoTo Top of While *)
  apply E_GoTo with (i := S O) (st :=  X !-> <{A s- Constant 1}>; X !-> A; empty_st_3) 
                    (n :=  S ( S (S O))) (pc := Pand <{X >= 0}> nil); 
  try reflexivity.
  unfold SAT. exists SAT_assignment_3_1. simpl. reflexivity. 
  (* While X >=0 (this time it's not) *)
  apply E_WhileUnSAT with (body := [<{X := X - (IntLit 1)}>; Go_To 1; Finish])
                          (be := Bge0 (SymSub sX (Constant 1)))
                          (st :=  X !-> <{A s- Constant 1}>; X !-> A; empty_st_3)
                          (n :=  S O) (pc := Pand <{X >= 0}> nil);
  try reflexivity. apply prog3_after_1_iteration.
  unfold SAT. exists SAT_assignment_3_1. simpl. reflexivity. 
  (* Done with 'true' branch *)
  apply E_Finish with (st :=  X !-> <{A s- Constant 1}>; X !-> A; empty_st_3)
                      (n :=  S (S (S (S (S O)))))
                      (pc := Pand <{ ~ sX s- (Constant 1) >= 0 }>
                        (Pand <{ X >= 0 }> nil));
  try reflexivity. unfold SAT. exists SAT_assignment_3_1. simpl. reflexivity. 
  (* Done with 'false' branch (loop never executes) *)
  apply E_Finish with (st :=  X !-> A; empty_st_3) (n :=  S (S (S (S (S O)))))
                      (pc := Pand <{ ~ sX >= 0 }> nil);
  try reflexivity. unfold SAT. exists SAT_assignment_3_2. simpl. reflexivity.
Qed.

(** This symbolic execution tree ends with two leaves. *)
Definition prog_3_leaves := 
  [(Pand <{ ~ sX s- (Constant 1) >= 0 }> (Pand <{ X >= 0 }> nil)) ;
   Pand <{ ~ sX >= 0 }> nil].

(** This proves that the first leaf node does not appear later in the list of
    leaves. This is sufficient for this case where we just have two leaves, but the
    idea of the proof would be the same for more leaves, just having to repeat for
    the subsequent sublists of leaves. *)
Theorem property_3_ex_3 : forall (pc : PathCond), 
  (get_head_pc prog_3_leaves) = pc -> ~ (In pc (tl prog_3_leaves)).
Proof.
  intros. unfold not. unfold prog_3_leaves. intros. inversion H0. simpl in H. 
  rewrite <- H in H1. discriminate H1. simpl in H1. destruct H1.
Qed.

(* ===================  End:  Proof of Property 2 for Program 3. ==================== *)

(* ==================== Definiton of Conventional Execution  ======================== *)

(** This section will define a conventional (concrete) execution in order for us to
    then prove the commutativity of the symbolic execution of our examples. Almost
    all of the functions, types and relations defined in this section are analagous
    to the ones in the symbolic section, except that they operate over ConcreteStates
    only. *)

Inductive ConcreteTreeNode : Type :=
  | ConcreteNode (s : concreteState) (pc : PathCond) (index : nat).

Definition conventionalState := total_map IntExp.

(** Getters to extract information from the ConcreteTreeNode object. *)

Definition extractConventionalState (n : ConcreteTreeNode) : concreteState :=
  match n with 
  | ConcreteNode s _ _ => s
  end. 

Definition extractConventionalIndex (n : ConcreteTreeNode) : nat :=
  match n with 
  | ConcreteNode _ _ i => i
  end.

Definition extractConventionalPathCond (n : ConcreteTreeNode) : PathCond :=
  match n with 
  | ConcreteNode _ pc _ => pc
  end.

(** An ExecutionTree is either empty or a root node with a list of
    child trees. *)
Inductive ConcreteExecutionTree : Type :=
  | null
  | ConcreteTr (n : ConcreteTreeNode) (children : list ConcreteExecutionTree).

Fixpoint conventional_inteval (ie: IntExp) (mappings:  concreteState) :=
  match ie with 
  | IntLit n => n
  | IntAdd n1 n2 => (conventional_inteval n1 mappings) +
                    (conventional_inteval n2  mappings)
  | IntSub n1 n2 => (conventional_inteval n1 mappings ) -
                    (conventional_inteval n2 mappings)
  | IntMult n1 n2 => (conventional_inteval n1 mappings) *
                     (conventional_inteval n2 mappings)
  | IntId x => mappings x
end.

Inductive node_eval_conventional :
  Program -> ConcreteTreeNode -> ConcreteExecutionTree -> Prop :=
  | E_AssignConcrete : forall prog node x ie st n pc tree',
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (SAT pc) ->
    (findStatement prog n) = <{x := ie}> ->
    node_eval_conventional prog
      (ConcreteNode (x !-> conventional_inteval ie st ; st) pc (n+1)) tree' ->
    node_eval_conventional prog node (ConcreteTr node [tree'])

  | E_IfSATConcrete : forall prog node be then_body else_body st n pc tree1' tree2',
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (SAT pc) -> 
    node_eval_conventional prog (ConcreteNode st (Pand be pc) (n+1)) tree1' ->
    node_eval_conventional prog (ConcreteNode st (Pand (Bnot be) pc)
      (n + (length then_body))) tree2' ->
    node_eval_conventional prog node (ConcreteTr node [tree1' ; tree2'])

  | E_IfUnSATConcrete : forall prog node be then_body else_body st n pc tree,
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (findStatement prog n) = <{if be then then_body else else_body end}> ->
    (SAT (Pand (Bnot be) pc)) ->
    node_eval_conventional prog (ConcreteNode st (Pand (Bnot be) pc)
      (n + (length then_body))) tree ->
    node_eval_conventional prog node (ConcreteTr node [tree])

  | E_GoToConcrete: forall prog node i st n pc tree',
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (SAT pc) ->
    (findStatement prog n) = <{go_to i}> ->
    node_eval_conventional prog (ConcreteNode st pc i) tree' ->
    node_eval_conventional prog node (ConcreteTr node [tree'])

  | E_WhileSATConcrete: forall prog node be body st n pc tree1' tree2',
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (SAT pc) ->
    node_eval_conventional prog (ConcreteNode st (Pand be pc) (n + 1)) tree1' ->
    node_eval_conventional prog (ConcreteNode st (Pand (Bnot be) pc)
      (n + (length body) + 1)) tree2' ->
    node_eval_conventional prog node (ConcreteTr node [tree1' ; tree2'])

  | E_WhileUnSATConcrete: forall prog node be body st n pc tree,
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (findStatement prog n) = <{while be do body end}> ->
    (SAT (Pand (Bnot be) pc)) ->
    node_eval_conventional prog (ConcreteNode st (Pand (Bnot be) pc)
      (n + (length body) + 1)) tree ->
    node_eval_conventional prog node (ConcreteTr node [tree])

  | E_FinishConcrete: forall prog node st n pc,
    extractConventionalState node = st ->
    extractConventionalIndex node = n ->
    extractConventionalPathCond node = pc ->
    (SAT pc) ->
    (findStatement prog n) = Finish ->
    node_eval_conventional prog node (ConcreteTr node []).

(* ================= End Definiton of Conventional Execution  ====================== *)

(* =================== Proof of Property 3 for Program 1 =========================== *)
Definition start_state_1: concreteState :=
  (A !-> 1; B !-> 2; C!-> 1; X !-> 0; Y !-> 0; Z !-> 0; _ !-> 0).
Definition intermediate_state_1: concreteState :=
  (A !-> 1; B !-> 2; C!-> 1; X !-> 3; Y !-> 3; Z !-> 0; _ !-> 0).
Definition final_state_1: concreteState :=
  (A !-> 1; B !-> 2; C!-> 1; X !-> 3; Y !-> 3; Z !-> 4; _ !-> 0).

(** Proof the following concrete execution tree is correct for prog 1.*)
Example prog_1_eval_conventional :
  node_eval_conventional prog_1 (ConcreteNode start_state_1 nil 0)
    (ConcreteTr (ConcreteNode start_state_1 nil 0) [(
      ConcreteTr (ConcreteNode (X !-> start_state_1 A + start_state_1 B; 
                  start_state_1) nil 1) [(
        ConcreteTr (ConcreteNode (Y !-> start_state_1 B + start_state_1 C;
                    X !-> start_state_1 A + start_state_1 B ; start_state_1) nil 2) [(
          ConcreteTr (ConcreteNode (Z !-> intermediate_state_1 X + intermediate_state_1
                      Y - start_state_1 B; Y !-> start_state_1 B + start_state_1 C;
                      X !-> start_state_1 A + start_state_1 B; start_state_1) nil 3) nil
    )])])]).
Proof.
  (* X := A + B *)
  apply E_AssignConcrete with (x := X) (ie := <{A + B}>)
                              (st := start_state_1) (n := O) (pc := nil);
  try reflexivity.
  unfold SAT. exists final_state_1. simpl. reflexivity. 
  (* Y := B + C*)
  apply E_AssignConcrete with (x := Y) (ie := <{B + C}>) 
                              (st := X !-> start_state_1 A + start_state_1 B;
                               start_state_1)
                              (n := S O) (pc := nil); try reflexivity.
  unfold SAT. exists final_state_1. simpl. reflexivity.
    (* Z := X + Y - B *)
  apply E_AssignConcrete with (x := Z ) (ie := <{X + Y - B}>)
                              (st := Y !-> start_state_1 B + start_state_1 C;
                               X !-> start_state_1 A + start_state_1 B ; start_state_1)
                              (n := S (S O)) (pc := nil);
  try reflexivity.
  unfold SAT. exists final_state_1. simpl. reflexivity.
  apply E_FinishConcrete with (st := Z !-> intermediate_state_1 X + intermediate_state_1 
                               Y - start_state_1 B;
                               Y !-> start_state_1 B + start_state_1 C;
                               X !-> start_state_1 A + start_state_1 B; start_state_1)
                              (n := S (S (S O))) (pc := nil);
  try reflexivity.
  unfold SAT. exists final_state_1. simpl. reflexivity.
Qed.

(** Conventional execution tree for example 1. Proved correct above. *)
Definition prog_1_conventional_tree := 
  node_eval_conventional prog_1 (ConcreteNode start_state_1 nil 0)
    (ConcreteTr (ConcreteNode start_state_1 nil 0) [(
      ConcreteTr (ConcreteNode (X !-> start_state_1 A + start_state_1 B; 
                  start_state_1) nil 1) [(
        ConcreteTr (ConcreteNode (Y !-> start_state_1 B + start_state_1 C;
                    X !-> start_state_1 A + start_state_1 B ; start_state_1) nil 2) [(
          ConcreteTr (ConcreteNode (Z !-> intermediate_state_1 X + intermediate_state_1
                      Y - start_state_1 B; Y !-> start_state_1 B + start_state_1 C;
                      X !-> start_state_1 A + start_state_1 B; start_state_1) nil 3) nil
    )])])]).

(** Final concrete node (i.e. leaf) in example 1's conventional tree. *)
Definition final_concrete_node_ex_1 :=
  ConcreteNode (Z !-> intermediate_state_1 X + intermediate_state_1 Y - start_state_1 B;
                Y !-> start_state_1 B + start_state_1 C;
                X !-> start_state_1 A + start_state_1 B; start_state_1) nil 3.

(** Function used to show equivalence of two states for example 1.*)
Definition ex_1_states_equivalent (s1 s2 : concreteState) : bool :=
  if Z.eqb (s1 X) (s2 X) then 
  if Z.eqb (s1 Y) (s2 Y) then 
  if Z.eqb (s1 Z) (s2 Z) then 
  if Z.eqb (s1 A) (s2 A) then 
  if Z.eqb (s1 B) (s2 B) then 
  if Z.eqb (s1 C) (s2 C) then true else false else false else false else false else false else false.
              
(** The final state of the concrete execution tree is the same as the SAT_assignment
    for the symbolic execution of the same example.*)                     
Theorem eval_1_commutative :  
  ex_1_states_equivalent (extractConventionalState final_concrete_node_ex_1) SAT_assign_ex_1 = true.
Proof. simpl. reflexivity. Qed.

(* =================== End: Proof of Property 3 for Program 1 ====================== *)

(* ================== Start: Proof of Property 3 for Program 2 ===================== *)

Definition start_state_2: concreteState := ( X !-> 1; Y !-> 0; _ !-> 0).
Definition final_state_2_true_branch: concreteState :=
  (J !-> 1 ; Z !-> 1 ; X !-> 1; Y !-> 0; _ !-> 0).
Definition start_state_2_false_branch: concreteState := (X !-> 1; Y !-> -2; _ !-> (0)).

(** As done in the previous example, we provide a proof that this conventional 
    execution tree is correct for this example so we can use information in its leaf
    nodes to prove commutatitivy. *)
Example prog_2_eval_conventional :
  node_eval_conventional prog_2 (ConcreteNode start_state_2 nil 0)
    (ConcreteTr (ConcreteNode start_state_2 nil 0) [(
      ConcreteTr (ConcreteNode (Z !-> 1 ; start_state_2) nil 1) [(
        ConcreteTr (ConcreteNode (J !-> 1 ; Z !-> 1 ; start_state_2) nil 2) [(
        ConcreteTr (ConcreteNode (J !-> 1 ; Z !-> 1 ; start_state_2) 
                   (Pand (Bge0 Y) nil) 3) [(
        ConcreteTr (ConcreteNode 
                   (Z !-> final_state_2_true_branch Z * final_state_2_true_branch X;
                   J !-> 1 ; Z !-> 1 ; start_state_2) (Pand (Bge0 Y) nil) 4) [(
        ConcreteTr (ConcreteNode
                   (Y !-> final_state_2_true_branch Y - final_state_2_true_branch J ;
                   Z !-> final_state_2_true_branch Z * final_state_2_true_branch X;
                   J !-> 1 ; Z !-> 1 ; start_state_2) (Pand (Bge0 Y) nil) 5) [(
        ConcreteTr (ConcreteNode
                   (Y !-> final_state_2_true_branch Y - final_state_2_true_branch J ;
                   Z !-> final_state_2_true_branch Z * final_state_2_true_branch X ;
                   J !-> 1 ; Z !-> 1 ; start_state_2) (Pand (Bge0 Y) nil) 2) [
        ConcreteTr (ConcreteNode
                   (Y !-> final_state_2_true_branch Y - final_state_2_true_branch J ;
                   Z !-> final_state_2_true_branch Z * final_state_2_true_branch X ;
                   J !-> 1 ; Z !-> 1 ; start_state_2) (Pand <{ ~ sY s- sJ >= 0 }>
                   (Pand <{ sY >= 0 }> nil)) 6) nil]
        )])])]);
        ConcreteTr (ConcreteNode (J !-> 1 ; Z !-> 1 ; start_state_2)
                   (Pand (Bnot (Bge0 Y)) nil) 6) nil
  ])])]).
Proof.
  (* Z := 1 *)
  apply E_AssignConcrete with (x := Z) (ie := IntLit 1) 
                              (st := start_state_2) (n := O) (pc := nil);
  try reflexivity.
  unfold SAT. exists final_state_2_true_branch. simpl. reflexivity.
  (* J := 1 *)
  apply E_AssignConcrete with (x := J) (ie := IntLit 1) 
                              (st := Z !-> 1 ; start_state_2) (n := S O) (pc := nil); 
  try reflexivity.
  unfold SAT. exists final_state_2_true_branch. simpl. reflexivity. 
  (* if Y >= 0. This is true for the first iteration. *)
  apply E_IfSATConcrete with (be := Bge0 sY) (then_body := [<{Z := Z * X }>;
                                                            <{Y := Y - J}>;
                                                            Go_To 2;
                                                            Finish])
                             (else_body := [Finish])
                             (st := J !-> 1 ; Z !-> 1 ; start_state_2) (n := S (S O))
                             (pc := nil);
  try reflexivity. unfold SAT. exists final_state_2_true_branch. simpl. reflexivity.
  (* Z := Z * X  *)
  apply E_AssignConcrete with (x := Z) (ie := <{Z * X}>) 
                              (st := J !-> 1 ; Z !-> 1 ; start_state_2)
                              (n := S (S (S O))) (pc := Pand <{ sY >= 0 }> nil);
  try reflexivity.
  unfold SAT. exists final_state_2_true_branch. simpl. reflexivity. 
  (* Y := Y - J  *)
  apply E_AssignConcrete with (x := Y) (ie := <{Y - J}>)
                              (st := Z !-> final_state_2_true_branch Z * 
                              final_state_2_true_branch X; J !-> 1 ; Z !-> 1 ; 
                              start_state_2) (n := S (S (S (S O))))
                              (pc := Pand <{ sY >= 0 }> nil);
  try reflexivity.
  unfold SAT. exists final_state_2_true_branch. simpl. reflexivity.
  (* Go_To 2. Jump back up to if statement *)
  apply E_GoToConcrete with (i := S(S(O))) (st := Y !-> final_state_2_true_branch Y - 
                            final_state_2_true_branch J ; 
                            Z !-> final_state_2_true_branch Z * 
                            final_state_2_true_branch X ;
                            J !-> 1 ; Z !-> 1 ; start_state_2) 
                            (n := 5%nat) (pc := Pand <{ sY >= 0 }> nil);
  try reflexivity.
  unfold SAT. exists final_state_2_true_branch. simpl. reflexivity.
  (* If Y >= 0. No longer true  *)
  apply E_IfUnSATConcrete with (be := Bge0 (SymSub sY sJ))
                               (then_body := [<{Z := Z * X }>;
                                              <{Y := Y - J}>;
                                              Go_To 2;
                                              Finish])
                               (else_body := [Finish])
                               (st := Y !-> final_state_2_true_branch Y - 
                               final_state_2_true_branch J ;
                               Z !-> final_state_2_true_branch Z * 
                               final_state_2_true_branch X;
                               J !-> 1 ; Z !-> 1 ; start_state_2) 
                               (n := S(S O)) (pc := Pand <{ sY >= 0 }> nil);
  try reflexivity. 
  apply cond_after_1_iteration. unfold SAT. exists final_state_2_true_branch.
  simpl. reflexivity.
  (* Finish. This is the end of the road for the original true branch. *)  
  apply E_FinishConcrete with (st := Y !-> final_state_2_true_branch Y -
                               final_state_2_true_branch J ;
                               Z !-> final_state_2_true_branch Z * 
                               final_state_2_true_branch X;
                               J !-> 1 ; Z !-> 1 ; start_state_2) 
                               (n := 6%nat) (pc := (Pand <{ ~ sY s- sJ >= 0 }>
                                                    (Pand <{ sY >= 0 }> nil)));
  try reflexivity.
  exists final_state_2_true_branch. simpl. reflexivity.
  (* Finish. This is the end of the road for the original else branch. *)  
  apply E_FinishConcrete with (st := J !-> 1; Z !-> 1 ; start_state_2) 
                              (n := 6%nat) (pc := (Pand <{ ~ Y >= 0 }> nil));
  try reflexivity.
  exists SAT_assign_prog_2_false_branch. simpl. reflexivity.
Qed.

(** We prove that each of the two paths through this program are commutative.*)

(* ========== Start:  Proof of Property 3 for Prog 2 Path 1 (True Branch) ========== *)
Definition final_concrete_node_ex_2_true_branch :=
  ConcreteNode (Y !-> final_state_2_true_branch Y - final_state_2_true_branch J ;
  Z !-> final_state_2_true_branch Z * final_state_2_true_branch X;J !-> 1 ; Z !-> 1 ; 
  start_state_2) (Pand <{ ~ sY s- sJ >= 0 }> (Pand <{ sY >= 0 }> nil)) 6.

Definition final_concrete_node_state :=
  (Y !-> final_state_2_true_branch Y - final_state_2_true_branch J ;
  Z !-> final_state_2_true_branch Z * final_state_2_true_branch X;
  J !-> 1 ; Z !-> 1 ; start_state_2).

Definition final_symbolic_node_ex_2_true_branch := 
  Node (Y !-> <{sY s- sJ}>; Z !-> <{sZ2 s* sX}>;J !-> (Constant 1) ;
  Z !-> (Constant 1) ; empty_st_2)
  (Pand <{ ~ sY s- sJ >= 0 }> (Pand <{ sY >= 0 }> nil)) 6.

(** Concreteize the state of the last symbolic node on the true branch. *)
Definition final_symbolic_node_state_sub :=
  ( Y !-> substituteInt <{sY s- sJ}> SAT_assign_prog_2_true_branch;
  Z !-> substituteInt <{sZ2 s* sX}> SAT_assign_prog_2_true_branch ;
  J !-> 1 ; Z !-> 1; start_state_2).

(* Function used to show equivalence of two states for example 2.*)
Definition ex_2_states_equivalent (s1 s2 : concreteState) : bool :=
  if  Z.eqb (s1 X) (s2 X) then 
  if Z.eqb (s1 Y) (s2 Y) then 
  if Z.eqb (s1 Z) (s2 Z) then 
  if Z.eqb (s1 J) (s2 J) then 
    true else false else false else false else false.

(** - The inital state concrete state for conventional execution and the SAT
      assignment for the symbolic exeuction of the true branch are the same.
    - The final state of the concrete execution tree is the same as the final state
      of the the symbolic execution of the same example. *)                     
Theorem eval_2_commutative_true_branch : 
  (ex_2_states_equivalent 
    start_state_2
    SAT_assign_prog_2_true_branch) = true /\
  (ex_2_states_equivalent 
    final_concrete_node_state
    final_symbolic_node_state_sub) = true.
Proof.
  split; simpl; reflexivity.
Qed.

(* =========== End: Proof of Property 3 for Prog 2 Path 1 (True Branch) =========== *)

(* ========== Start: Proof of Property 3 for Prog 2 Path 2 (False Branch) ========= *)

Definition final_concrete_node_state_false :=
  (J !-> 1 ; Z !-> 1 ; start_state_2_false_branch). 

Definition final_symbolic_node_state_false := 
  (J !-> substituteInt(Constant 1) SAT_assign_prog_2_false_branch;
  Z !-> substituteInt (Constant 1) SAT_assign_prog_2_true_branch ; 
  start_state_2_false_branch).

(** - The inital state concrete state for conventional execution and the SAT
      assignment for the symbolic exeuction of the false branch are the same.
    - The final state of the concrete execution tree is the same as the final state
      of the the symbolic execution of the same example.  *)   
Theorem eval_2_commutative_false_branch : 
  (ex_2_states_equivalent 
    start_state_2_false_branch
    SAT_assign_prog_2_false_branch) = true /\
 (ex_2_states_equivalent 
    final_concrete_node_state_false
    final_symbolic_node_state_false) = true.
Proof.
  split; simpl; reflexivity.
Qed.
(* =========== End: Proof of Property 3 for Prog 2 Path 2 (False Branch) =========== *)

(* =================== End: Proof of Property 3 for Program 2 ====================== *)

(* ================== Start: Proof of Property 3 for Program 3 ===================== *)

(** start state for iterating once and stopping *)
Definition start_state_3_1: concreteState := ( A !-> 0; _ !-> 0).
Definition end_state_3_1 := ( X !-> -1; A !-> 0; _ !-> 0).

(** start state for never looping *)
Definition start_state_3_2: concreteState := ( X !-> -1; A !-> -1; _ !-> 0).
Definition end_state_3_2 : concreteState := ( X !-> -1 ; A !-> -1; _ !-> 0).

(** Proof that this conventional execution tree is correct for this example so we
    can use information in its leaf nodes to prove commutatitivy. *)
Example prog_3_eval_conventional :
  node_eval_conventional prog_3 (ConcreteNode start_state_3_1 nil 0)
    (* X := A*)
    (ConcreteTr (ConcreteNode start_state_3_1 nil 0) [(
    (* while x >=0 *)
    ConcreteTr (ConcreteNode (X !-> start_state_3_1 A ; start_state_3_1) nil 1) [(
    (* X = X - 1  *)
    ConcreteTr (ConcreteNode (X !-> start_state_3_1 A ; start_state_3_1) 
               (Pand <{X >= 0}> nil) 2) [(
    (* GoTo *)
    ConcreteTr (ConcreteNode (X !-> start_state_3_1 X - 1 ; X !-> start_state_3_1 A;
                start_state_3_1)
               (Pand <{X >= 0}> nil) 3) [(
    (* While_unsat *)
    ConcreteTr (ConcreteNode (X !-> start_state_3_1 X - 1 ; X !-> start_state_3_1 A;
                start_state_3_1)
               (Pand <{X >= 0}> nil) 1) [(
    (* finish *)
    ConcreteTr (ConcreteNode (X !-> start_state_3_1 X - 1 ; X !-> start_state_3_1 A; 
                start_state_3_1)
               (Pand <{ ~ sX s- (Constant 1) >= 0 }> (Pand <{ X >= 0 }> nil)) 5) nil
  )])])]);        
    (* unsat/finish*)
    ConcreteTr (ConcreteNode (X !-> start_state_3_1 A ; start_state_3_1) 
    (Pand <{ ~X >= 0}> nil) 5) nil 
  ])]).
Proof. 
  (* X := A *)
  apply E_AssignConcrete with (x := X) (ie := <{IntId A}>) 
                              (st := start_state_3_1) (n := O) (pc := nil);
  try reflexivity.
  unfold SAT. exists start_state_3_1. reflexivity.
  (* While X >= 0 *)
  apply E_WhileSATConcrete with (be := Bge0 sX) (body := [<{X := X - (IntLit 1)}>;
                                                          Go_To 1;
                                                          Finish])
                                (st := X !-> 0;  start_state_3_1)
                                (n := S O) (pc := nil);
  try reflexivity.
  unfold SAT. exists start_state_3_1. reflexivity.
  (* X := X - 1 *)
  apply E_AssignConcrete with (x := X) (ie := <{X - IntLit 1}>) 
                              (st :=  X !-> 0; start_state_3_1)
                              (n := S (S O)) (pc := Pand <{X >= 0}> nil); 
  try reflexivity.
  unfold SAT. exists start_state_3_1. simpl. reflexivity. 
  (* GoTo Top of While **)
  apply E_GoToConcrete with (i := S O) (st :=  X !-> start_state_3_1 X - 1; X !-> 0;
                            start_state_3_1)
                            (n :=  S (S (S O))) (pc := Pand <{X >= 0}> nil); 
  try reflexivity.
  unfold SAT. exists start_state_3_1. simpl. reflexivity. 
  (* While X >=0 (this time its not) **)
  apply E_WhileUnSATConcrete with (body := [<{X := X - (IntLit 1)}>;
                                            Go_To 1;
                                            Finish])
                                  (be := Bge0 (SymSub sX (Constant 1))) 
                                  (st :=  X !-> start_state_3_1 X - 1; X !-> 0;
                                  start_state_3_1)
                                  (n :=  S O) (pc := Pand <{X >= 0}> nil);
  try reflexivity. apply prog3_after_1_iteration.
  unfold SAT. exists start_state_3_1. simpl. reflexivity. 
  (* Done with `true` branch **)
  apply E_FinishConcrete with (st :=  X !-> start_state_3_1 X - 1; X !-> 0;           
                              start_state_3_1) (n :=  S (S (S (S (S O)))))
                              (pc := Pand <{ ~ sX s- (Constant 1) >= 0 }>
                              (Pand <{ X >= 0 }> nil));
  try reflexivity. unfold SAT. exists start_state_3_1. simpl. reflexivity. 
  (* Done with `false` branch (loop never executes**)
  apply E_FinishConcrete with (st := X !-> 0 ; start_state_3_1)
                              (n :=  5%nat) (pc := Pand <{ ~ sX >= 0 }> nil);
  try reflexivity. unfold SAT. exists end_state_3_2. simpl. reflexivity.
Qed.

(** We prove that each of the two paths through this program are commutative.
    Reminder: we call the case that the loop executes the 'True branch' and the case
    that the loop never executes the 'False branch.' *)

(* =========== Start: Proof of Property 3 for Prog 2 Path 1 (True Branch) =========== *)
Definition final_concrete_node_ex_3_true_branch :=
    (ConcreteNode (X !-> start_state_3_1 X - 1 ; X !-> start_state_3_1 A; 
    start_state_3_1)
      (Pand <{ ~ sX s- (Constant 1) >= 0 }> (Pand <{ X >= 0 }> nil)) 5).

Definition final_symbolic_node_ex_3_true_branch := 
  (Node (X !-> <{A s- Constant 1}> ; X !-> A; empty_st_3)
    (Pand <{ ~ sX s- (Constant 1) >= 0 }> (Pand <{ X >= 0 }> nil)) 5).

(** Concreteize the state of the last symbolic node on the true branch. *)
Definition final_symbolic_node_3_state_sub :=
  (X !-> substituteInt <{A s- Constant 1}> SAT_assignment_3_1 ;
  X !-> substituteInt A SAT_assignment_3_1; _ !-> 0).

(** Function used to show equivalence of two states for example 1.*)
Definition ex_3_states_equivalent (s1 s2 : concreteState) : bool :=
  if  Z.eqb (s1 X) (s2 X) then 
  if Z.eqb (s1 A) (s2 A) then 
    true else false else false.

(** - The inital state concrete state for conventional execution and the SAT
      assignment for the symbolic exeuction of the true branch are the same.
    - The final state of the concrete execution tree is the same as the final state of
      the symbolic execution of the same example.*)                     
Theorem eval_3_commutative_true_branch : 
  (ex_3_states_equivalent 
    start_state_3_1
    SAT_assignment_3_1) = true /\
  (ex_3_states_equivalent 
    end_state_3_1
    final_symbolic_node_3_state_sub) = true.
Proof.
  split; simpl; reflexivity.
Qed.

(* =========== End: Proof of Property 3 for Prog 3 Path 1 (True Branch) ============ *)

(* ========= Start of Proof of Property 3 for Prog 3 Path 2 (False Branch) ========= *)
 

Definition final_symbolic_node_state_false_3 := 
  (X !-> substituteInt A SAT_assignment_3_2; _ !-> 0).

(** - The inital state concrete state for conventional execution and the SAT
      assignment for the symbolic exeuction of the false branch are the same.
    - The final state of the concrete execution tree is the same as the final state
      of the symbolic execution of the same example.  *)   
Theorem eval_3_commutative_false_branch : 
  (ex_3_states_equivalent 
    start_state_3_2
    SAT_assignment_3_2 = true) /\
  (ex_2_states_equivalent 
    end_state_3_2
    final_symbolic_node_state_false_3) = true.
Proof.
  split; simpl; reflexivity.
Qed.
(* ================ End: Proof of Property 3 for Program 3 ========================= *)
