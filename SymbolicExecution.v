From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope list_scope.
(** From LF Require Import Maps. *)
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical_Pred_Type.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Structures.OrderedTypeEx.
From SE Require Export Model.
Import ListNotations.
Close Scope string_scope.

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
  (*intros. induction tr.
  - destruct i.

    *  reflexivity. 
    * simpl. reflexivity. 
  - simpl. destruct i. destruct tr1. unfold treeDiff. unfold MAX_TREE_DEPTH. *)

(** The following relation is our representation of symbolic execution of a program.
    It relates a given program, and a node corresponding to a particular statement,
    to a resultant execution tree. As defined here, the relation will generate 
    nodes for unsatisfiable path conditions (i.e. false path conditions) but
    will not progress execution past these nodes. *)

Inductive node_eval (prog: Program) : TreeNode -> list TreeNode -> Prop :=
  | E_Empty:
    let st := (emptySt prog) in
    node_eval prog <<st, nil, 0>> [<<st, nil, 0>>]
  
  | E_Assign : forall x ie st pc n path,
    let se := (makeSymbolicInt st ie) in
    let node := <<st, pc, n>> in
    let node' := <<(x, se) :: st, pc, n+1>> in
    (findStatement (stmts prog) n) = <{x := ie}> ->
    node_eval prog node path ->
    node_eval prog node' (node' :: path)

   | E_IfThen : forall be then_body else_body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let node := <<st, pc, n>> in
    let node' := <<st, sbe::pc, (n+1)>> in
    (findStatement (stmts prog) n) = <{if be then then_body else else_body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (sbe::pc)) ->
    node_eval prog node path ->
    node_eval prog node' (node' :: path)

  | E_IfElse : forall be then_body else_body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let node := <<st, pc, n>> in
    let node' := << st, (<[~sbe]>)::pc, (n + (progLength then_body))>> in
    (findStatement (stmts prog) n) = <{if be then then_body else else_body end}> ->
    (SAT (<[~sbe]>::pc)) ->
    node_eval prog node path ->
    node_eval prog node' (node' :: path)

   | E_GoTo: forall pos st pc n path,
    let node := << st, pc, n>> in
    let node' := <<st, pc, pos>> in
    (findStatement (stmts prog) n) = <{go_to pos}> ->
    node_eval prog node path ->
    node_eval prog node' (node' :: path)

  | E_WhileBody: forall be body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let node := <<st, pc, n>> in
    let node' := <<st, sbe::pc, (n + 1)>> in
    (findStatement (stmts prog) n) = <{while be do body end}> ->
    (SAT (sbe:: pc)) ->
    node_eval prog node path ->
    node_eval prog node' (node' :: path)

 | E_WhileSkip: forall be body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let node := <<st, pc, n>> in
    let node' := << st, (<[~sbe]>:: pc), (n + (progLength body) + 1)>> in
    (findStatement (stmts prog) n) = <{while be do body end}> ->
    (SAT (<[~sbe]>:: pc)) ->
    node_eval prog node path ->
    node_eval prog node' (node' :: path).

(** This is stating
    that if a superset of a condition is satisfiable, then the condition itself is 
    satisfiable. *)
Theorem superset_SAT : forall (p: PathCond) (sbe : SBoolExp),
  SAT (sbe::p) -> SAT p.
Proof. intros. destruct H. unfold SAT. exists x. simpl in H. destruct (eval_pc p x). 
 - reflexivity.
 - rewrite andb_comm in H. simpl in H. apply H.
Qed.

Lemma eval_pc_false : forall p cs,
  eval_pc p cs = false ->
  exists sbe, In sbe p /\ (substituteBool sbe cs) = false.
Proof.
  intros. induction p.
  discriminate.
  simpl in H. remember (substituteBool a cs).
  destruct b.
  - simpl in H. apply IHp in H. destruct H as [sbe [H1 H2]].
    exists sbe. split. right. apply H1. apply H2.
  - exists a. split. left. reflexivity. easy.
Qed.

Lemma SAT_terms : forall p,
  SAT p <-> exists cs, forall sbe, (In sbe p -> (substituteBool sbe cs) = true).
Proof.
  split; intros.
  - unfold SAT in H. destruct H. exists x. induction p.
    + intros. destruct H0.
    + intros. simpl in H. destruct H0.
      * subst. destruct (substituteBool sbe x).
        reflexivity. discriminate.
      * apply IHp. destruct (substituteBool a x).
        simpl in H. destruct (eval_pc p x).
        reflexivity. discriminate. discriminate.
        apply H0.
  - destruct H as [cs H]. induction p.
    + exists nil. reflexivity.
    + exists cs. simpl. assert (substituteBool a cs = true).
    { apply (H a). left; reflexivity. } rewrite H0. simpl.
    remember (eval_pc p cs). destruct b.
    * reflexivity.
    * symmetry in Heqb. apply eval_pc_false in Heqb.
      destruct Heqb as [sbe [H1 H2]].
      assert (substituteBool sbe cs = true).
      { apply (H sbe). right. apply H1. }
      rewrite H2 in H3. apply H3.
Qed.

Lemma SAT_comm : forall p1 p2,
  SAT (p1 ++ p2) -> SAT (p2 ++ p1).
Proof.
  intros. apply SAT_terms. apply SAT_terms in H.
  destruct H as [cs H]. exists cs; intros.
  apply in_app_or in H0. destruct H0.
  - destruct p2. destruct H0.
    apply H. apply in_or_app. right. apply H0.
  - destruct p1. destruct H0.
    apply H. apply in_or_app. left. apply H0.
Qed.
  
Lemma superset_SAT_paths : forall p1 p2,
  SAT (p1 ++ p2) -> SAT p2.
Proof.
  intros. induction p1.
  - easy.
  - apply (superset_SAT (p1 ++ p2) a) in H.
    apply IHp1 in H. apply H.
Qed.

(* ================== End: Definition Symbolic Execution Concepts. ==================*)

(* ========================= Start: Proof of Property 1. ============================*)

(** The path condition never becomes identically false.  *)
Theorem property_1 : forall prog node path,
  node_eval prog node path ->
  SAT (extractPathCond node).
Proof.
  intros. induction H; subst; simpl; try auto.
  - exists nil. reflexivity.
Qed.

(* ========================= End: Proof of Property 1. ==============================*)

Definition prog_1 := <{ X := A + B ;
                        Y := B + C ; 
                        Z := X + Y - B }>.

Definition empty_st := [(A, sA); (B, sB); (C, sC)].


(**Example prog_1_ex : node_eval prog_1 <<[(Z, <[sA + sB + (sB + sC) - sB]>); (Y, <[sB + sC]>); (X, <[sA + sB]>); (A, sA); (B, sB); (C, sC)], nil, 3>>.
Proof.
  assert (H: node_eval prog_1 <<empty_st, nil, 0>>). { apply E_Empty. reflexivity. }
  apply E_Assign with (x := X) (ie := <{A + B}>) (st := empty_st) (n := 0%nat) (pc := nil) in H; try reflexivity.
  apply E_Assign with (x := Y) (ie := <{B + C}>) (st := (X, <[sA + sB]>) :: empty_st) (n := 1%nat) (pc := nil) in H; try reflexivity.
  apply E_Assign with (x := Z) (ie := <{X + Y - B}>) (st := (Y, <[sB + sC]>) :: (X, <[sA + sB]>) :: empty_st) (n := 2%nat) (pc := nil) in H; try reflexivity.
  simpl in H. apply H.
Qed.*)

(* ====================== Start: Proof of Property 2. ===================*)

(* Lemma nil_path : forall prog node path,
  node_eval prog node path ->
  path = [] ->
  node = <<(emptySt prog), nil, 0>>.
Proof.
  intros. induction H; try reflexivity; try discriminate.
Qed. *)

Lemma node_path : forall prog node path,
  node_eval prog node path ->
  In node path.
Proof.
  intros. induction H; left; easy.
Qed.

Lemma node_path_2 : forall prog node path,
  node_eval prog node path ->
  nth 0%nat path <<emptySt prog, nil, 0>> = node.
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma base_path : forall prog node path,
  node_eval prog node path ->
  In <<(emptySt prog), nil, 0>> path.
Proof.
  intros. induction H;
  try (left; reflexivity);
  try (right; apply IHnode_eval).
Qed.
  
  (** Version for path without current node at head. *)
  (* intros remember H as H'. clear HeqH'. induction H;
  (** Base case is a contradiction. *)
  try easy. - 
  (** Otherwise, we have two cases: either the parent
      node is the root (with an empty path), or it's not
      and we can apply the inductive hypothesis. *)
  destruct path;
  try (right; apply IHnode_eval; easy).
  - apply nil_path in H1. left. easy. easy.
  - apply nil_path in H3. left. easy. easy.
  - apply nil_path in H2. left. easy. easy.
  - apply nil_path in H1. left. easy. easy.
  - apply nil_path in H2. left. easy. easy.
  - apply nil_path in H2. left. easy. easy. *)

Definition ancestor (prog: Program) (node1 node2: TreeNode) (path2: list TreeNode): Prop :=
  node_eval prog node2 path2 /\ In node1 path2.

Lemma ancestor_eval : forall prog node1 node2 path2,
  ancestor prog node1 node2 path2 -> exists path1, node_eval prog node1 path1.
Proof. Admitted.
  (* intros. destruct H; induction H; destruct H0;
    try (exists path; rewrite <- H0; easy);
    try (apply IHnode_eval in H0; apply H0).
Qed. *)

Lemma pathcond_extend : forall prog node1 node2 path2,
  (ancestor prog node1 node2 path2) ->
  exists path_subset, extractPathCond node2 = path_subset ++ extractPathCond node1.
Proof. Admitted.
  (* intros. destruct H. induction H; destruct H0; try (rewrite <- H0);
    try (exists nil; simpl; unfold node; reflexivity);
    try (apply IHnode_eval in H0; apply H0).
  - exists [sbe]; reflexivity.
  - apply IHnode_eval in H0. destruct H0 as [p Hp].
    exists (sbe :: p). unfold node in Hp; simpl in *. rewrite Hp; reflexivity.
  - exists [<[~sbe]>]; reflexivity.
  - apply IHnode_eval in H0. destruct H0 as [p Hp].
    exists (<[~sbe]> :: p). unfold node in Hp; simpl in *. rewrite Hp; reflexivity.
  - exists [sbe]; reflexivity.
  - apply IHnode_eval in H0. destruct H0 as [p Hp].
    exists (sbe :: p). unfold node in Hp; simpl in *. rewrite Hp; reflexivity.
  - exists [<[~sbe]>]; reflexivity.
  - apply IHnode_eval in H0. destruct H0 as [p Hp].
    exists (<[~sbe]> :: p). unfold node in Hp; simpl in *. rewrite Hp; reflexivity.
Qed. *)

(* Lemma path_extend : forall prog node1 node2 path1 path2,
  node_eval prog node1 path1 ->
  ancestor prog node1 node2 path2 ->
  exists path_subset, path2 = path_subset ++ path1.
Proof. Abort. *)

Lemma path_extend : forall prog node node' path,
  node_eval prog node' (node' :: node :: path) ->
  node_eval prog node (node :: path).
Proof.
  intros. inversion H;
  try (subst; remember H4 as H5; clear HeqH5;
    apply node_path_2 in H4; simpl in H4;
    rewrite <- H4 in H5; apply H5).
  - subst. remember H3 as H4. clear HeqH4.
    apply node_path_2 in H3. simpl in H3.
    rewrite <- H3 in H4. apply H4.
  - subst. remember H5 as H6. clear HeqH6.
    apply node_path_2 in H5. simpl in H5.
    rewrite <- H5 in H6. apply H6.
  - subst. remember H3 as H4. clear HeqH4.
    apply node_path_2 in H3. simpl in H3.
    rewrite <- H3 in H4. apply H4.
Qed.

Theorem property_2_simpler : forall prog node1 node2 path2,
  ancestor prog node1 node2 path2 ->
  SAT ((extractPathCond node1) ++ (extractPathCond node2)).
Proof.
  intros. remember H as H1. clear HeqH1.
  apply pathcond_extend in H1. destruct H1 as [p H0].
  rewrite H0. apply SAT_comm.
  unfold ancestor in H. destruct H as [H _].
  apply property_1 in H. rewrite H0 in H.
  apply SAT_terms in H. destruct H as [cs H].
  apply SAT_terms. exists cs; intros. apply in_app_or in H1.
  destruct H1. apply H in H1. easy.
  apply H. apply in_or_app. right. easy.
Qed.

Lemma path_head : forall prog parent child node2 path path2,
  node_eval prog parent path ->
  node_eval prog child (child :: path) ->
  node_eval prog node2 path2 -> 
  In parent path2 ->
  ~ In child path2 ->
  parent = node2.
Proof. Admitted.

Theorem property_2 : forall prog node1 node2 path1 path2, 
(node_eval prog node1 path1) -> 
(node_eval prog node2 path2) ->
  ~(ancestor prog node1 node2 path2) ->
  ~(ancestor prog node2 node1 path1) ->
  ~ (SAT (( extractPathCond node1) ++ (extractPathCond node2))).
Proof.
  intros. intros H4. unfold ancestor in H1. apply not_and_or in H1.
  (** Since we have assumed that both nodes are in the relation, we need to
      unfold the ancestor definition to get that neither node is in the other's path. *)
  destruct H1. apply H1. apply H0.
  unfold ancestor in H2. apply not_and_or in H2.
  destruct H2. apply H2. apply H. remember H as E. clear HeqE.
  (** Now we can proceed by induction on H. *)
  induction H; intros.
    - apply base_path in H0. apply H1 in H0. apply H0.
    - apply IHnode_eval; auto.
      + clear IHnode_eval. clear H. clear H4. intro Hc.
        assert (node = node2). { apply (path_head prog node node' node2 path path2); easy. }
      apply H2. right.
        apply node_path in H0.
        destruct path2 as [| h t]. destruct Hc.
        destruct Hc. unfold In in H1. apply not_or_and in H1.
        destruct H1 as [H1 _]. destruct H1. apply H. 
      + 
    (* - apply IHnode_eval. admit. intros HI. apply H2. right. apply HI.
      simpl in *. apply H3.
    -  *)


(* ==================== End: Proof of Property 2 ===================== *)

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
