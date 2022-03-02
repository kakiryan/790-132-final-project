From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope nat_scope.
Open Scope list_scope.
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
    let parent := <<st, pc, n>> in
    let child := <<(x, se) :: st, pc, (nextInstruction (stmts prog) n)>> in
    (findStatement (stmts prog) n) = <{x := ie}> ->
    node_eval prog parent path ->
    node_eval prog child (child :: path)

   | E_IfThen : forall be then_body else_body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let parent := <<st, pc, n>> in
    let child := <<st, sbe::pc, (n+1)>> in
    (findStatement (stmts prog) n) = <{if be then then_body else else_body end}> ->
    (makeSymbolicBool st be) = sbe ->
    (SAT (sbe::pc)) ->
    node_eval prog parent path ->
    node_eval prog child (child :: path)

  | E_IfElse : forall be then_body else_body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let parent := <<st, pc, n>> in
    let child := << st, (<[~sbe]>)::pc, (n + (progLength then_body))>> in
    (findStatement (stmts prog) n) = <{if be then then_body else else_body end}> ->
    (SAT (<[~sbe]>::pc)) ->
    node_eval prog parent path ->
    node_eval prog child (child :: path)

   | E_GoTo: forall pos st pc n path,
    let parent := << st, pc, n>> in
    let child := <<st, pc, pos>> in
    (findStatement (stmts prog) n) = <{go_to pos}> ->
    node_eval prog parent path ->
    node_eval prog child (child :: path)

  | E_WhileBody: forall be body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let parent := <<st, pc, n>> in
    let child := <<st, sbe::pc, (n + 1)>> in
    (findStatement (stmts prog) n) = <{while be do body end}> ->
    (SAT (sbe:: pc)) ->
    node_eval prog parent path ->
    node_eval prog child (child :: path)

 | E_WhileSkip: forall be body st pc n path,
    let sbe := (makeSymbolicBool st be) in
    let parent := <<st, pc, n>> in
    let child := << st, (<[~sbe]>:: pc), (n + (progLength body) + 1)>> in
    (findStatement (stmts prog) n) = <{while be do body end}> ->
    (SAT (<[~sbe]>:: pc)) ->
    node_eval prog parent path ->
    node_eval prog child (child :: path).

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

Lemma node_path : forall prog node path,
  node_eval prog node path ->
  In node path.
Proof.
  intros. induction H; left; easy.
Qed.

Lemma path_not_empty : forall prog node path,
  node_eval prog node path ->
  exists tail, path = node :: tail.
Proof.
  intros; inversion H;
  try (exists nil; reflexivity);
  try (exists path0; reflexivity).
Qed.

Lemma base_path : forall prog node path,
  node_eval prog node path ->
  In <<(emptySt prog), nil, 0>> path.
Proof.
  intros. induction H;
  try (left; reflexivity);
  try (right; apply IHnode_eval).
Qed.

(* Definition ancestor (prog: Program) (node1 node2: TreeNode) (path2: list TreeNode): Prop :=
  node_eval prog node2 path2 /\ In node1 path2. *)

Definition ancestor (prog: Program) (node1 node2: TreeNode) (path2: list TreeNode): Prop :=
  node_eval prog node2 path2 /\ In node1 path2.

Lemma ancestor_eval : forall prog node1 node2 path2,
  ancestor prog node1 node2 path2 -> exists path1, node_eval prog node1 path1.
Proof.
  intros. destruct H as [H H0]. remember H as E. clear HeqE.
  induction H; destruct H0;
  try (exists (child :: path); rewrite <- H0; easy);
  try (apply IHnode_eval; easy).
  - exists [<<st, [], 0>>]. rewrite <- H. apply E_Empty.
  - destruct H.
Qed.

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

(* Lemma path_extend : forall prog node node' path,
  node_eval prog node' (node' :: node :: path) ->
  node_eval prog node (node :: path).
Proof.
  intros. inversion H;
  try (subst; remember H4 as H5; clear HeqH5;
    apply node_path_2 in H4; simpl in H4;
    rewrite <- H4 in H5; apply H5).
  - subst. remember H3 as H4. clear HeqH4.
    apply node_path_2 in H3. destruct H3. injection H0; intros.
    rewrite <- H3 in H4. apply H4.
  - subst. remember H5 as H6. clear HeqH6.
    apply node_path_2 in H5. simpl in H5.
    rewrite <- H5 in H6. apply H6.
  - subst. remember H3 as H4. clear HeqH4.
    apply node_path_2 in H3. simpl in H3.
    rewrite <- H3 in H4. apply H4.
Qed. *)

Lemma not_ancestor_not_path : forall prog node1 path1 node2 path2,
  node_eval prog node1 path1 ->
  node_eval prog node2 path2 ->
  ~(ancestor prog node1 node2 path2) ->
  ~(ancestor prog node2 node1 path1) ->
  ~(In node1 path2) /\ ~(In node2 path1).
Proof.
  intros. unfold ancestor in *. split.
  - intro. apply H1. split.
    apply H0. apply H3.
  - intro. apply H2. split.
    apply H. apply H3.
Qed.

Lemma pc_ancestor : forall prog node1 node2 path2 sbe,
  ancestor prog node1 node2 path2 ->
  In sbe (extractPathCond node1) ->
  In sbe (extractPathCond node2).
Proof.
  intros. destruct H as [H H1]. induction H; destruct H1;
  try (rewrite <- H in H0; simpl in H0; apply H0; apply H);
  try (subst; apply H0);
  try (simpl; right);
  auto.
Qed.

Lemma unique_path_head : forall prog node1 node2 path,
  node_eval prog node1 path ->
  node_eval prog node2 path ->
  node1 = node2.
Proof.
  intros. apply path_not_empty in H. apply path_not_empty in H0.
  destruct H. destruct H0.
  rewrite H in H0. injection H0; intros; easy.
Qed.

Lemma unique_child : forall prog parent path,
  let stmt := (findStatement (stmts prog) (extractIndex parent)) in
  ((exists n, stmt = <{Go_To n}>) \/
  (exists x ie, stmt = <{x := ie}>)) ->
  node_eval prog parent path ->
  exists! child, node_eval prog child (child :: path).
Proof.
  intros. destruct H.
  - destruct H as [n H]. destruct parent.
    exists <<s, pc, n>>. split.
    + simpl in *. admit.
    + intros child Hchild.
      inversion Hchild.
      * apply base_path in H0. rewrite <- H3 in H0. destruct H0.
      * simpl in *. assert (parent = <<s, pc, index>>).
        { apply (unique_path_head prog _ _ path); easy. }
        simpl in *. subst. unfold parent in H5. injection H5. intros.
        subst. unfold stmt in H. rewrite H in H2. inversion H2.
Admitted.

Lemma pc_differ : forall prog node1 node2 path1 path2,
  let pc1 := (extractPathCond node1) in
  let pc2 := (extractPathCond node2) in
  node_eval prog node1 path1 ->
  node_eval prog node2 path2 ->
  ~ ancestor prog node1 node2 path2 ->
  ~ ancestor prog node2 node1 path1 ->
  exists sbe, (In sbe pc1 /\ In <[~sbe]> pc2) \/
    (In sbe pc2 /\ In <[~sbe]> pc1).
Proof.
  intros. unfold ancestor in H1. apply not_and_or in H1.
  destruct H1. apply H1 in H0. destruct H0.
  unfold ancestor in H2. apply not_and_or in H2.
  destruct H2. apply H2 in H. destruct H. remember H as E. clear HeqE.

  induction H.
  - simpl in *. apply base_path in H0. apply H1 in H0. destruct H0.
  - assert (exists! child', node_eval prog child' (child' :: path)).
  { apply (unique_child _ parent _); try auto. right. exists x, ie; easy. }
  destruct H4 as [child' H4]. destruct H4.

  apply IHnode_eval; auto. admit. simpl in H2. apply not_or_and in H2.
  easy.
Abort.

Lemma hope : forall prog node1 node2 path1 path2,
  node_eval prog node1 path1 ->
  node_eval prog node2 path2 ->
  SAT (extractPathCond node1 ++ extractPathCond node2) ->
  In node1 path2 \/ In node2 path1.
Proof.
  intros. induction H.
  - left. apply (base_path prog node2). auto.
  (*- right. apply IHnode_eval in H1. right. destruct H1 as [H5 | H6].
    + admit.
    +  *)
  - apply IHnode_eval in H1. destruct H1.
    + left. admit.
    + right. right. auto.
  - unfold child in H1. simpl in H1. apply superset_SAT in H1.
    apply IHnode_eval in H1. destruct H1.
    + admit.
    + right. right. auto.
  - unfold child in H1. simpl in H1. apply superset_SAT in H1.
    apply IHnode_eval in H1. destruct H1.
    + admit.
    + right. right. auto.
  - apply IHnode_eval in H1. destruct H1.
    + admit.
    + right. right. auto.
  - unfold child in H1. simpl in H1. apply superset_SAT in H1.
    apply IHnode_eval in H1. destruct H1.
    + admit.
    + right. right. auto.
  - unfold child in H1. simpl in H1. apply superset_SAT in H1.
    apply IHnode_eval in H1. destruct H1.
    + admit.
    + right. right. auto.
Abort.
  
  
  
  (*remember H as E. clear HeqE.
  induction H.
  - intros. left. apply (base_path prog node2). apply H.
  - intro. induction H1; intros.
    + right. apply (base_path prog child). auto.
    + assert (In parent (child0 :: path0) \/ In child0 path).
      { admit. }
      destruct H4.
      assert (In child path0 \/ In parent0 (child :: path)).
      { admit. }
      destruct H5.
      left. right. auto.
      admit.
      right. right. apply H4.*)


Axiom excluded_middle : forall P, P \/ ~P.

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
  induction H.
  (** Now we can proceed by induction on H. *)

  (* apply SAT_terms in H4. destruct H4 as [cs H4]. *)
    - apply base_path in H0. apply H1 in H0. apply H0.
    - assert (In parent path2 \/ ~ In parent path2).
      { apply excluded_middle. }
      destruct H5.
      + clear IHnode_eval.
    (* apply IHnode_eval; auto.
      clear IHnode_eval. clear H4.
      + intro.
      + intro. assert (exists! child', node_eval prog child' (child' :: path)).
      { apply (unique_child _ parent _). right. exists x, ie; easy. easy. }
      destruct H5 as [child' [H5 H6]].
      apply (H6 child) in E. subst.
      assert (parent = node2).
      (** We know path2 = node2 :: tail, so then destruct H4 and show that parent has to be at the head or there's a contradiction with H1. *)
      { destruct path2 as [|h t]. apply base_path in H0. destruct H0.
        destruct H4.
        - admit. (* easy case *)
        - clear H. clear H2. admit.
      }
      rewrite <- H7 in H2. simpl in H2. apply not_or_and in H2.
      destruct H2. apply node_path in H3. apply H8 in H3. destruct H3.
      + simpl in H2. apply not_or_and in H2. destruct H2. auto.
    - simpl in *. apply superset_SAT in H4. apply IHnode_eval; auto.
      intro. clear IHnode_eval. clear H4. clear H5.
      apply not_or_and in H2. destruct H2.*)
Abort. 


(* ==================== End: Proof of Property 2 ===================== *)

(* ==================== Start: Proof of Property 3 ===================== *)

Check Z.

Fixpoint populateParams (params : list string) (args : list Z) : concreteState :=
  match params with
  | nil => nil
  | h :: t =>
    match args with
    | nil => (h, 0) :: (populateParams t nil)
    | h' :: t' => (h, h') :: (populateParams t t')
    end
  end.

Definition populate (prog : Program) (args : list Z) : concreteState :=
  match prog with
  | P stmts params => populateParams params args
 end.

Inductive concrete_eval (prog: Program) : ConcreteNode -> list ConcreteNode -> Prop :=
  | CE_Empty:
    forall args,
    let cs := populate prog args in 
    concrete_eval prog {{cs, 0}} [{{cs, 0}}]
  
  | CE_Assign : forall x ie cs n path,
    let parent := {{cs, n}} in
    let result := inteval ie cs in
    let child := {{(x, result) :: cs, (nextInstruction (stmts prog) n)}} in
    (findStatement (stmts prog) n) = <{x := ie}> ->
    concrete_eval prog parent path ->
    concrete_eval prog child (child :: path)

   | CE_IfThen : forall be then_body else_body cs n path,
    let parent := {{cs, n}} in
    let child := {{cs, (n+1)}} in
    (findStatement (stmts prog) n) = <{if be then then_body else else_body end}> ->
    beval be cs = true -> 
    concrete_eval prog parent path ->
    concrete_eval prog child (child :: path)

  | CE_IfElse : forall be then_body else_body cs n path,
    let parent := {{cs, n}} in
    let child :=  {{cs, (n + (progLength then_body))}} in
    (findStatement (stmts prog) n) = <{if be then then_body else else_body end}> ->
    beval be cs = false -> 
    concrete_eval prog parent path ->
    concrete_eval prog child (child :: path) 

   | CE_GoTo: forall pos cs n path,
    let parent := {{ cs, n}} in
    let child := {{ cs, pos}} in
    (findStatement (stmts prog) n) = <{go_to pos}> ->
    concrete_eval prog parent path ->
    concrete_eval prog child (child :: path)

  | CE_WhileBody: forall be body cs n path,
    let parent := {{ cs, n }} in
    let child :=  {{ cs, (n + 1)}} in
    (findStatement (stmts prog) n) = <{while be do body end}> ->
    beval be cs = true -> 
    concrete_eval prog parent path ->
    concrete_eval prog child (child :: path)

 | CE_WhileSkip: forall be body cs n path,
    let parent := {{cs, n}} in
    let child := {{cs, (n + (progLength body) + 1)}} in
    (findStatement (stmts prog) n) = <{while be do body end}> ->
    beval be cs = false -> 
    concrete_eval prog parent path ->
    concrete_eval prog child (child :: path).

Fixpoint fillState (cs: concreteState) (st: state) : concreteState := 
 match st with 
  | nil => nil
  | h::t => match h with
      | (x,se) => (x, (substituteInt se cs)) :: (fillState cs t)
      end
  end.


Lemma int_exp_equiv : forall ie st initial_cs,
let se := makeSymbolicInt st ie in
let cs := fillState initial_cs st in
(substituteInt se initial_cs) = (inteval ie cs).
Proof.
intros. induction ie.
- simpl. reflexivity.
- simpl. rewrite IHie1. rewrite IHie2. reflexivity.
- simpl. rewrite IHie1. rewrite IHie2. reflexivity.
- simpl. rewrite IHie1. rewrite IHie2. reflexivity.
- simpl in *. unfold se. simpl. induction st.
  + simpl in *. reflexivity.
  + destruct a as [k v]. simpl. destruct (string_dec k x).
    * reflexivity.
    * apply IHst.
Qed.

Lemma bool_exp_equiv : forall be st inital_cs,
let se := makeSymbolicBool st be in
let cs := fillState inital_cs st in
(substituteBool se inital_cs) = (beval be cs).
Proof.
intros. induction be.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite IHbe. reflexivity.
- simpl. assert ((substituteInt (makeSymbolicInt st n) inital_cs) = inteval n cs).
 * apply int_exp_equiv.
 * rewrite H. reflexivity.
Qed. 

(* LOL this is from class *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. 
  - destruct c eqn:Ec.
      + reflexivity.
      + intros H. rewrite <- H. 
      { destruct b eqn:Eb.
        * reflexivity.
        * reflexivity.
      }
  Qed.

(* Theorem property_3 : forall prog node path cs final_cs' n', 
 let final_cs := fillState cs (extractState node) in
 node_eval prog node path ->
 eval_pc (extractPathCond node) cs = true ->
 concrete_eval prog {{final_cs' n'}}
 *)

Fixpoint initial_state (cpath : list ConcreteNode) : concreteState :=
  match cpath with
  | nil => nil
  | h :: t => match t with
    | nil => extractConcreteState h
    | h' :: t' => (initial_state t)
    end
  end.

Lemma fillEmptySt : forall prog cs,
  fillState cs (emptySt prog) = cs.
Proof. Admitted.

(*  intros. generalize dependent args. destruct prog. induction params; intros.
  - reflexivity.
  - destruct args.
    + unfold cs in *. simpl in *. destruct (string_dec a a).
      * assert (fillState ((a, 0) :: populateParams params []) (paramsToEmptySt params) =
                populateParams params []).
      { clear e. Admitted. *)

(* induction params.
  - simpl. unfold cs. simpl in *. reflexivity.
  - simpl in *. unfold cs. unfold applyCState. simpl. destruct args.
    * unfold cs. injection. rewrite <- IHparams. 
Abort. *)

Lemma concrete_path_head : forall prog cnode cpath,
  concrete_eval prog cnode cpath ->
  exists tail, cpath = cnode :: tail.
Proof.
  intros. inversion H; try (exists path; reflexivity).
  - exists nil. reflexivity.
Qed.

Ltac wrong H := apply concrete_path_head in H; destruct H; discriminate.

Ltac auto_wrong :=
  match goal with
    H: concrete_eval ?P ?N []
    |- _ => wrong H
  end.

Lemma initial_state_match : forall prog parent child cpath,
  concrete_eval prog parent cpath ->
  concrete_eval prog child (child :: cpath) ->
  initial_state cpath = initial_state (child :: cpath).
Proof.
  intros. inversion H; try reflexivity.
Qed.

Ltac wrong_ind IH A B C D final_cs' n0 path0 prog parent0 child1 :=
  apply (IH final_cs' n0 path0 A B (initial_state path0));
  try reflexivity; simpl;
  apply (initial_state_match prog parent0 child1 path0 A) in C;
  rewrite C; apply D.

Ltac wrong_ind_auto :=
  match goal with
  | IH: forall (final_cs' : concreteState) (n' : nat)
      (cpath : list ConcreteNode),
       concrete_eval ?prog {{final_cs', n'}} cpath ->
       Datatypes.length ?path = Datatypes.length cpath ->
       forall cs : concreteState,
       initial_state cpath = cs ->
       eval_pc (extractPathCond ?parent) cs = true -> n' = extractIndex ?parent,
    A: concrete_eval ?prog ?parent0 ?path0,
    B: Datatypes.length ?path = Datatypes.length ?path0,
    C: concrete_eval ?prog ?child1 (?child1 :: ?path0),
    D: eval_pc (extractPathCond ?child) (initial_state (?child1 :: ?path0)) = true,
    n0: nat,
    final_cs': concreteState,
    path0: list ConcreteNode,
    prog: Program,
    parent0: ConcreteNode,
    child1: ConcreteNode
    
  |- _ => wrong_ind IH A B C D final_cs' n0 path0 prog parent0 child1
  end.
  

Lemma prog_index_match : forall prog node path cs cpath final_cs' n',
  node_eval prog node path ->
  concrete_eval prog {{final_cs', n'}} cpath ->
  initial_state cpath = cs ->
  eval_pc (extractPathCond node) cs = true ->
  length path = length cpath ->
  n' = extractIndex node.
Proof.
  intros. generalize dependent cs. generalize dependent cpath.
  generalize dependent n'. generalize dependent final_cs'.
  induction H; intros.
  - simpl in *. clear H2. destruct cpath. inversion H3.
    destruct cpath.
    + inversion H0; try auto_wrong.
      * reflexivity.
    + inversion H3.
  - inversion H1;
      try (subst; assert (n0 = n);
      simpl in H3; injection H3; intro Hnew; fold child1 in H1;
      try wrong_ind_auto; subst; rewrite H7 in H; discriminate).
    + subst. simpl in *. injection H3; intros.
      apply (path_not_empty prog parent path) in H0. destruct H0.
      subst. inversion H2.
    + subst; assert (n0 = n);
      simpl in H3; injection H3; intro Hnew; fold child0 in H1;
      try wrong_ind_auto; subst; simpl in *; reflexivity.
  - inversion H3.
    + subst. simpl in *. injection H4; intros.
      apply (path_not_empty prog parent path) in H2. destruct H2.
      subst. inversion H5.
    + subst; assert (n0 = n);
      simpl in H4; injection H4; intro Hnew. fold child0 in H3.
      try wrong_ind_auto.

Admitted.

Theorem property_3 : forall prog node path cs cpath final_cs' n',
  (* with some concrete state that we get by symbolically executing and then
  substituting...*)
  (* this may depend on property 2? *)
  let final_cs := fillState cs (extractState node) in
  node_eval prog node path ->
  (*... and assuming the operations are valid/the path is satisfiable ..**)
  eval_pc (extractPathCond node) cs = true ->
  (*... then we have some concrete node in the relation with internal final_cs'
  that is the result of taking some concrete path, cpath. **)
  concrete_eval prog {{final_cs', n'}} cpath ->
  (* additionally, the inital state of our concrete path is equal to the same 
   concrete state as before.. *)
  initial_state cpath = cs ->
  (* ... if the lengths of the paths are the same ... *)
  length path = length cpath ->
  (* then the final concrete state that we arrived at via substitution is the 
   same one we arrived at via directly executing the program concretely. *)
  final_cs = final_cs'.
Proof.
  intros. generalize dependent cs. generalize dependent cpath. 
  generalize dependent final_cs'. generalize dependent n'.
  remember H as E. clear HeqE. induction H; intros.
  - simpl in *. destruct cpath. inversion H3.
    destruct cpath.
      + simpl in *.
        apply (concrete_path_head prog {{final_cs', n'}} [c]) in H1.
        destruct H1. injection H; intros. rewrite H4 in H2. simpl in *.
        subst. clear H. clear H0. clear H3.
        unfold final_cs. unfold st. apply fillEmptySt.
      + simpl in *. inversion H3.
  - apply (IHnode_eval H0 n final_cs' ({{final_cs', n'}} :: cpath)).






Theorem property_3 : forall prog node path cs, 
 let final_cs := fillState cs (extractState node) in
 node_eval prog node path ->
 eval_pc (extractPathCond node) cs = true ->
 exists cpath, concrete_eval prog {{final_cs, (extractIndex node)}} cpath.
Proof.
intros. remember H as E. clear HeqE. induction H; intros.
- simpl. exists [{{final_cs, 0}}]. apply CE_Empty.
- unfold final_cs. simpl in *. apply IHnode_eval in H0. clear IHnode_eval.
  apply (CE_Assign _ x ie) in H0.
  assert (inteval ie (fillState cs st) = substituteInt se cs).
  { unfold se. symmetry. apply int_exp_equiv. }
  rewrite <- H2. apply H0. easy. easy.
- unfold final_cs. apply IHnode_eval in H3. 
  apply (CE_IfThen _ be then_body else_body) in H3. simpl in *. 
  * easy. 
  * easy. 
  * simpl. rewrite <- bool_exp_equiv. clear IHnode_eval.
    simpl in H0. rewrite andb_comm in H0.
    apply andb_true_elim2 in H0. easy.
  * simpl. simpl in H0. apply andb_true_elim2 in H0. apply H0.
- 
Admitted.

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
