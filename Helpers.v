From SE Require Export Model.
From SE Require Export Equality.

Fixpoint treeSize (tree: ExecutionTree) : nat :=
  match tree with
  | empty => O 
  | Tr node l r => S ((treeSize l) + (treeSize r))
  end.

(** Traversal strategy *)
Fixpoint findNode (tree: ExecutionTree) (target: nat) : TreeNode :=
  match tree with
  | empty => empty_node
  | Tr h l r =>
    match target with
    | O => h
    | _ => if (Nat.leb target (treeSize l))
           then findNode l (target - 1)
           else findNode r (target - (treeSize l) - 1)
    end 
  end.

Fixpoint addNode (tree: ExecutionTree) (target: nat) (node: TreeNode) : ExecutionTree :=
  match target with
  | O => 
    match tree with 
    | empty => Tr node empty empty
    | Tr h empty r => Tr h (Tr node empty empty) r
    | Tr h l empty => Tr h l (Tr node empty empty)
    | Tr h l r => tree
    end
  | _ =>
    match tree with
    | empty => empty (* Bad *)
    | Tr h l r => Tr h (addNode l (target - 1) node) (addNode r (target - (treeSize l) - 1) node)
    end 
  end.

Fixpoint isLeaf (tree: ExecutionTree) (target: nat) : bool := 
  match target with
  | O =>
    match tree with 
    | empty => false
    | Tr h empty empty => true 
    | _ => false
    end
  | _ => 
    match tree with 
    | empty => false
    | Tr h l r => orb (isLeaf l (target - 1)) (isLeaf r (target - (treeSize l) - 1))
    end
  end.

(** This function will compare the structure of two trees:
    the common case is that the first argument is a subtree
    of the second. Conceptually, it overlays the two trees, and returns a list of all nodes which don't have a
    counterpart in the same position in the other tree. Since
    Coq can't infer a strictly decreasing argument otherwise,
    we provide a maximum tree depeth and wrap this helper
    inside another function. *)
Fixpoint treeDiffHelper (tr1 tr2: ExecutionTree) (gas: nat) : list TreeNode :=
  match gas with 
  | O => nil 
  | S gas' =>
    match tr1 with 
    | empty =>
      match tr2 with
      | empty => nil 
      | Tr h2 l2 r2 => h2 :: ((treeDiffHelper empty l2 gas') ++ (treeDiffHelper empty r2 gas'))
      end 
    | Tr h1 l1 r1 =>
      match tr2 with 
      | empty => h1 :: ((treeDiffHelper l1 empty gas') ++ (treeDiffHelper r1 empty gas'))
      | Tr h2 l2 r2 => (treeDiffHelper l1 l2 gas') ++ (treeDiffHelper r1 r2 gas')
      end 
    end
  end.

Definition MAX_TREE_DEPTH : nat := 1000.

Definition treeDiff (tr1 tr2: ExecutionTree) : list TreeNode :=
  treeDiffHelper tr1 tr2 MAX_TREE_DEPTH.

(** This function is similar, but returns a list of all
    nodes in the second tree which don't appear in the first.
    We use our nodeEq function to ensure stricter equality. *)
Fixpoint treeDiffStrictHelper (tr1 tr2: ExecutionTree) (gas: nat) : list TreeNode :=
  match gas with 
  | O => nil 
  | S gas' =>
    match tr1 with
    | empty =>
      match tr2 with 
      | empty => nil
      | Tr h l r => h :: ((treeDiffStrictHelper tr1 l gas') ++ (treeDiffStrictHelper tr1 r gas'))
      end
    | Tr h1 l1 r1 =>
      match tr2 with
      | empty => h1 :: ((treeDiffStrictHelper l1 tr2 gas') ++ (treeDiffStrictHelper r1 tr2 gas'))
      | Tr h2 l2 r2 =>
        match (nodeEq h1 h2) with 
        | true => (treeDiffStrictHelper l1 l2 gas') ++ (treeDiffStrictHelper r1 r2 gas')
        | false => h2 :: (treeDiffStrictHelper l1 l2 gas') ++ (treeDiffStrictHelper r1 r2 gas')
        end
      end
    end
  end.

Definition treeDiffStrict (tr1 tr2: ExecutionTree) : list TreeNode :=
  treeDiffStrictHelper tr1 tr2 MAX_TREE_DEPTH.