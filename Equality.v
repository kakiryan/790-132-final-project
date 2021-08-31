From Coq Require Import Strings.String.
From SE Require Export Model.

(** Checks whether two symbolic expressions are equal.
    As of right now, does not worry about manipulations
    by commutativity, associativity, or the like. *)
Fixpoint symbolicExpEq (se1 se2: SymbolicExp) : bool :=
  match se1 with 
  | Symbol str1 =>
    match se2 with
    | Symbol str2 => (String.eqb str1 str2)
    | _ => false 
    end
  | SymAdd se1_l se1_r =>
    match se2 with 
    | SymAdd se2_l se2_r => andb (symbolicExpEq se1_l se2_l) (symbolicExpEq se1_r se2_r)
    | _ => false
    end
  | SymSub se1_l se1_r =>
    match se2 with 
    | SymSub se2_l se2_r => andb (symbolicExpEq se1_l se2_l) (symbolicExpEq se1_r se2_r)
    | _ => false 
    end
  | SymMult se1_l se1_r =>
    match se2 with 
    | SymMult se2_l se2_r => andb (symbolicExpEq se1_l se2_l) (symbolicExpEq se1_r se2_r)
    | _ => false 
    end
  | Constant n1 =>
    match se2 with 
    | Constant n2 => true 
    | _ => false 
    end
  end.

(** Checks whether two symbolic boolean expressions
    are equal. As above, we don't consider any logical
    manipulations of the same boolean function as equivalent. *)
Fixpoint SBoolExpEq (sbe1 sbe2: SBoolExp) : bool :=
  match sbe1 with
  | SBTrue =>
    match sbe2 with 
    | SBTrue => true 
    | _ => false 
    end 
  | SBFalse =>
    match sbe2 with 
    | SBFalse => true 
    | _ => false 
    end
  | SBnot sbe1p =>
    match sbe2 with 
    | SBnot sbe2p => SBoolExpEq sbe1p sbe2p
    | _ => false 
    end
  | SBge0 se1 => match sbe2 with 
    | SBge0 se2 => symbolicExpEq se1 se2
    | _ => false
    end
  end.

Fixpoint listEq {A: Type} (eq: A -> A -> bool) (list1 list2: list A) : bool :=
  match (Nat.eqb (List.length list1) (List.length list2)) with 
  | true =>
    match list1 with 
    | nil =>
      match list2 with 
      | nil => true 
      | _   => false
      end 
    | h1 :: t1 => match list2 with 
      | nil => false 
      | h2 :: t2 => andb (eq h1 h2) (listEq eq t1 t2)
      end
    end
  | false => false
  end.

Definition oneMapEq (x y: (string * SymbolicExp)) : bool :=
  match x with 
  | (s1, se1) =>
  match y with 
  | (s2, se2) =>
  andb (String.eqb s1 s2) (symbolicExpEq se1 se2)
  end 
  end.

Definition stateEq (st1 st2: state) : bool :=
  listEq oneMapEq st1 st2.

Definition pcEq (pc1 pc2: PathCond) : bool := 
  listEq SBoolExpEq pc1 pc2.

(** Building on everything else in this file, this function tests
    whether two nodes are equal. This definition of equality will
    treat the node's state and path condition as sets of individual
    mappings and boolean expressions, respectively. But we only check
    equality naively on expressions, not worrying about rearrangements
    of equivalent statements. In practice this isn't a problem, as
    we mostly will be comparing nodes within one symbolic execution
    tree. *)
Definition nodeEq (node1 node2: TreeNode) : bool :=
  match node1 with 
  | << st1, pc1, i1 >> =>
  match node2 with 
  | << st2, pc2, i2 >> =>
  andb (stateEq st1 st2) (andb (pcEq pc1 pc2) (Nat.eqb i1 i2))
  end 
end.