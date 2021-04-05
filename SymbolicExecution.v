From Coq Require Import Strings.String.
Require Import ZArith.
Open Scope Z_scope.
From LF Require Import Maps.

Compute 1 + -2.

(** TODO: 
    - Figure out how to use numbers (done)
    - Finish booleval last case (done)
    - Include program state (potentially with Table from ADT chapter)
      + Update eval functions to consider state
      + Update evals with new notation
    - Make a representation of the symbolic execution tree
    - Make a program eval function (only with if/else, not loops/goto)
      + Make a symbolic version:
        * Takes in program, state, symbolic execution tree, and path condition
        * For each instruction type, update these in a different way
        * State maps variable names to expressions
    - Make notation for new concepts
*)

Declare Custom Entry com.
Declare Scope com_scope.

Inductive IntExp : Type :=
| IntLit (n : Z)
| IntAdd (n1 n2: IntExp)
| IntSub (n1 n2: IntExp)
| IntMult (n1 n2: IntExp)
| IntId (x : string).


Definition state := total_map IntExp.

Inductive BoolExp : Type :=
  | BTrue
  | BFalse
  | Band (b1 : BoolExp) (b2 : BoolExp)
  | Bor (b1 : BoolExp) (b2 : BoolExp)
  | Bnot (b : BoolExp)
  | Bge0 (n : IntExp).


Inductive Statement := 
  | Assignment (x: string) (a: IntExp) (* made up of a LHS loc and a RHS expr to evaluated*)
  | Seq (c1 c2: Statement)
  | If_Stmt (b: BoolExp) (c1 c2: Statement) (* evaluates to the BoolExp defined above *)
  | Go_To. (* how do we want to define functions? do we want to limit them to be just a name with 2 int params or someting?*)

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
Notation "'if' x 'then' y 'else' z 'end'" :=
         (If_Stmt x y z)  (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "x ; y" :=
         (Seq x y)
           (in custom com at level 90, right associativity) : com_scope.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).


Open Scope com_scope. 

Check <{1 + 1}>.

Fixpoint inteval (s : state) (ie : IntExp) : IntExp :=
  match ie with
  | IntLit n => IntLit n
  | <{n1 + n2}> =>  <{(inteval s n1) + (inteval s n2)}>
  | <{n1 - n2}> => <{(inteval s n1) - (inteval s n2)}>
  | <{n1 * n2}> =>  <{(inteval s n1) * (inteval s n2)}>
  | IntId n => s n
  end.

Definition a := IntId "a".
Definition b := IntId "b".
Definition c := IntAdd a b.
Definition examplemap := (t_update (t_empty (IntLit 1)) "a" c).
Compute examplemap "a".

Inductive program_eval : Statement -> state -> state -> Prop :=
 | E_Assign: forall st a n x,
    (inteval st a) = n ->
    st =[ x := a]=> (x !-> n ; st)
 | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''

where "st =[ c ]=> st'" := (program_eval c st st').

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example eval_example:
  empty_st =[
     X := 2;
     Z := 4
  ]=> (X !-> 2 ; Z !-> 4).
Proof.
   apply E_Seq with (X !-> 2).
   - Abort.

(** TODO: We want a path condition to be a list of conditions on
    symbolic variables, which isn't reflected here. *)
Inductive Pathcond : Type :=
  | none
  | Pand (be : BoolExp) (p : Pathcond).

(* Fixpoint eval_BoolExp (s: state) (be : BoolExp) : bool :=
  match be with
  | BTrue => true
  | BFalse => false
  | Band b1 b2 => (eval_BoolExp b1) && (eval_BoolExp b2)
  | Bor b1 b2 => (eval_BoolExp b1) || (eval_BoolExp b2)
  | Bnot b => negb (eval_BoolExp b)
  | Bge0 n => Z.leb 0 (inteval s n)
  end.

Fixpoint eval_pathcond (p : pathcond) : bool :=
  match p with
  | none       => true
  | Pand be p' => (eval_BoolExp be) && (eval_pathcond p')
  end.
*)


  (** TODO: Defining the Integer language.
  - exlusively signed ints
  - simple assigns
  - if Statements with then/else
  - go-to labels
  - way to get inputs (e.g. procedure parameters, global variables, read operations). 
  - arithmetic expr: +, -, x
  - bool expr: >= 0 only *)

(** TODO: Just brainstorming adding notes -- 3/23/21
  - function to visit  each variable in the value store associated with
 execution state and make symbolic
  - Inductive Statement type? Starting below 
  - in Vol 3 ADT Chapter -- Table type would be good for name/symbol mappings.
 - *)

