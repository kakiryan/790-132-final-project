From Coq Require Import Strings.String.
From Coq Require Import ZArith.Int.
(* TODO: Figure out how to use numbers *)
Import Z_as_Int.

(** We can treat a boolean expression as one object,
    if we wrap it inside this type. *)

(** TODO: 
    - Figure out how to use numbers
    - Finish booleval last case
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

Declare Custom Entry intlang.
Declare Scope intlang_scope.

Inductive intexp : Type :=
| IntLit (n : nat)
| IntAdd (n1 n2: intexp)
| IntSub (n1 n2: intexp)
| IntMult (n1 n2: intexp).
(* | IntId (x : string) *)

(* TODO: update function to also consider state *)
Fixpoint inteval (ie : intexp) : nat :=
  match ie with
  | IntLit n => n
  | IntAdd n1 n2 => (inteval n1) + (inteval n2)
  | IntSub n1 n2 => (inteval n1) - (inteval n2)
  | IntMult n1 n2 => (inteval n1) * (inteval n2)
  end.

Inductive boolexp : Type :=
  | BTrue
  | BFalse
  | Band (b1 : boolexp) (b2 : boolexp)
  | Bor (b1 : boolexp) (b2 : boolexp)
  | Bnot (b : boolexp)
  | Bge0 (n : intexp).

(** TODO: We want a path condition to be a list of conditions on
    symbolic variables, which isn't reflected here. *)
Inductive pathcond : Type :=
  | none
  | Pand (be : boolexp) (p : pathcond).

Fixpoint eval_boolexp (be : boolexp) : bool :=
  match be with
  | BTrue => true
  | BFalse => false
  | Band b1 b2 => (eval_boolexp b1) && (eval_boolexp b2)
  | Bor b1 b2 => (eval_boolexp b1) || (eval_boolexp b2)
  | Bnot b => negb (eval_boolexp b)
  | Bge0 n => true
  end.

Fixpoint eval_pathcond (p : pathcond) : bool :=
  match p with
  | none       => true
  | Pand be p' => (eval_boolexp be) && (eval_pathcond p')
  end.


  (** TODO: Defining the Integer language.
  - exlusively signed ints
  - simple assigns
  - if statements with then/else
  - go-to labels
  - way to get inputs (e.g. procedure parameters, global variables, read operations). 
  - arithmetic expr: +, -, x
  - bool expr: >= 0 only *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** TODO: Just brainstorming adding notes -- 3/23/21
  - function to visit  each variable in the value store associated with
 execution state and make symbolic
  - Inductive statement type? Starting below 
  - in Vol 3 ADT Chapter -- Table type would be good for name/symbol mappings.
 - *)

Inductive statement := 
  | assignment (x: string) (a: intexp) (* made up of a LHS loc and a RHS expr to evaluated*)
  | if_stmt (b: boolexp) (c1 c2: statement) (* evaluates to the boolexp defined above *)
  | go_to. (* how do we want to define functions? do we want to limit them to be just a name with 2 int params or someting?*)


Notation "'if' x 'then' y 'else' z 'end'" :=
         (if_stmt x y z). (*what level to put at ? *)

Notation "<{ e }>" := e (at level 0, e custom intlang at level 99) : com_scope.
Notation "( x )" := x (in custom intlang, x at level 99) : com_scope.
Notation "x" := x (in custom intlang at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom intlang at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (IntAdd x y)
  (in custom intlang at level 50, left associativity).
Notation "x - y" := (IntSub x y)
  (in custom intlang at level 50, left associativity).
Notation "x * y" := (IntMult x y)
  (in custom intlang at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom intlang at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom intlang at level 0).
Notation "x >= 0" := (Bge0 x) (in custom intlang at level 70, no associativity).
Notation "x && y" := (Band x y)
  (in custom intlang at level 80, left associativity).
Notation "x || y" := (Bor x y)
  (in custom intlang at level 80, left associativity).
Notation "'~' b"  := (Bnot b)
  (in custom intlang at level 75, right associativity).