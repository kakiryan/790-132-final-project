From Coq Require Import Strings.String.
(** We can treat a boolean expression as one object,
    if we wrap it inside this type. *)
Inductive boolexp : Type :=
  | B (b : bool)
  | Band (b1 : boolexp) (b2 : boolexp)
  | Bor (b1 : boolexp) (b2 : boolexp)
  | Bnot (b : boolexp).

(** TODO: We want a path condition to be a list of conditions on
    symbolic variables, which isn't reflected here. *)
Inductive pathcond : Type :=
  | none
  | Pand (be : boolexp) (p : pathcond).

Fixpoint eval_boolexp (be : boolexp) : bool :=
  match be with
  | B b => b
  | Band b1 b2 => (eval_boolexp b1) && (eval_boolexp b2)
  | Bor b1 b2 => (eval_boolexp b1) || (eval_boolexp b2)
  | Bnot b => negb (eval_boolexp b)
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


Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Inductive Int :=
  | Zero : Int
  | Positive: nat -> Int
  | Negative: nat  -> Int.

Check Negative 4.
Check Positive 2.
Check O.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive intexp : Type :=
| IntAdd (n1 n2: Int)
| IntSub (n1 n2: Int)
| IntMult (n1 n2: Int)
| IntId (x : string).



Definition Int_plus (n1 n2: Int) : Int :=
 match n1, n2 with
 | Positive n1, Positive n2 => Positive (n1 + n2)
 | Positive n1, Negative n2 => if n2 <=? n1 then Positive (n1 - n2) else Negative (n2 - n1)
 | Negative n1, Positive n2 => if n1 <=? n2 then Positive (n2 - n1) else Negative (n1 - n2)
 | Negative n1, Negative n2 => Negative (n1 + n2)
 | Zero, x => x
 | x, Zero => x
end.

Check Int_plus (Negative 2) (Positive 4).
Compute Int_plus (Negative 2) (Positive 4).
Compute Int_plus (Negative 6) (Positive 4).
Compute Int_plus Zero Zero.
Compute Int_plus (Negative 5) Zero.


(* this may not be quite right *) 
Definition Int_minus (n1 n2: Int) : Int :=
 match n1, n2 with
 | Positive n1, Positive n2 => Positive (n1 - n2)
 | Positive n1, Negative n2 => if n2 <=? n1 then Positive (n1 + n2) else Negative (n2 + n1)
 | Negative n1, Positive n2 => if n1 <=? n2 then Negative (n2 + n1) else Negative (n1 + n2)
 | Negative n1, Negative n2 => Negative (n1 - n2)
 | Zero, Positive n2 => Negative n2
 | Zero, Negative n2 => Positive n2
 | x, Zero => x
end.

Check Int_minus (Negative 2) (Positive 4).
Compute Int_minus (Negative 2) (Positive 4).
Compute Int_minus (Negative 6) (Positive 4).
Compute Int_minus Zero (Positive 2).
Compute Int_minus (Negative 5)  (Negative 5).

Definition Int_mult (n1 n2: Int) : Int :=
 match n1, n2 with
 | Positive n1, Positive n2 => Positive (n1 * n2)
 | Positive n1, Negative n2 => Negative (n1 * n2)
 | Negative n1, Positive n2 => Negative (n1 * n2)
 | Negative n1, Negative n2 => Positive (n1 * n2)
 | Zero, x => Zero
 | x, Zero => Zero
end.

Check Int_mult (Negative 2) (Positive 4).
Compute Int_mult (Negative 2) (Positive 4).
Compute Int_mult (Negative 6) (Positive 4).
Compute Int_mult Zero (Positive 2).
Compute Int_mult (Negative 5)  (Negative 5).

Definition inteval (a: intexp) : Int :=
 match a with
  | IntAdd n1 n2 => Int_plus n1 n2
  | IntSub n1 n2 => Int_minus n1 n2
  | IntMult n1 n2 => Int_mult n1 n2
  | IntId x => Positive 2 (* Lol this is arbitrary so it will compile. 
need to do something like the textbook does with states probably *)
end.

(* the only condition supported by lang is checking its >= 0 *)
Definition Int_non_neg (n1 : Int) : boolexp :=
 match n1 with
 | Positive n1 => B (true)
 | Zero => B (true)
 | Negative n1 => B (false)
end.

Check Int_non_neg (Positive 3).
Compute Int_non_neg (Positive 3).
Compute Int_non_neg (Zero).
Compute Int_non_neg (Negative 3).

(** TODO: Just brainstorming adding notes -- 3/23/21
  - function to visit  each variable in the value store associated with
 execution state and make symbolic
  - Inductive statement type? Starting below 
  - in Vol 3 ADT Chapter -- Table type would be good for name/symbol mappings.
 - *)

Inductive statement := 
  | assignment (x: string) (a: intexp) (* made up of a LHS loc and a RHS expr to evaluated*)
  | if_stmt (b: boolexp) (c1 c2: statement) (* evaluates to the boolexp defined above *)
  | go_to. (* how do we ant to define functions? do we want to limit them to be just a name with 2 int params or someting?*)


Notation "'if' x 'then' y 'else' z 'end'" :=
         (if_stmt x y z). (*what level to put at ? *)
