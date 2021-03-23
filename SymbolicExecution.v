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

