(** We can treat a boolean expression as one object,
    if we wrap it inside this type. *)
Inductive boolexp : Type :=
  | B (b : bool)
  | Band (b1 : bool) (b2 : bool)
  | Bor (b1 : bool) (b2 : bool)
  | Bnot (b : bool).

(** TODO: We want a path condition to be a list of conditions on
    symbolic variables, which isn't reflected here. *)
Inductive pathcond : Type :=
  | none
  | Pand (be : boolexp) (p : pathcond).

Definition evaluate_boolexp (be : boolexp) : bool :=
  match be with
  | B b => b
  | Band b1 b2 => b1 && b2
  | Bor b1 b2 => b1 || b2
  | Bnot b => negb b
  end.

Fixpoint evaluate_pathcond (p : pathcond) : bool :=
  match p with
  | none       => true
  | Pand be p' => (evaluate_boolexp be) && (evaluate_pathcond p')
  end.