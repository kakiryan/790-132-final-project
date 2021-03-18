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