(** Signature module to choose a variable on which the DPLL algorithm will branch. *)
module type CHOICE = sig
  val choice : Ast.Cnf.t -> Ast.var
end

(** Signature for a SAT solver. *)
module type SOLVER = sig

  (** solve takes a cnf formula and returns either None if it is unsatisfiable or
      a model that satisfies the formula. *)
  val solve : Ast.t -> Ast.model option

end

(** DPLL is a SAT solver parameterized by a choice function. *)
module DPLL(C:CHOICE) : SOLVER

(** Implement a choice by Default. More choices can be implemented. *)
module DefaultChoice : CHOICE
