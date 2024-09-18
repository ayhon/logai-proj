type t
type env

(** [read str] reads a string encoding a sudoku. Returns a sudoku and its solution. *)
val read : string -> t * t

(** [to_cnf t] encodes a sudoku and returns an environement as long as a cnf problem *)
val to_cnf : t -> env * Ast.t

(** [solution_of env m] takes an environement [env] and a model [m] and returns the solution of a sudoku *)
val solution_of : env -> Ast.model -> t

type 'a printer = Format.formatter -> 'a -> unit

(** [pp sudoku] is a pretty printer for a sudoku *)
val pp : t printer
