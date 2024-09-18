(** Type of variables in cnf formulas. *)
type var = int

(** We use the same type for litterals except we use negatives values. *)
type lit = int

(** Contains litterals that satisfy a cnf formula as returned by a SAT solver. *)
type model = int list

(** A set of variables *)
module Clause : Set.S with type elt = var

(** A set of clauses *)
module Cnf : Set.S with type elt = Clause.t

(** A cnf problem *)
type t =
  {
    nb_var : int; (** number of variables *)
    nb_clause : int; (** number of clauses *)
    cnf : Cnf.t (** the cnf formula *)
  }

(** [neg v] returns the opposite litteral *)
val neg : lit -> lit

type 'a printer = Format.formatter -> 'a -> unit

(** [pp_clause fmt cl] prints a clause *)
val pp_clause : Clause.t printer

(** [pp_cnf fmt cnf] prints a cnf *)
val pp_cnf : Cnf.t printer

(** [pp fmt ast] prints an ast (problem) *)
val pp : t printer
