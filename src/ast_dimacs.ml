module Location =
struct
  type t = {
    file : string;
    start_line : int;
    start_column : int;
    stop_line : int;
    stop_column : int;
  }

let mk file start_line start_column stop_line stop_column =
  { file; start_line; start_column; stop_line; stop_column; }

let mk_pos start stop =
  let open Lexing in
  mk
    start.pos_fname
    start.pos_lnum (start.pos_cnum - start.pos_bol)
    stop.pos_lnum (stop.pos_cnum - stop.pos_bol)
end

module Statement =
struct

  type t = Header of int * int | Clause of Cnf.Ast.Clause.t

  (** Header of a dimacs file. First argument is the number of variables,
      second is the number of clauses. *)
  let p_cnf : ?loc:Location.t -> int -> int -> t = fun ?loc:_ n_var n_clause ->
    Header(n_var,n_clause)

  (** Make a clause from a list of literals. *)
  let clause : ?loc:Location.t -> int list -> t = fun ?loc:_ ls ->
    Clause (Cnf.Ast.Clause.of_list ls)

end
