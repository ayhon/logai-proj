type var = int

type lit = int

type model = int list

module Clause = Set.Make(
  struct type t = lit

    let compare x y =
      if abs x == abs y then (compare y x)
      else if abs x > abs y then 1 else -1
  end)

module Cnf = Set.Make(struct type t = Clause.t let compare = Clause.compare end)

type t = {
  nb_var: int;
  nb_clause: int;
  cnf: Cnf.t
}

let neg var = -var

type 'a printer = Format.formatter -> 'a -> unit

let pp_clause : Clause.t printer = fun fmt clause ->
  Clause.iter (fun v -> Format.fprintf fmt "%d " v) clause

let pp_cnf : Cnf.t printer = fun fmt cnf ->
  Cnf.iter (fun clause -> Format.fprintf fmt "%a0@." pp_clause clause) cnf

let pp : t printer = fun fmt t ->
  Format.fprintf fmt "p %d %d@." t.nb_var t.nb_clause;
  Format.fprintf fmt "%a@." pp_cnf t.cnf
