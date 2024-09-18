module type CHOICE = sig
  val choice : Ast.Cnf.t -> Ast.var
end

module DefaultChoice =
struct
  let choice : Ast.Cnf.t -> Ast.var = fun cnf -> failwith "todo: choice"
end

module type SOLVER = sig
  val solve : Ast.t -> Ast.model option
end

module DPLL(C:CHOICE) : SOLVER =
struct
  module LitSet = Set.Make(struct type t = int let compare = compare end)

  type instance = {
    ast: Ast.t;
    assignment: Ast.model;
    unbound: LitSet.t
  }

  let assign_literal (instance: instance) (literal: Ast.var): instance =
    (* Construct a new CNF without the literal *)
    let cnf =
      let assign_clause (clause: Ast.Clause.t) (cnf: Ast.Cnf.t) =
        if Ast.Clause.mem literal clause then cnf
        else Ast.Cnf.add (Ast.Clause.remove (Ast.neg literal) clause) cnf
      in Ast.Cnf.fold assign_clause instance.ast.cnf Ast.Cnf.empty in
    { ast = { instance.ast with cnf };
      assignment = literal :: instance.assignment;
      unbound = LitSet.remove (abs literal) instance.unbound }

  let rec unit_propagate (instance: instance): Ast.model =
    let unit_clause = Ast.Clause.fold (fun x y -> x :: y)
    in Ast.Cnf.fold unit_clause (Ast.Cnf.filter (fun clause -> (Ast.Clause.cardinal clause) == 1) instance.ast.cnf) []

  let pure_literal (instance: instance): Ast.model =
    let rec filter_pure_literal list =
      match list with
      | x :: y :: xs -> if x == -y then filter_pure_literal xs else x :: filter_pure_literal (y :: xs)
      | _ -> list
    in filter_pure_literal (Ast.Clause.elements (Ast.Cnf.fold Ast.Clause.union instance.ast.cnf Ast.Clause.empty))

  let rec simplify (instance: instance): instance =
    (* Check if there is a unit clause in formula or pure: Unit Propagation *)
    match unit_propagate instance with
    | [] -> begin
        (* Check if there is a literal that occurs pure in formula *)
        match pure_literal instance with
        | [] -> instance
        | literals -> simplify (List.fold_left assign_literal instance (pure_literal instance))
      end
    | literals -> simplify (List.fold_left assign_literal instance literals)

  let rec solve_sat (instance: instance): Ast.model option =
    (* Simplify formula *)
    let instance = simplify instance in

    (* Check if the formula is empty: SAT *)
    if Ast.Cnf.is_empty instance.ast.cnf then Some instance.assignment else

    (* Check if the formula contains an empty clause: UNSAT *)
    if Ast.Cnf.exists Ast.Clause.is_empty instance.ast.cnf then None else

    (* Choose a literal *)
    let literal = LitSet.choose instance.unbound in

    (* Call recursively the algorithm *)
    match solve_sat (assign_literal instance (Ast.neg literal)) with
    | Some list -> Some list
    | None -> solve_sat (assign_literal instance literal)

  let solve (f: Ast.t): Ast.model option =
    let range = List.init f.nb_var (fun x -> x + 1) in
    let unbound_vars = List.fold_left (fun set x -> LitSet.add x set) LitSet.empty range in
    solve_sat { ast = f; assignment = []; unbound = unbound_vars }
end
