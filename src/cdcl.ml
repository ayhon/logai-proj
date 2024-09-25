module CDCL: Dpll.SOLVER = struct

  module LitMap = Map.Make(struct
    type t = Ast.lit
    let compare = compare
  end)
  type model = bool LitMap.t
  let get_assignment(lit: Ast.lit)(m: model): bool option =
    LitMap.find_opt (abs lit) m

  let rec unit_propagation(f: Ast.Cnf.t)(m: model): model =
    (* TODO: Should also extend the implication graph *)
    let unassigned_lits clause = clause
      |> Ast.Clause.filter (fun lit ->
        m |> get_assignment lit
          |> Option.is_none
      )
      |> Ast.Clause.elements
    in
    let literals_to_propagate =  f
      |> Ast.Cnf.elements
      |> List.map unassigned_lits
      |> List.filter (fun literals -> List.length literals == 1)
      |> List.flatten
    in
    if List.is_empty literals_to_propagate then
      m
    else
      literals_to_propagate
        |> List.map (fun i -> (abs i, if i > 0 then true else false))
        |> LitMap.of_list
        |> LitMap.union (fun _ _ _ ->
            failwith "We're supposed to be parsing unassinged literals. There can't be a conflict where this function is used."
          ) m
        |> unit_propagation f

  let satisfies_clause(m: model)(clause: Ast.Clause.t): bool option =
    let assignments = clause
      |> Ast.Clause.elements
      |> List.map (fun lit ->
          get_assignment lit m
        )
    in
    if  List.exists (fun lit -> lit == Some true) assignments then
      Some true
    else if List.for_all (fun lit -> lit == Some false) assignments then
      Some false
    else
      None

  let satisfies_cnf(m: model)(f: Ast.Cnf.t): bool option =
    let conjunctions = f
      |> Ast.Cnf.elements
      |> List.map (satisfies_clause m)
    in
    if  List.exists (fun clause -> clause == Some true) conjunctions then
      Some true
    else if List.for_all (fun clause -> clause == Some false) conjunctions then
      Some false
    else
      None

  (* Returns a conflict clause learned using implicatoin graph and
     a decision level upto which the solver needs to backtrack. *)
  let analyze_conflict(f: Ast.Cnf.t)(m: model): Ast.Cnf.t * int =
    failwith "TODO"

  (* Chooses an unassigned variable in [m] and assigns it a
     boolean value *)
  let decide(f: Ast.Cnf.t)(m: model): model =
    failwith "TODO"

  let cdcl(f: Ast.Cnf.t)(m: model): model option =
    (* IDEA: Instead of keeping a dl and dstack, can't we use
             the runtime's stack through recursion? If we don't
             mutate the model, but updated inmutably, we can
             simply store it in the stack.contents
             We would need to rethink how to implement the
             [analyze_conflict] step though
       TODO: Decide whether it's worth it *)
    let inner_cdcl(f: Ast.Cnf.t)(m: model): model option =
      failwith "TODO"
    in
    failwith "TODO"

  let solve(info: Ast.t): Ast.model option =
    let to_ast_model: model -> Ast.model =
      failwith "TODO"
    in
      cdcl info.cnf (LitMap.empty)
        |> Option.map to_ast_model
end
