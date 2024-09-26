module CDCL: Dpll.SOLVER = struct


  module LitSet = Set.Make(struct
    type t = Ast.lit
    let compare = compare
  end)

  (** A dependency graph identifies each literal
      with the set of literals that made it unit propagate.
      These are the elements of the clause that triggered it,
      minus the unassigned node itself. *)
  type graph = (Ast.Clause.t) array

  module LitMap = Map.Make(struct
    type t = Ast.lit
    let compare = compare
  end)
  type model = bool LitMap.t
  let get_assignment(lit: Ast.lit)(m: model): bool option =
    LitMap.find_opt (abs lit) m

  let rec collect: ('a option) list -> 'a list = function
    | [] -> []
    | (Some x)::xs -> x :: collect xs
    | None::xs -> collect xs

  let rec unit_propagation(f: Ast.Cnf.t)(m: model): model* ((Ast.lit * Ast.Clause.t) list) =
    (* TODO: Should also extend the implication graph.
       IDEA: Return also the literals which were assigned through
             unit propagation. *)
    let rec inner acc m =
      let unassigned_lit_and_deps clause =
        let unassigned_lits = clause
          |> Ast.Clause.filter  (fun lit -> get_assignment lit m == None)
          |> Ast.Clause.elements
        in
        match unassigned_lits with
        | [x] -> Some (x, Ast.Clause.remove x clause)
        | _ -> None
      in
      let literals_to_propagate = f
        |> Ast.Cnf.elements
        |> List.map unassigned_lit_and_deps
        |> collect
      in
      if List.is_empty literals_to_propagate then
        (m, acc)
      else
        literals_to_propagate
          |> List.map (fun (i,_) -> (abs i, if i > 0 then true else false))
          |> LitMap.of_list
          |> LitMap.union (fun _ _ _ ->
              failwith "We're supposed to be parsing unassinged literals. There can't be a conflict where this function is used."
            ) m
          |> inner (literals_to_propagate @ acc)
    in
    inner [] m

  let assignments(m: model)(f: Ast.Cnf.t): ((bool option) list) list =
    f |> Ast.Cnf.elements
      |> List.map (fun clause ->
          clause
            |> Ast.Clause.elements
            |> List.map (fun lit -> get_assignment lit m)
      )

  let satisfies_cnf(m: model)(f: Ast.Cnf.t): bool option =
    let satisfies_clause(m: model)(assignments: (bool option) list): bool option =
      if  List.exists (fun lit -> lit == Some true) assignments then
        Some true
      else if List.for_all (fun lit -> lit == Some false) assignments then
        Some false
      else
        None
    in
    let conjunctions = f
      |> assignments m
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
  let analyze_conflict(conflict: Ast.Clause.t)(m: model)(g: graph): LitSet.t =
    let rec get_minimal_node node =
      let neighbours = g.(node) in
      if LitSet.is_empty neighbours then
        LitSet.singleton node
      else
        LitSet.fold (fun neigh acc  ->
            get_minimal_node neigh
            |> LitSet.union acc
          )  neighbours LitSet.empty
    in
      Ast.Clause.fold (fun neigh acc ->
          get_minimal_node neigh
          |> LitSet.union acc
        ) conflict LitSet.empty

  (* Chooses an unassigned variable in [m] and assigns it a
     boolean value *)
  let decide(f: Ast.Cnf.t)(m: model): model =
    failwith "TODO"

  let cdcl(info: Ast.t): model option =
    (* IDEA: Instead of keeping a dl and dstack, can't we use
             the runtime's stack through recursion? If we don't
             mutate the model, but updated inmutably, we can
             simply store it in the stack.contents
             We would need to rethink how to implement the
             [analyze_conflict] step though.
       TODO: Decide whether it's worth it *)
    let inner_cdcl(f: Ast.Cnf.t)(m: model)(g: graph): model option =
      failwith "TODO"
    in
    let (m, lit_deps) = unit_propagation info.cnf LitMap.empty in
    let g: graph = Array.make info.nb_var Ast.Clause.empty  in
    let g = lit_deps
      |> List.fold_left (fun g (lit, deps) ->
        g.(abs lit) <- Ast.Clause.union deps g.(abs lit);
        g
      ) g
    in
    inner_cdcl info.cnf m g

  let solve(info: Ast.t): Ast.model option =
    let to_ast_model: model -> Ast.model =
      failwith "TODO"
    in
      cdcl info
        |> Option.map to_ast_model
end
