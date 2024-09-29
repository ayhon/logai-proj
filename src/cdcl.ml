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

  type model = LitSet.t
  let get_assignment(lit: Ast.lit)(m: model): bool option =
    LitSet.find_opt lit m
    |> Option.map (fun lit -> lit > 0)

  let rec collect: ('a option) list -> 'a list = function
    | [] -> []
    | (Some x)::xs -> x :: collect xs
    | None::xs -> collect xs

  let rec unit_propagation(f: Ast.Cnf.t)(m: model): model * ((Ast.lit * Ast.Clause.t) list) =
    (*  IDEA: Return also the literals which were assigned through
             unit propagation. *)
    let unassigned_lit_and_deps clause =
      let unassigned_lits = clause
        |> Ast.Clause.filter  (fun lit -> get_assignment lit m == None)
        |> Ast.Clause.elements
      in
      match unassigned_lits with
      | [x] -> Some (x, Ast.Clause.remove x clause)
      | _ -> None
    in
    let rec inner acc m =
      let literals_to_propagate = f
        |> Ast.Cnf.elements
        |> List.map unassigned_lit_and_deps
        |> collect
      in
      if List.is_empty literals_to_propagate then
        (m, acc)
      else
        literals_to_propagate
          |> List.map (fun (i,_) -> i)
          |> LitSet.of_list
          |> LitSet.union m
          |> inner (literals_to_propagate @ acc)
    in inner [] m

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
    let disjunctions = f
      |> assignments m
      |> List.map (satisfies_clause m)
    in
    if List.for_all (fun clause -> clause == Some true) disjunctions then
      Some true
    else if List.exists (fun clause -> clause == Some false) disjunctions then
      Some false
    else
      None

  (* Returns a conflict clause learned using implicatoin graph and
     a decision level upto which the solver needs to backtrack. *)
  let analyze_conflict(conflict: Ast.Clause.t)(m: model)(g: graph): LitSet.t =
    let rec get_minimal_node node =
      let neighbours = g.(node) in
      if Ast.Clause.is_empty neighbours then
        LitSet.singleton node
      else
        Ast.Clause.fold (fun neigh acc  ->
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
             mutate the model, but update it inmutably, we can
             simply store it in the stack.contents
             We would need to rethink how to implement the
             [analyze_conflict] step though.
       TODO: Decide whether it's worth it *)
    let rec inner_cdcl(f: Ast.Cnf.t)(m: model)(g: graph): model option =
      (* BACKTRACKING *)
      while satisfies_cnf m f == Some false do
        failwith "TODO"
      done;
      (* BOOLEAN DECISION *)
      if satisfies_cnf m f == None then
        failwith "TODO"
      else ();
      inner_cdcl f m g
    in
    let (m, lit_deps) = unit_propagation info.cnf LitSet.empty in
    let g: graph = Array.make info.nb_var Ast.Clause.empty  in
    lit_deps |> List.iter (fun (lit, deps) ->
        g.(abs lit) <- Ast.Clause.union deps g.(abs lit);
      );
    inner_cdcl info.cnf m g

  let solve(info: Ast.t): Ast.model option =
    cdcl info
      |> Option.map  LitSet.elements

end
