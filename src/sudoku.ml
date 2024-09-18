type t = int list

type env = int
let size = 9
let root = int_of_float (sqrt (float_of_int size))

type 'a printer = Format.formatter -> 'a -> unit

let pp : 'a printer = fun fmt sudoku ->
  for i = 0 to (size -1) do
    if i mod root = 0 && i <> 0 then
      Format.fprintf fmt "@.";
    for j = 0 to (size -1) do
      if j mod root = 0 && j <> 0 then
        Format.fprintf fmt " ";
      Format.fprintf fmt "%d " (List.nth sudoku (i*size + j))
    done;
    Format.fprintf fmt "@.";
  done

(*
Internal representation of literals
-----------------------------------

(1,9)     | (10,18)   | (19,27)   || (28,36)   | (37,45)   | (46,54)   || (55,63)   | (64,72)   | (73,81)
(82,90)   | (91,99)   | (100,108) || (109,117) | (118,126) | (127,135) || (136,144) | (145,153) | (154,162)
(163,171) | (172,180) | (181,189) || (190,198) | (199,207) | (208,216) || (217,225) | (226,234) | (235,243)
==================================++===================================++==================================
(244,252) | (253,261) | (262,270) || (271,279) | (280,288) | (289,297) || (298,306) | (307,315) | (316,324)
(325,333) | (334,342) | (343,351) || (352,360) | (361,369) | (370,378) || (379,387) | (388,396) | (397,405)
(406,414) | (415,423) | (424,432) || (433,441) | (442,450) | (451,459) || (460,468) | (469,477) | (478,486)
==================================++===================================++==================================
(487,495) | (496,504) | (505,513) || (514,522) | (523,531) | (532,540) || (541,549) | (550,558) | (559,567)
(568,576) | (577,585) | (586,594) || (595,603) | (604,612) | (613,621) || (622,630) | (631,639) | (640,648)
(649,657) | (658,666) | (667,675) || (676,684) | (685,693) | (694,702) || (703,711) | (712,720) | (721,729)
*)

let init ?(start = 1) ?(step = 1) x =
  List.init x (fun x -> step * x + start)

let at_least_value: Ast.Clause.t list =
  List.map (fun x -> Ast.Clause.of_list (init ~start:x 9)) (init ~step:9 81)

let at_most_value: Ast.Clause.t list =
  let two_choose start =
    List.filter (fun (x, y) -> x < y)
      (List.concat_map (fun x -> List.combine (init ~step:0 ~start:x 9) (init ~start 9)) (init ~start 9)) in

  List.map (fun (x, y) -> Ast.Clause.of_list [-x; -y]) (List.concat_map two_choose (init ~step:9 81))

let rows: Ast.Clause.t list =
  List.concat_map (fun x -> List.map (fun x -> Ast.Clause.of_list (init ~start:x ~step:9 9)) (init ~start:x 9)) (init ~step:81 9)

let cols: Ast.Clause.t list =
  List.map (fun x -> Ast.Clause.of_list (init ~start:x ~step:81 9)) (init 81)

let block: Ast.Clause.t list =
  let block_idx left_corner = Ast.Clause.of_list (List.concat_map (fun x -> init ~start:x ~step:81 3) (init ~step:9 ~start:left_corner 3)) in
  List.concat_map (fun x -> List.map block_idx (init ~start:x 9)) [1; 28; 55; 244; 271; 298; 487; 514; 541]

let clues (sudoku: (int * int) list): Ast.Clause.t list =
  List.map (fun (i, x) -> Ast.Clause.singleton (i * 9 + x)) sudoku

let to_cnf : t -> env * Ast.t = fun sudoku ->
  let sudoku = List.filter (fun (_, x) -> x <> 0) (List.mapi (fun i x -> (i, x)) sudoku) in
  let cnf = Ast.Cnf.of_list (at_least_value @ at_most_value @ rows @ cols @ block @ clues sudoku) in
  let ast = {Ast.nb_var = 729; Ast.nb_clause = 3240 + List.length sudoku; Ast.cnf = cnf} in
  (0, ast)

let solution_of : env -> Ast.model -> t = fun env model ->
  List.map (fun x -> if x mod 9 == 0 then 9 else x mod 9) (List.sort (-) (List.filter (fun x -> x > 0) model))

let grid_of_str : string -> t = fun str ->
  let l = ref [] in
  String.iter (fun c -> l := (int_of_char c - (int_of_char '0'))::!l) str;
  List.rev !l

let read : string -> t * t = fun str ->
  match String.split_on_char ',' str with
  | [left;right] -> grid_of_str left, grid_of_str right
  | _ -> assert false
