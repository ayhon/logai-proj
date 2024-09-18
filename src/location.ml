type pos = pos_data Lazy.t
and pos_data =
  { fname      : string option (** File name for the position.       *)
  ; start_line : int (** Line number of the starting point.          *)
  ; start_col  : int (** Column number (utf8) of the starting point. *)
  ; end_line   : int (** Line number of the ending point.            *)
  ; end_col    : int (** Column number (utf8) of the ending point.   *) }

(** [to_string pos] transforms [pos] into a readable string. *)
let to_string : pos -> string = fun p ->
  let {fname; start_line; start_col; end_line; end_col} = Lazy.force p in
  let fname =
    match fname with
    | None    -> ""
    | Some(n) -> n ^ ", "
  in
  if start_line <> end_line then
    Printf.sprintf "%s%d:%d-%d:%d" fname start_line start_col end_line end_col
  else if start_col = end_col then
    Printf.sprintf "%s%d:%d" fname start_line start_col
  else
    Printf.sprintf "%s%d:%d-%d" fname start_line start_col end_col

(** [print oc pos] prints the optional position [pos] to [oc]. *)
let print : Format.formatter -> pos -> unit = fun ch p ->
  Format.pp_print_string ch (to_string p)
