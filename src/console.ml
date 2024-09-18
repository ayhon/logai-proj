(** Format transformers (colors). *)
let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m%!"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

(** Type of logging function data. *)
type logger_data =
  { logger_key     : char     (** Character used to unable the logger.      *)
  ; logger_name    : string   (** 4 character name used as prefix in logs.  *)
  ; logger_desc    : string   (** Description of the log displayed in help. *)
  ; logger_enabled : bool ref (** Is the log enabled? *) }

(** [log_enabled] is set to true when logging functions may print messages. *)
let log_enabled : bool ref = ref false

(** [loggers] constains the registered logging functions. *)
let loggers : logger_data list ref = ref []

(** [log_summary ()] returns descriptions for logging options. *)
let log_summary : unit -> string list = fun () ->
  let fn data = Format.sprintf "%c : %s" data.logger_key data.logger_desc in
  List.sort String.compare (List.map fn !loggers)

(** [set_log value key] enables or disables the loggers corresponding to every
    character of [str] according to [value]. *)
let set_debug : bool -> string -> unit = fun value str ->
  let fn {logger_key; logger_enabled; _} =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn !loggers;
  let is_enabled data = !(data.logger_enabled) in
  log_enabled := List.exists is_enabled !loggers

(** Exception raised in case of failure. *)
exception Fatal of Location.pos option * string

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

let fatal : Location.pos option -> ('a,'b) koutfmt -> 'a = fun pos fmt ->
  let cont _ = raise (Fatal(pos, Format.flush_str_formatter ())) in
  Format.kfprintf cont Format.str_formatter fmt

(** [exit_with fmt] is similar to [fatal_no_pos fmt], but the whole program is
    (irrecoverably) stopped with return code [1], indicating failure. *)
let exit_with : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (red (fmt ^^ "\n%!"))
