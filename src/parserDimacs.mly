%{
    let mk_clause : int list -> Ast.Clause.t = fun ls -> Ast.Clause.of_list ls

    let mk_cnf : int * int -> Ast.Clause.t list -> Ast.t = fun (nb_var,nb_clause) cls ->
      let open Ast in
      {nb_var; nb_clause; cnf = Cnf.of_list cls}
%}

%token EOF
%token ZERO
%token P CNF
%token NEWLINE
%token <int> INT


/* Starting symbols */

%start <Ast.t> file

%%

file:
  | NEWLINE* h=start l=cnf
    { mk_cnf h l }

start:
  | P CNF nbvar=INT nbclause=INT NEWLINE
    { (nbvar, nbclause) }

cnf:
  | EOF
    { [] }
  | NEWLINE l=cnf
    { l }
  | c=clause l=cnf
    { c :: l }

clause:
  | c=nonempty_list(atom) ZERO NEWLINE
    { mk_clause c }

atom:
  | i=INT
    { i }
