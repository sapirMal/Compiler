#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception DEBUG;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
  
(*   
  val extract_bindings_vars : sexpr -> sexpr -> sexpr
  val extract_bindings_vals : sexpr -> sexpr -> sexpr
  val create_whatever_bindings : sexpr -> sexpr
  val create_set_bindings : sexpr -> sexpr -> sexpr
  val tag_parse : sexpr  -> expr  *)
 

end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let rec extract_bindings_vars bindings vars =
match bindings with 
| Pair(Pair(Symbol(var),value),cdr) ->
    Pair(Symbol(var), extract_bindings_vars cdr vars)
| Nil -> vars
| _ -> raise X_syntax_error;;

let rec extract_bindings_vals bindings vals =
match bindings with  
| Pair(Pair(var,Pair(value,Nil)),cdr) ->
    Pair(value, extract_bindings_vals cdr vals)
| Nil -> vals
| _ -> raise X_syntax_error;;

let rec create_whatever_bindings bindings  =
match bindings with
 | Pair(Pair(Symbol(var),value),cdr) ->
    Pair(Pair(Symbol(var), Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)) ,create_whatever_bindings cdr)
 | Nil -> Nil
 | _ -> raise X_syntax_error;;

let rec create_set_bindings bindings set_bindings = 
match bindings with
  | Pair(Pair(Symbol(var),Pair(value, Nil)),cdr) ->
    Pair(Pair(Symbol "set!", Pair(Symbol(var), Pair(value, Nil))), create_set_bindings cdr set_bindings)
  | Nil -> set_bindings
  | _ -> raise X_syntax_error;;
    
let rec symbol_pair_to_list pair list =
match pair with
  | Nil -> (list, "", true)
  | Symbol(x) -> 
        if (List.mem x list)
        then raise X_syntax_error (* duplicate param *)
        else (list, x, false)
  | Pair(car,cdr)->(
        (match car with
          | Symbol(x) ->
            if (List.mem x list)
            then raise X_syntax_error (* duplicate param *)
            else 
            (let list = (List.append list [x]) in
              (symbol_pair_to_list cdr list))
          | _ -> raise X_syntax_error (* invalid param, not var *)))
  |_ -> raise X_syntax_error;;
      
let rec tag_parse_sexpr_pair_to_list pair list =
match pair with
  | Nil -> []
  | Pair(car ,Nil) -> list @ [(tag_parse car)]
  | Pair(car ,cdr) -> 
    let list = list @ [(tag_parse car)] in
    (tag_parse_sexpr_pair_to_list cdr list)
  | _ -> raise X_syntax_error
      

and tag_parse sexpr = 

match sexpr with
(* const *)
| Bool(x) -> Const(Sexpr(sexpr))
| Number(x) -> Const(Sexpr(sexpr))
| Char(x) -> Const(Sexpr(sexpr))
| String(x) -> Const(Sexpr(sexpr))
| Nil -> Const(Sexpr(sexpr))
| Pair(Symbol "quote", Pair(x, Nil)) -> Const(Sexpr(x))
| Pair(Symbol "unquote", Pair(x, Nil)) -> Const(Sexpr(x))
| TaggedSexpr (name, Pair (Symbol "quote", Pair (x, Nil))) 
      -> Const (Sexpr(TaggedSexpr (name,x)))
| TaggedSexpr (name, x)
      -> Const (Sexpr(sexpr))
| TagRef(x) -> Const(Sexpr(sexpr))

(* if *)
| Pair(Symbol "if", Pair(test, Pair(dit, Pair(dif, Nil)))) 
      -> If(tag_parse test, tag_parse dit, tag_parse dif)
| Pair(Symbol "if", Pair(test, Pair(dit, Nil))) 
      -> If(tag_parse test, tag_parse dit, Const(Void))

(* lambda *)
| Pair(Symbol "lambda", Pair(arglist, body))  
      -> (match body with
      | Nil -> raise X_syntax_error (* not expr+ in body *)
      | _ ->  let (arglist, optarg, simple) = (symbol_pair_to_list arglist []) in
              if (simple) 
              then LambdaSimple (arglist ,tag_parse (Pair(Symbol "begin",body)))
              else LambdaOpt (arglist, optarg, tag_parse (Pair(Symbol "begin",body))))

(* or *)
| Pair(Symbol "or", rands) 
        -> (match rands with
        | Nil -> tag_parse(Bool(false))
        | Pair(car,Nil) -> tag_parse(car)
        | Pair(car,cdr) -> Or (tag_parse_sexpr_pair_to_list rands [])
        | _ -> raise X_syntax_error)



(* define *)

| Pair(Symbol "define", Pair(Symbol(var), Pair (value,Nil))) 
        -> 
        let var = tag_parse (Symbol(var)) in
        (match var with
        | Var(x) -> Def (var, (tag_parse value))
        | _ -> raise X_syntax_error)    

(* define-MIT *)
| Pair(Symbol "define", Pair(Pair(var, argl), expr)) ->  
      tag_parse (Pair(Symbol "define", Pair(var, Pair(Pair(Symbol "lambda", Pair(argl, expr)),Nil))))


(* set! *)
| Pair(Symbol "set!", Pair(var, Pair (value,Nil))) 
        -> 
        let var = tag_parse var in
        (match var with
        | Var(x) -> Set (var, (tag_parse value))
        | _ -> raise X_syntax_error)    

(* begin *)
| Pair(Symbol "begin", body)
        ->
        (match body with
        | Nil -> Const(Void)
        | Pair(car, Nil) -> tag_parse car
        | _  -> Seq(tag_parse_sexpr_pair_to_list body []))
        

(* var *)
| Symbol(x) -> 
              if(not (List.mem x reserved_word_list)) 
              then Var(x) 
              else raise X_syntax_error



(* quasiquoted *)
| Pair(Symbol "quasiquote", Pair(sexpr, Nil)) ->
(match sexpr with
 | Symbol(x) -> tag_parse (Pair(Symbol "quote", Pair(Symbol(x), Nil)))
 | Nil -> tag_parse (Pair(Symbol "quote", Pair(Nil, Nil)))
 | Number(x) -> tag_parse (Pair(Symbol "quote", Pair(Number(x), Nil)))
 | String (x) -> tag_parse (Pair(Symbol "quote", Pair(String(x), Nil)))
 | Char(x) -> tag_parse (Pair(Symbol "quote", Pair(Char(x), Nil)))
 | Bool(x) -> tag_parse (Pair(Symbol "quote", Pair(Bool(x), Nil)))
 | Pair(a,b) ->
    
 (match a with
  | Symbol "unquote"-> 
    (match b with 
    | Pair(sexpr,_) -> tag_parse(sexpr)
    | _ -> raise X_syntax_error)
  | Symbol "unquote-splicing" -> raise X_syntax_error
  | Pair(Symbol "unquote-splicing", sexpr) ->
      (match sexpr with
      | Pair(sexpr,_) -> tag_parse (Pair(Symbol "append", Pair(sexpr, Pair(Pair(Symbol "quasiquote", Pair(b, Nil)),Nil))))
      | _ -> raise X_syntax_error)
  | _ -> (match b with 
            | Pair(Symbol "unquote-splicing", sexpr) ->
              (match sexpr with
              | Pair(sexpr,_) -> tag_parse(Pair(Symbol "cons", Pair(Pair(Symbol "quasiquote", Pair(a, Nil)), Pair(sexpr, Nil))))
              | _ -> raise X_syntax_error)
            | _ -> tag_parse(Pair(Symbol "cons", Pair(Pair(Symbol "quasiquote", Pair(a, Nil)),
                                                 Pair(Pair(Symbol "quasiquote", Pair(b, Nil)), Nil))))
  ))
  | _ -> raise X_syntax_error)





(* let-macro *)

| Pair(Symbol "let", Pair(bindings, body)) ->
    let vars = extract_bindings_vars bindings Nil in
    let vals = extract_bindings_vals bindings Nil in
    tag_parse (Pair(Pair(Symbol "lambda", Pair(vars, body)), vals))

(* letrec-macro *)
| Pair(Symbol "letrec", Pair(bindings, body)) -> 
    (match body with
    | Nil -> raise X_syntax_error
    | _ ->
    let whatever_bindings = create_whatever_bindings bindings  in
    let body = create_set_bindings bindings body in
    tag_parse (Pair(Symbol "let", Pair(whatever_bindings, body))))

| Pair(Symbol "let*", Pair(bindings, body)) ->
    (match bindings with
      | Nil -> tag_parse (Pair(Symbol "let", Pair(bindings, body)))
      | Pair(bind, Nil) ->  tag_parse (Pair(Symbol "let", Pair(bindings, body)))
      | Pair(bind, rest) ->
            let bindings = Pair(bind, Nil) in
            let body = Pair(Symbol "let*", Pair(rest, body)) in
            tag_parse (Pair(Symbol "let", Pair(bindings, Pair(body,Nil))))
      | _ -> raise X_syntax_error)


(* and *)
| Pair(Symbol "and", rands) -> 
  (match rands with 
    | Nil -> tag_parse(Bool(true))
    | Pair(car,Nil) -> tag_parse(car)
    | Pair(car,cdr) -> 
        tag_parse (Pair(Symbol "if", Pair(car, Pair(Pair(Symbol "and", cdr), Pair(Bool(false),Nil)))))
    | _ -> raise X_syntax_error )

(* cond-macro *)
| Pair(Symbol "cond", ribs) ->
    (match ribs with
      | Pair(rib, Nil) -> (* last rib *)
        (match rib with
          | Pair(test, Pair(Symbol "=>", func)) ->
            tag_parse(Pair(Symbol "let", Pair(
              Pair(
                Pair(Symbol "value", Pair(test, Nil)), 
                Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, func)), Nil)), Nil)),
                Pair(
                  Pair(Symbol "if", 
                    Pair(Symbol "value", 
                    Pair(
                      Pair(
                        Pair(Symbol "f", Nil),
                        Pair(Symbol "value", Nil)),
                      Nil))),
                  Nil))))
          | Pair(test, body) ->
          (match test with
            | Symbol "else" -> tag_parse(Pair(Symbol "begin", body))
            | _ ->  tag_parse (Pair(Symbol "if", 
                    Pair(test, 
                    Pair(
                      Pair(Symbol "begin", body),
                      Nil))))
            )
        | _ -> raise X_syntax_error)
      | Pair(rib, ribs) -> 
          (match rib with
            | Pair(test, Pair(Symbol "=>", func)) ->
              tag_parse (Pair(Symbol "let", Pair(
                Pair(
                  Pair(Symbol "value", Pair(test, Nil)), 
                  Pair(
                    Pair(
                      Symbol "f", 
                      Pair(
                        Pair(
                          Symbol "lambda", 
                          Pair(Nil, func)), Nil)),
                    Pair(Pair(
                          Symbol "rest", 
                          Pair(
                            Pair(
                              Symbol "lambda", 
                              Pair(Nil, Pair(Pair(Symbol "cond", ribs), Nil))), Nil)), Nil))), 
                  Pair(
                    Pair(
                      Symbol "if", 
                      Pair(
                        Symbol "value", 
                        Pair(
                          Pair(
                            Pair(Symbol "f", Nil), 
                            Pair(Symbol "value", Nil)), 
                          Pair(Pair(Symbol "rest", Nil), Nil)))), 
                    Nil))))
            | Pair(test, body) ->
              (match test with
                | Symbol("else") -> tag_parse(Pair(Symbol "begin", body)) (* not the last rib *)
                | _ -> tag_parse (Pair(Symbol "if", 
                    Pair(test, 
                    Pair(
                      Pair(Symbol "begin", body),
                      Pair(Pair(Symbol "cond", ribs),Nil)))))
              )
          | _ -> raise X_syntax_error)
        | _ -> raise X_syntax_error)


(* application *)
| Pair(op, rands) 
      -> Applic (tag_parse op, (tag_parse_sexpr_pair_to_list rands []))

      
  

 


;;

let tag_parse_expression sexpr = tag_parse(sexpr);;


let tag_parse_expressions sexpr = (List.map tag_parse sexpr);

end;; (* struct Tag_Parser *)

