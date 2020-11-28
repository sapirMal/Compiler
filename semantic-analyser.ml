#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | Box'(_), Box'(_) -> true
  | BoxGet'(_), BoxGet'(_) -> true
  | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
  | _ -> false;;

	
                       
exception X_syntax_error;;


module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  (*val expr_to_exprtag : expr -> expr'*)
end;;

module Semantics : SEMANTICS = struct

(* if its member return index else -1*)
let rec find name lst =
    match lst with
    | [] -> VarFree(name)
    | h :: t -> (
      match h with 
      | VarParam(x,_) when String.equal name x -> h
      | VarBound (x, _, _) when String.equal name x -> h
      | _ -> find name t );;

(* global env *)
let env = {contents = []} ;;


(* env = (major, minor) (int * string list) list *)
let rec expr_to_exprtag e =
  match e with
  | Const(expr) -> Const'(expr)
  | Var(name) -> Var'(find name !env )
  | If(test, dit, dif) -> If'(expr_to_exprtag test, expr_to_exprtag dit, expr_to_exprtag dif)
  | Seq(exprs) -> Seq'(List.map (expr_to_exprtag) exprs)
  | Set(var,value) -> Set' (expr_to_exprtag var, expr_to_exprtag value)      
  | Def(var,value) -> Def' (expr_to_exprtag var, expr_to_exprtag value)
  | Or(exprs) -> Or'(List.map (expr_to_exprtag) exprs)
  | LambdaSimple(params,body) -> 

      (* add params to env *)  
      env := (List.map  
      (fun elemnt -> match elemnt with 
      | VarParam(name, minor) -> VarBound (name, 0 ,minor)
      | VarBound (name, major,minor) -> VarBound (name, major + 1, minor)
      | _ -> raise X_syntax_error
      ) !env ) ;

      let param = List.mapi (fun i param-> VarParam(param,i)) params in

      env := param @ !env ;

      let output = LambdaSimple' (params, expr_to_exprtag body) in

      (*  remove params from env  *)
      env := List.filter 
      (fun e -> match e with
      | VarParam(_,_) -> false
      | _ -> true ) 
      !env ;
      env := List.map
      (fun e -> match e with
      | VarBound(name, 0, minor) -> VarParam(name, minor)
      | VarBound(name, major, minor) -> VarBound(name, major - 1, minor)
      | _ -> raise X_syntax_error)
      !env ;
      output

  | LambdaOpt (params, opt, body) -> 
       (* add params to env *)  
      env := (List.map  
      (fun elemnt -> match elemnt with 
      | VarParam(name, minor) -> VarBound (name, 0 ,minor)
      | VarBound (name, major,minor) -> VarBound (name, major + 1, minor)
      | _ -> raise X_syntax_error
      ) !env ) ;

      let param = List.mapi (fun i param-> VarParam(param,i)) (params @ [opt]) in

      env := param @ !env ;

      let output = LambdaOpt' (params, opt, expr_to_exprtag body) in

      (*  remove params from env  *)
      env := List.filter 
      (fun e -> match e with
      | VarParam(_,_) -> false
      | _ -> true ) 
      !env ;
      env := List.map
      (fun e -> match e with
      | VarBound(name, 0, minor) -> VarParam(name, minor)
      | VarBound(name, major, minor) -> VarBound(name, major - 1, minor)
      | _ -> raise X_syntax_error)
      !env ;
      output

  | Applic(op,args) -> Applic'(expr_to_exprtag op, List.map (expr_to_exprtag) args);;
  

let annotate_lexical_addresses e = 
  expr_to_exprtag e;;

let rec expr_to_tail e tp = match e with
  | Const'(x) -> e
  | Var'(x) -> e
  | If'(test,dit,dif) -> If'(expr_to_tail test false, expr_to_tail dit tp, expr_to_tail dif tp)
  | Seq'(x) -> 
      (match x with
      | head::tail -> 
        let res = List.rev x in 
        (match res with 
        | h::t ->
              let output = List.rev_map (fun e -> expr_to_tail e false) t in
              Seq'(output @ [expr_to_tail h tp])
        | _ -> raise X_syntax_error)
      | _ -> raise X_syntax_error)
  | Set'(var,value) -> Set'(expr_to_tail var false, expr_to_tail value false)
  | Def'(var, value) -> Def'(expr_to_tail var false, expr_to_tail value false)
  | Or'(x) ->
  (match x with
      | head::tail -> 
        let res = List.rev x in 
        (match res with 
        | h::t ->
            let output = List.rev_map (fun e -> expr_to_tail e false) t in
            Or'(output @ [expr_to_tail h tp])
        | _ -> raise X_syntax_error)
      | _ -> raise X_syntax_error)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (expr_to_tail body true))
  | LambdaOpt'(params, opt, body) -> LambdaOpt' (params, opt, (expr_to_tail body true)) 
  | Applic'(op,args) -> 
      if tp
      then ApplicTP'(expr_to_tail op false, List.map (fun e -> expr_to_tail e false) args)
      else Applic'(expr_to_tail op false, List.map (fun e -> expr_to_tail e false) args)
  | _ -> raise X_syntax_error

;;




let annotate_tail_calls e = expr_to_tail e false;;

let i = {contents = 0} ;;
let j = {contents = 0} ;;

type box =
    { 
      mutable v     : var ;
      mutable read  : (int*int) list; (* (major, indebx of lambda in major 0) *)
      mutable write : (int*int) list;
      mutable index : int; (*index of lambda in major 0, update when add new lambda *)
      mutable box   : bool;
    };;

let env_box  = {contents=[]};;

let get_name var =
match var with
| Var'(VarParam(name,_)) -> name
| Var'(VarBound(name,_,_)) -> name
| Var'(VarFree(name)) -> name
| _ -> raise X_syntax_error;;

let rec find_var_box var lst = 
let x = get_name (var) in
  (match lst with
  | [] -> raise X_syntax_error
  | h :: t -> (
      match h.v with
      | VarParam(name,_) when String.equal name x -> h
      | VarBound (name,_,_) when String.equal name x -> h
      | _ ->  find_var_box var t));;

 
let find_box_param lst = 

      let maybe_box = List.filter 
      (fun e -> match e.v with
      |  VarParam(_,_) -> true
      | _ -> false ) 
      lst in

      let box_list = (List.map
      (fun e ->
      let read_len = List.length e.read in 
      let write_len = List.length e.write in
      (match e.v with 
      | VarParam(name,minor)->
      
      if (read_len = 0 || write_len = 0)
      then Var'(e.v)
      else begin
        i := 0;
        while (!i <= read_len-1) do
          begin
          j := 0;
          let curr_read = (List.nth e.read !i) in (*major read ; -1 is on stack*) (* (major,index) *)
          while (!j <= write_len-1) do 
          begin
             let curr_write = (List.nth e.write !j) in (*major write ; -1 is on stack*) (* (major,index) *)
             match curr_read, curr_write with
             | (0,y), (0,z) when y != z -> j := write_len + 1
             | (-1,_), (x,_) when x > -1 -> j := write_len + 1
             | (x, _) , (-1, _) when x > -1 ->  j := write_len + 1
             | (x,y) , (w,z) when y != z ->  j := write_len + 1
             | _ -> j := !j + 1 (* this curr read with curr write dont need a box check next *)
             
          end
           done ;
          if (!j = (write_len +1))
          then i := (read_len +1)
          else i := !i +1
      end
       done;
       if (!i = (read_len +1))
       then 
          Box'(VarParam(name,minor))
       else 
          Var'(VarParam(name,minor))
         
       end
      

      | _ -> raise X_syntax_error))
      maybe_box) in

     (* stay only with vars box *)
      let box_list = List.filter (fun e -> match e with
        | Var'(VarParam(_,_)) -> false
        | _ -> true ) 
        box_list in
        box_list;;

let add_params_to_env params = 
(* add params to env *)  
      env_box := (List.map  
      (fun e -> 
      (match e with 
      | {v= variable; read= read_list; write= write_list; index = i; box = b} -> 
      (match e.v with
        | VarParam(name, minor) -> 
          e.v <- VarBound (name, 0 ,minor) ; 
          e.index <- e.index + 1; 
          e
        | VarBound (name, major,minor) -> 
          e.v <- VarBound (name, major + 1, minor) ;
          e
        | _ -> raise X_syntax_error)
      ))
      !env_box ) ;

      let param = (List.mapi (fun i param-> ({v = VarParam(param, i); read = []; write = []; index = -1; box = false})) params) in

      env_box := param @ !env_box ;;


let remove_params_from_env () = 
        env_box := List.filter 
        (fun e -> (match e with 
        | {v= variable; read= read_list; write= write_list; index = i; box = b} -> 
          (match e.v with
            | VarParam(x,_) -> false
            | _ -> true )
        ))
         !env_box ;

        env_box := List.map
        (fun e -> 
          (match e with 
          | {v= variable; read= read_list; write= write_list ; index = i; box = b} -> 
            (match e.v with
              | VarBound(name, 0, minor) ->
                e.v <- VarParam(name, minor);
                e
              | VarBound(name, major, minor) -> 
                e.v <- VarBound(name, major - 1, minor);
                e
              | _ -> raise X_syntax_error)
          ))
          !env_box ;;



let rec expr_to_box e = match e with
  | Const'(x) -> e
  | Var'(x) -> 
    (match x with
    | VarFree(_) -> e
    | _ -> let var = find_var_box e !env_box in
    
    if(var.box)
    then BoxGet'(x)
    else 
      (match x with
      | VarParam(_,_) -> var.read <- var.read @ [(-1,var.index)]; e
      | VarBound(_,m,_)-> var.read <- var.read @ [(m,var.index)]; e
      | VarFree(_) -> e))
  | Box'(x) -> e 
  | BoxGet'(x) -> e
  | BoxSet'(var, value) -> BoxSet'(var, expr_to_box value)
  | If'(test, dit, dif) -> If'(expr_to_box test, expr_to_box dit, expr_to_box dif)
  | Seq'(expr_list) -> Seq'(List.map (expr_to_box) expr_list)
  | Set'(x, value) ->  
    (match x with
    | Var'(VarFree(y)) -> Set'(x, expr_to_box value)
    |_ -> let var = find_var_box x !env_box in
    if(var.box)
    then 
    (match x with

      | Var'(x) -> BoxSet'(x, expr_to_box value)
      | _ -> raise X_syntax_error
    )
    else 
      (match x with
      | Var'(VarParam(_,_)) -> var.write <- var.write @ [(-1,var.index)]; Set'(x, expr_to_box value)
      | Var'(VarBound(_,m,_))-> var.write <- var.write @ [(m,var.index)]; Set'(x, expr_to_box value)
      | Var'(VarFree(_)) -> Set'(x, expr_to_box value)
      | _ -> raise X_syntax_error))
  | Def'(x, value) -> Def'(x, expr_to_box value)
  | Or'(expr_list) -> Or' (List.map (expr_to_box) expr_list)
  | LambdaSimple'(params,body) ->
     add_params_to_env params ;
     
    let output = LambdaSimple'(params, expr_to_box body) in (* env_box update for read and write *)

      (* check if there is a var that need a box *)
    let box_list = find_box_param !env_box in

    (match box_list with
      | [] -> remove_params_from_env(); output  (* no boxes, so we're done *)
      | _ ->

      (* add set! Set(VarParam(v, minor), Box'(VarParam(v, minor)))  to body *)

      let add_box_set = List.map 
      (fun e -> (match e with
      | Box'(VarParam(name,minor)) -> Set'(Var'(VarParam(name,minor)), Box'(VarParam(name,minor)))
      | _ -> raise X_syntax_error))
      box_list in

      (* update env_box e.box<-true for params that need boxing*)
      env_box := List.map 
      (fun e -> (match e.v with
      | VarParam(name,minor) ->
        if List.mem (Box'(e.v)) box_list
        then begin e.box <- true; e end
        else e
      | _ -> e
       )) !env_box;

      (* add  Set'(Var'(VarParam(name,minor)), Box'(VarParam(name,minor) to body *)
      (match output with
      | LambdaSimple'(params, body) -> 
        let body = expr_to_box body in
        let body = Seq'(add_box_set @ [body]) in

        (* update get (read) BoxGet' and set (write) BoxSet' rec *)
        remove_params_from_env();

        LambdaSimple'(params, body)
      
        
      | _ -> raise X_syntax_error))
      

  | LambdaOpt' (params, opt, body) -> 
    add_params_to_env (params @ [opt]) ;
     
    let output = LambdaOpt'(params, opt, expr_to_box body) in (* env_box update for read and write *)

      (* check if there is a var that need a box *)
    let box_list = find_box_param !env_box in

    (match box_list with
      | [] -> remove_params_from_env(); output  (* no boxes, so we're done *)
      | _ ->

      (* add set! Set(VarParam(v, minor), Box'(VarParam(v, minor)))  to body *)

      let add_box_set = List.map 
      (fun e -> (match e with
      | Box'(VarParam(name,minor)) -> Set'(Var'(VarParam(name,minor)), Box'(VarParam(name,minor)))
      | _ -> raise X_syntax_error))
      box_list in

      (* update env_box e.box<-true for params that need boxing*)
      env_box := List.map 
      (fun e -> (match e.v with
      | VarParam(name,minor) ->
        if List.mem (Box'(e.v)) box_list
        then begin e.box <- true; e end
        else e
      | _ -> e
       )) !env_box;

      (* add  Set'(Var'(VarParam(name,minor)), Box'(VarParam(name,minor) to body *)
      (match output with
      | LambdaOpt'(params, opt, body) -> 
        let body = expr_to_box body in
        let body = Seq'(add_box_set @ [body]) in
                 
        (* update get (read) BoxGet' and set (write) BoxSet' rec *)
        remove_params_from_env();

        LambdaOpt'(params, opt, body)  

      | _ -> raise X_syntax_error))
  | Applic'(op, args) -> Applic'(expr_to_box op, List.map (expr_to_box) args)
  | ApplicTP'(op, args) -> ApplicTP'(expr_to_box op, List.map (expr_to_box) args)
 ;;

let box_set e = expr_to_box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
