#use "semantic-analyser.ml";;
open Semantics;;
exception DEBUG;;
exception DEBUG1;;
exception WHY_IS_HERE;;
exception X_not_yet_implemented;;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
 
  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string

  val rename_tagged : expr' -> expr'
end;;

module Code_Gen : CODE_GEN = struct
let tag_count = {contents = 0};;
let tag_count_name = {contents = []};;

let find_and_set name = 
  tag_count := !tag_count + 1 ;
  if (List.mem name (List.map (fun (n,i)-> n) !tag_count_name))
  then 
    tag_count_name := (List.fold_left
    (fun lst (n,i)-> 
      if(String.equal name n)
      then lst @ [(n,!tag_count)]
      else lst @ [(n,i)]
    )   []    !tag_count_name )
  else
  begin
  tag_count_name := !tag_count_name @ [(name, !tag_count)];
  end
 ;;

 let find_and_get name = 
  try 
    let (n, index) as res = List.find (fun (n,i) -> String.equal n name) !tag_count_name in
    index
  with Not_found ->
  begin
    find_and_set name;
    !tag_count
  end
  ;;
  
let rec rename_sexpr sexpr = 
  match sexpr with
      | Bool(y) -> sexpr
      | Nil -> sexpr
      | Number(y) -> sexpr
      | Char(y) -> sexpr
      | String(y) -> sexpr
      | Symbol(y) -> sexpr
      | TagRef(name) -> 
      begin
        let index = find_and_get name in
        TagRef(name^(string_of_int index))
      end
      | Pair(a,b) -> Pair(rename_sexpr a, rename_sexpr b)
      | TaggedSexpr(name, y) -> 
      begin 
        TaggedSexpr(name^(string_of_int (find_and_get name)), rename_sexpr y)
      end
    ;;

let rec rename_tagged expr = 
  match expr with
      | Const'(const) -> 
        (match const with
        | Void -> expr
        | Sexpr(x) -> 
          (match x with
          | Bool(y) -> expr
          | Nil -> expr
          | Number(y) -> expr
          | Char(y) -> expr
          | String(y) -> expr
          | Symbol(y) -> expr
          | TagRef(y) -> 
            begin 
              tag_count_name := [];
              Const'(Sexpr(rename_sexpr x))
            end
          | Pair(a,b) ->
            begin 
              tag_count_name := [];
              Const'(Sexpr(rename_sexpr x))
              end
          | TaggedSexpr(name, y) -> 
            begin 
              tag_count_name := [];
              Const'(Sexpr(rename_sexpr x))
              end
        ))

      | Var'(x) -> expr
      | Box'(x) -> expr
      | BoxGet'(x) -> expr
      | BoxSet'(var, value) -> BoxSet'(var,(rename_tagged value))
      | If'(test,dit,dif) -> If'(rename_tagged test, rename_tagged dit, rename_tagged dif)
      | Seq'(exprs) -> Seq'(List.map rename_tagged exprs)
      | Set'(var, value) -> Set'(var, rename_tagged value)
      | Def'(var, value) -> Def'(var, rename_tagged value)
      | Or'(exprs) -> Or'(List.map rename_tagged exprs)
      | LambdaSimple'(params, body) -> LambdaSimple'(params, rename_tagged body)
      | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt,rename_tagged body)
      | Applic'(op, rands) -> Applic'(rename_tagged op,List.map rename_tagged rands)
      | ApplicTP'(op, rands) -> ApplicTP'(rename_tagged op,List.map rename_tagged rands)
  ;;

let tag_definitions = {contents = []}

let rec extract_consts expr =
  match expr with
    | Const'(const) ->
      (match const with
        | Void -> [const]
        | Sexpr(x) -> 
        (match x with
          | Bool(y) -> [const]
          | Nil -> [const]
          | Number(y) -> [const]
          | Char(y) -> [const]
          | String(y) -> [const]
          | Symbol(y) -> [const]
          | TagRef(y) -> []
          | Pair(a,b) -> [const]
          | TaggedSexpr(name, sexpr) -> 
            begin
            tag_definitions := !tag_definitions @ [(name, sexpr)];
            [(Sexpr(sexpr))]
            end))
    | Var'(x) -> []
    | Box'(x) -> []
    | BoxGet'(x) -> []
    | BoxSet'(var, value) -> (extract_consts value)
    | If'(test,dit,dif) -> List.flatten [extract_consts test; extract_consts dit; extract_consts dif]
    | Seq'(exprs) -> List.flatten (List.map extract_consts exprs)
    | Set'(var, value) -> List.flatten [extract_consts var; extract_consts value]
    | Def'(var, value) -> List.flatten [extract_consts var; extract_consts value]
    | Or'(exprs) -> List.flatten (List.map extract_consts exprs)
    | LambdaSimple'(params, body) -> (extract_consts body)
    | LambdaOpt'(params, opt, body) -> (extract_consts body)
    | Applic'(op, rands) -> List.flatten [extract_consts op; List.flatten (List.map extract_consts rands)]
    | ApplicTP'(op, rands) -> List.flatten [extract_consts op; List.flatten (List.map extract_consts rands)]
  ;;

let make_set list =
  List.fold_left 
  (fun tail head ->
    if (List.mem head tail)
    then tail
    else tail @ [head]
  )
  [] 
  list;;
let rec build_pair expr =
  match expr with
  | Bool(y) -> expr
  | Nil -> expr
  | Number(y) -> expr
  | Char(y) -> expr
  | String(y) -> expr
  | Symbol(y) -> expr
  | TagRef(y) -> expr
  | Pair(a,b) -> Pair(build_pair a, build_pair b)
  | TaggedSexpr(name, sexpr) -> sexpr;;

let rec sub_sexpr expr list =
  match expr with
  | Sexpr(x) -> 
      (match x with
      | Bool(y) -> [expr] @ list
      | Nil -> [expr] @ list
      | Number(y) -> [expr] @ list
      | Char(y) -> [expr] @ list
      | String(y) -> [expr] @ list
      | Symbol(y) -> [(Sexpr(String(y)));expr] @ list
      | TagRef(y) -> list
      | Pair(a,b) -> (sub_sexpr (Sexpr(b)) []) @ (sub_sexpr (Sexpr(a)) []) @ ([Sexpr(build_pair x)] @ list)
      | TaggedSexpr(name, sexpr) -> 
        begin
          tag_definitions := !tag_definitions @ [(name, sexpr)];
          (sub_sexpr (Sexpr(sexpr)) []) @ list
        end)
    |_ -> raise DEBUG;; 
let find_tag name =
    let tag = List.filter (fun (n,s) -> String.equal name n) !tag_definitions in
    match tag with
    | (n,s)::t -> s
    | _ -> raise WHY_IS_HERE
    ;;
let expand_consts_list list =
 List.fold_left 
   (fun expr_a expr_b -> 
   match expr_b with
   | Void -> expr_a @ [expr_b]
   | Sexpr(x) -> 
      (match x with
      | Bool(y) -> expr_a @ [expr_b]
      | Nil -> expr_a @ [expr_b]
      | Number(y) -> expr_a @ [expr_b]
      | Char(y) -> expr_a @ [expr_b]
      | String(y) -> expr_a @ [expr_b]
      | Symbol(y) -> expr_a @ [(Sexpr(String(y)));expr_b]
      | TagRef(y) -> expr_a @ [expr_b] (* will be change in second round *)
      | Pair(a,b) -> expr_a @ (sub_sexpr expr_b [])
      | TaggedSexpr(name, sexpr) -> raise WHY_IS_HERE
        ))
   []
   list;;

let get_size const =
  match const with
    | Void -> 1
    | Sexpr(x) -> 
      (match x with
      | Bool(y) -> 2
      | Nil -> 1
      | Number(y) -> 9
      | Char(y) -> 2
      | String(y) -> (String.length y) + 9
      | Symbol(y) -> 9
      | TagRef(y) -> 8 (* pointer only *)
      | Pair(a,b) -> 17
      | TaggedSexpr(name, y) -> raise WHY_IS_HERE ) (* pointer to name (string) and a pointer to y (sexpr) *);;

let offset_consts = {contents = 0};;

let rec compare_consts const_a const_b =
  match const_a, const_b with
    | Void, Void -> true
    | Sexpr(x), Sexpr(z) -> 
      (match x, z with
      | Bool(y), Bool(w) when y = w -> true
      | Nil, Nil -> true
      | Number(y), Number(w) -> 
        (match y, w with
          | Int(num1), Int(num2) when num1 = num2 -> true
          | Float(num1), Float(num2) when num1 = num2 -> true
          | _ -> false
        )
      | Char(y), Char(w) when y = w -> true
      | String(y), String(w) when (String.equal y w) -> true
      | Symbol(y), Symbol(w) when (String.equal y w) -> true
      | TagRef(y), TagRef(w) when (String.equal y w) -> true
      | Pair(a,b), Pair(c,d) when ((compare_consts (Sexpr(a)) (Sexpr(c))) && (compare_consts (Sexpr(b)) (Sexpr(d)))) -> true
      | TaggedSexpr(name1, y), TaggedSexpr(name2, w) when ((String.equal name1 name2) && (compare_consts (Sexpr(y)) (Sexpr(w)))) -> true
      | _, _ -> false)
    | _, _ -> false;;


let get_const_offset const table =
  try let output = 
    List.find
    (fun elem ->
      (compare_consts const (fst elem))
    )
    table in
    let offset = (string_of_int (fst (snd output))) in
    offset
  with Not_found -> 
    (match const with
      | Sexpr(TagRef(name)) -> "REF"
      | _ -> raise DEBUG
    );;


(* (constant * (int * string)) list *)
let create_consts_tuples table expr =
  let (tuple, size) = 
    (match expr with
      | Void -> ((expr, (!offset_consts, "MAKE_VOID")), get_size Void)
      | Sexpr(x) -> 
        (match x with
        | Bool(y) when y = false -> ((expr, (!offset_consts, "MAKE_BOOL(0)")), get_size expr)
        | Bool(y) when y = true -> ((expr, (!offset_consts, "MAKE_BOOL(1)")), get_size expr)
        | Nil -> ((expr, (!offset_consts, "MAKE_NIL")), get_size expr)
        | Number(y) -> 
          (match y with
            | Int(num) -> ((expr, (!offset_consts, "MAKE_LITERAL_INT(" ^ (string_of_int num) ^ ")")), get_size expr)
            | Float(num) -> ((expr, (!offset_consts, "MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^ ")")), get_size expr) (* to complete *)
          )
        | Char(y) -> ((expr, (!offset_consts, Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (Char.code y))), get_size expr)
        | String(y) -> ((expr, (!offset_consts, "MAKE_LITERAL_STRING \"" ^ (String.escaped y) ^ "\"")), get_size expr)
        | Symbol(y) -> ((expr, (!offset_consts, 
            "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (get_const_offset (Sexpr(String(y))) table) ^ ")")), 
            get_size expr)
        | TagRef(y) -> raise WHY_IS_HERE
        | Pair(a,b) -> ((expr, (!offset_consts, 
            "MAKE_LITERAL_PAIR"
            ^ "(const_tbl+" ^ (get_const_offset (Sexpr(a)) table) ^ 
            ", const_tbl+" ^ (get_const_offset (Sexpr(b)) table) ^ ")")), 
            get_size expr)
        
        | _ -> raise DEBUG)) in
  offset_consts := !offset_consts + size;
  table @ [tuple];;


let rec tag_helper sexpr old_tbl =
  match sexpr with
    | Bool(y) -> get_const_offset (Sexpr(sexpr)) old_tbl
    | Nil -> get_const_offset (Sexpr(sexpr)) old_tbl
    | Number(y) -> get_const_offset (Sexpr(sexpr)) old_tbl
    | Char(y) -> get_const_offset (Sexpr(sexpr)) old_tbl
    | String(y) -> get_const_offset (Sexpr(sexpr)) old_tbl
    | Symbol(y) -> get_const_offset (Sexpr(sexpr)) old_tbl
    | TagRef(name) -> 
        begin
          let sexpr = find_tag name in
          let address = get_const_offset (Sexpr(sexpr)) old_tbl in
          address
        end  
    | Pair(a,b) -> get_const_offset (Sexpr(sexpr)) old_tbl
    | TaggedSexpr(_,_) -> raise WHY_IS_HERE
    
    
    ;;
let tag_consts_table old_tbl table tuple =
  let element = 
    (match (fst tuple) with
      | Sexpr(Pair(a,b)) -> (Sexpr(Pair(a,b)),((fst(snd tuple)),"MAKE_LITERAL_PAIR"
            ^ "(const_tbl+" ^ (tag_helper a old_tbl) ^ 
            ", const_tbl+" ^ (tag_helper b old_tbl) ^ ")"))
      | _ -> tuple
     ) in
  table @ [element];;


let make_consts_tbl asts = 
    let consts_list = List.flatten (List.map extract_consts asts) in
    let consts_list = [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))] @ consts_list in
    let consts_list = make_set consts_list in
    let consts_list = expand_consts_list consts_list in
    let consts_list = make_set consts_list in
    let consts_list = List.fold_left create_consts_tuples [] consts_list in
    let consts_list = List.fold_left (tag_consts_table consts_list) [] consts_list in


    offset_consts := 0;
    tag_count := 0;
    consts_list
   ;;

let fvar_offset = {contents = 0};;

let rec extract_fvars expr =
  match expr with
    | Const'(const) -> []
    | Var'(x) -> 
      (match x with
        | VarFree(y) -> [y]
        | _ -> [])
    | Box'(x) -> 
      (match x with
        | VarFree(y) -> [y]
        | _ -> [])
    | BoxGet'(x) -> 
      (match x with
        | VarFree(y) -> [y]
        | _ -> [])
    | BoxSet'(var, value) -> 
      (match var with
        | VarFree(y) -> [y] @ (extract_fvars value)
        | _ -> (extract_fvars value))
    | If'(test,dit,dif) -> List.flatten [extract_fvars test; extract_fvars dit; extract_fvars dif]
    | Seq'(exprs) -> List.flatten (List.map extract_fvars exprs)
    | Set'(var, value) -> List.flatten [extract_fvars var; extract_fvars value]
    | Def'(var, value) -> List.flatten [extract_fvars var; extract_fvars value]
    | Or'(exprs) -> List.flatten (List.map extract_fvars exprs)
    | LambdaSimple'(params, body) -> (extract_fvars body)
    | LambdaOpt'(params, opt, body) -> (extract_fvars body)
    | Applic'(op, rands) -> List.flatten [extract_fvars op; List.flatten (List.map extract_fvars rands)]
    | ApplicTP'(op, rands) -> List.flatten [extract_fvars op; List.flatten (List.map extract_fvars rands)]
  ;;

let create_fvar_tuples lst fvar =
    let names_lst = (List.map (fun (str,index) -> str) lst) in
    if (List.mem fvar names_lst)
    then lst
    else 
      begin
        let output = lst @ [(fvar, !fvar_offset)] in
        fvar_offset := !fvar_offset + 8;
        output
      end;;

let get_fvar_address fvar table =
  try let output = 
    List.find
    (fun elem ->
      (String.equal fvar (fst elem))
    )
    table in
    let offset = (string_of_int (snd output)) in
    offset
  with Not_found -> raise DEBUG1;;

let make_fvars_tbl asts = 
  let fvars_list = ["boolean?"; "float?"; "integer?"; "pair?";
   "null?"; "char?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "symbol->string"; "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "="; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!";
   "apply"] in
  let fvars_list = fvars_list @ (List.flatten (List.map extract_fvars asts)) in
  let fvars_list = List.fold_left create_fvar_tuples [] fvars_list in
  fvar_offset := 0;
  fvars_list;;

let env_counter = {contents = -1};;
let label_counter = {contents = 1};;
let label_generator label =
  let numbered_label = Printf.sprintf "%s%d" label !label_counter in
  label_counter := !label_counter + 1;
  numbered_label;;

let rec generate consts fvars e = 
  match e with
    | Const'(const) -> 
      let const = (match const with
        | Sexpr(TaggedSexpr(name, sexpr)) -> 
          let sexpr = (match sexpr with
            | Pair(a,b) -> Pair((build_pair a),(build_pair b))
            | _ -> sexpr
          ) in
          Sexpr(sexpr)
        | Sexpr(Pair(a,b)) -> Sexpr((build_pair (Pair(a,b))))
        | _ -> const
      ) in
      let address = (get_const_offset const consts) in
      Printf.sprintf ";Const ->\n mov rax, const_tbl+%s\n ;<- Const\n\n" address
    | Var'(x) -> 
      (match x with
        | VarFree(name) ->
          let address = (get_fvar_address name fvars) in
          Printf.sprintf ";Fvar ->\n mov rax, [fvar_tbl+%s]\n ;<- Fvar\n\n" address
        | VarParam(_,minor) -> 
          let var_get = Printf.sprintf "mov rax, qword [rbp + 8 * (4 + %d)]\n" minor in
          Printf.sprintf "; Pvar ->\n %s; <- Pvar\n" var_get
        | VarBound(_,major,minor) -> 
          let var_get = "mov rax, qword [rbp + 8 * 2]\n" in
          let var_get = var_get ^ Printf.sprintf "mov rax, qword [rax + 8 * %d]\n" major in
          let var_get = var_get ^ Printf.sprintf "mov rax, qword [rax + 8 * %d]\n" minor in
          Printf.sprintf "; Bvar ->\n%s; <- Bvar\n" var_get
      )
    | Box'(x) -> 
      (match x with
        | VarParam(name,minor) -> 
          let var = (generate consts fvars (Var'(x))) in
          let var = var ^ "push rax\n" in
          let set = "MALLOC rax, 8\n" in
          let set = set ^ "pop qword [rax]\n" in
          let output = var ^ set in
          Printf.sprintf "; -> Box\n %s ; <- Box\n" output
        | _ -> raise DEBUG
      )
    | BoxGet'(x) -> 
      let var = (generate consts fvars (Var'(x))) in
      let read = "mov rax, qword [rax]\n" in
      let output = var ^ read in
      Printf.sprintf "; BoxGet ->\n %s ; <- BoxGet\n" output
    | BoxSet'(var, value) -> 
      let value = (generate consts fvars value) in
      let value = value ^ "push rax\n" in
      let var = (generate consts fvars (Var'(var))) in
      let set = "pop qword [rax]\n" in
      let finish = "mov rax, SOB_VOID_ADDRESS\n" in
      let output = value ^ var ^ set ^ finish in
      Printf.sprintf "; BoxSet ->\n %s ; <- BoxSet\n" output
    | If'(test,dit,dif) -> 
      let lelse = (label_generator "Lelse") in
      let lexit = (label_generator "Lexit") in
      let test = generate consts fvars test in
      let dit = generate consts fvars dit in
      let dif = generate consts fvars dif in
      let output = ";IF -> \n" ^
      test ^
      "cmp rax, SOB_FALSE_ADDRESS\n" ^
      "je " ^ lelse ^ "\n" ^ 
      dit ^
      "jmp " ^ lexit ^ "\n" ^
      lelse ^ ":\n" ^ dif ^
      lexit ^ ":\n" ^
      ";<- IF\n\n" in
      Printf.sprintf "%s" output
    | Seq'(exprs) -> Printf.sprintf ";Seq ->\n %s\n" (List.fold_left (fun output expr -> output ^ (generate consts fvars expr)) "" exprs)
    | Set'(var, value) ->
      let value_load = ";Set -> \n " ^ (generate consts fvars value) in
      let complete_set = 
        (match var with
        | Var'(VarFree(name)) -> 
          let output = value_load ^ "mov qword [fvar_tbl+" ^ (get_fvar_address name fvars) ^ "], rax\n" ^
                       "mov rax, SOB_VOID_ADDRESS\n" in
          Printf.sprintf "%s" output
        | Var'(VarParam(_, minor)) -> 
          let output = value_load ^ Printf.sprintf "mov qword [rbp + 8 * (4 + %d)], rax\n" minor in
          let output = output ^ "mov rax, SOB_VOID_ADDRESS\n" in
          Printf.sprintf "%s" output
        | Var'(VarBound(_,major,minor)) -> 
          let pushes = "push rbx\n" in
          let var_set = "mov rbx, qword [rbp + 8 * 2]\n" in
          let var_set = var_set ^ Printf.sprintf "mov rbx, qword [rbx + 8 * %d]\n" major in
          let var_set = var_set ^ Printf.sprintf "mov qword [rbx + 8 * %d], rax\n" minor in
          let var_set = var_set ^ "mov rax, SOB_VOID_ADDRESS\n" in
          let pops = "pop rbx\n" in
          let output = pushes ^ value_load ^ var_set ^ pops in
          Printf.sprintf "; Bvar ->\n%s; <- Bvar\n" output
        | _ -> raise DEBUG) in
        complete_set
    | Def'(var, value) -> 
      let value_load = ";Def -> \n" ^ (generate consts fvars value) in
      let complete_def = 
        (match var with
        | Var'(VarFree(name)) -> 
          let output = value_load ^ "mov qword [fvar_tbl+" ^ (get_fvar_address name fvars) ^ "], rax\n" ^
                       "mov rax, SOB_VOID_ADDRESS\n" in
          Printf.sprintf "%s" output
        | _ -> raise WHY_IS_HERE
        ) in
        complete_def
    | Or'(exprs) -> 
      let lexit = label_generator "Lexit" in
      let output = Printf.sprintf ";Or ->\n %s\n"
        (List.fold_left 
          (fun output expr ->
               output ^ (generate consts fvars expr) ^
               "cmp rax, SOB_FALSE_ADDRESS\n"^
               "jne "^ lexit ^"\n")
          ""
          exprs) in
      output ^ lexit ^ ":\n ;<- Or\n"


    | LambdaSimple'(params, body) -> 
      env_counter := !env_counter + 1;
      let pushes = "push rbx\n"^
                   "push rdx\n"^
                   "push rcx\n"^
                   "push r8\n"^
                   "push rdi\n"^
                   "push r9\n" in
      let env = if (!env_counter = 0)
      then Printf.sprintf "mov rbx, const_tbl+%s\n" (get_const_offset (Sexpr(Nil)) consts)
      else 
        begin
          let env_size = Printf.sprintf "mov rbx, %d\n" !env_counter in
          let env_size = env_size ^ "shl rbx, 3\n" in
          let env_size = env_size ^ "MALLOC rbx, rbx\n" in (* major vector *)
          let ext_env = {contents = ""} in
          for major = 0 to (!env_counter - 2) do
              ext_env := !ext_env ^ 
              "mov rdx, qword [rbp + 8 * 2]\n" ^ (* old env *)
              "mov rdx, qword [rdx + 8 * " ^ (string_of_int major) ^ "]\n" ^ (* get pointer to minor *)
              "mov qword [rbx + 8 * " ^ (string_of_int (major +1)) ^ "], rdx\n"; (* set pointer to minor *)
          done ;
          let lext_env = label_generator "Ext_Env_Loop" in
          let env = env_size ^ !ext_env in 
          let env = env ^  (* set major, minor 0,0 *)
          "mov rcx, qword [rbp + 8 * 3] ; param count old frame\n" ^ (* size of params in old env *)
          "mov rax, rcx\n" ^
          "shl rax, 3\n" ^
          "MALLOC rdx, rax\n" ^
          "mov r9, rcx \n" ^ (* size of params in old env *)
          lext_env ^ ":\n" ^
            "\t mov rax, 4\n" ^
            "\t sub r9, 1\n" ^
            "\t add rax, r9\n" ^ (* place in stack of param*)
            "\t mov r8, qword [rbp + 8 * rax] ;r8 <- param[i]\n" ^
            "\t mov qword [rdx + 8 * r9], r8 ;ExtEnv[0][i] = param_i \n" ^ 
            "\t loop " ^ lext_env ^ ", rcx\n" ^
            "mov qword [rbx], rdx ;connect ExtEnv[0]\n" in
            env
        end in
      let lcode = label_generator "Lcode" in
      let lcont = label_generator "Lcont" in
      let closure = 
      "MAKE_CLOSURE(rax, rbx, " ^ lcode ^ ")\n" ^
      "jmp " ^ lcont ^ "\n" in
      let code = lcode ^ ":\n" ^
      "\t push rbp\n" ^
      "\t mov rbp, rsp\n" ^
      "\t " ^ (generate consts fvars body) ^ 
      "\t leave \n" ^
      "\t ret; pop and jmp to ret addr\n" ^ lcont ^":\n" in
      let pops = "\tpop r9\n"^
                 "\tpop rdi\n"^
                 "\tpop r8\n"^
                 "\tpop rcx\n"^
                 "\tpop rdx\n"^
                 "\tpop rbx\n" in
      let final_closure = pushes ^ env ^ closure ^ code ^ pops in
      env_counter := !env_counter - 1 ;
      Printf.sprintf ";LambdaSim ->\n %s ;LambdaSim\n" final_closure
      


    | LambdaOpt'(params, opt, body) -> 
      env_counter := !env_counter + 1;
      let pushes = "push rbx\n"^
                   "push rdx\n"^
                   "push rcx\n"^
                   "push r8\n"^
                   "push rdi\n"^
                   "push r9\n" in
      let env = if (!env_counter = 0)
      then Printf.sprintf "mov rbx, const_tbl+%s\n" (get_const_offset (Sexpr(Nil)) consts)
      else 
        begin
          let env_size = Printf.sprintf "mov rbx, %d\n" !env_counter in
          let env_size = env_size ^ "shl rbx, 3\n" in
          let env_size = env_size ^ "MALLOC rbx, rbx\n" in (* major vector *)
          let ext_env = {contents = ""} in
          for major = 0 to (!env_counter - 2) do
              ext_env := !ext_env ^ 
              "mov rdx, qword [rbp + 8 * 2]\n" ^ (* old env *)
              "mov rdx, qword [rdx + 8 * " ^ (string_of_int major) ^ "]\n" ^ (* get pointer to minor *)
              "mov qword [rbx + 8 * " ^ (string_of_int (major +1)) ^ "], rdx\n"; (* set pointer to minor *)
          done ;
          let lext_env = label_generator "Ext_Env_Loop" in
          let env = env_size ^ !ext_env in 
          let env = env ^  (* set major, minor 0,0 *)
          "mov rcx, qword [rbp + 8 * 3] ; param count old frame\n" ^ (* size of params in old env *)
          "mov rax, rcx\n" ^
          "shl rax, 3\n" ^
          "MALLOC rdx, rax\n" ^
          "mov r9, rcx \n" ^ (* size of params in old env *)
          lext_env ^ ":\n" ^
            "\t mov rax, 4\n" ^
            "\t sub r9, 1\n" ^
            "\t add rax, r9\n" ^ (* place in stack of param*)
            "\t mov r8, qword [rbp + 8 * rax] ;r8 <- param[i]\n" ^
            "\t mov qword [rdx + 8 * r9], r8 ;ExtEnv[0][i] = param_i \n" ^ 
            "\t loop " ^ lext_env ^ ", rcx\n" ^
            "mov qword [rbx], rdx ;connect ExtEnv[0]\n" in
            env
        end in
      let lcode = label_generator "Lcode" in
      let lcont = label_generator "Lcont" in
      let closure = 
      "MAKE_CLOSURE(rax, rbx, " ^ lcode ^ ")\n" ^
      "jmp " ^ lcont ^ "\n" in
      let code = lcode ^ ":\n" ^
         "\t push rbp\n" ^
         "\t mov rbp, rsp\n" ^
      Printf.sprintf "\t FIX_OPT_STACK %d\n" (List.length params) ^
     
        "\t " ^ (generate consts fvars body) ^ 
      "\t leave\n" ^
      "\t ret; pop and jmp to ret addr\n" ^ lcont ^":\n" in
      let pops = "\tpop r9\n"^
                 "\tpop rdi\n"^
                 "\tpop r8\n"^
                 "\tpop rcx\n"^
                 "\tpop rdx\n"^
                 "\tpop rbx\n" in
      let final_closure = pushes ^ env ^ closure ^ code ^ pops in
      env_counter := !env_counter - 1 ;
      Printf.sprintf ";LambdaOpt ->\n %s ;LambdaOpt\n" final_closure



    | Applic'(op, rands) -> 
      let lerror = (label_generator "ERROR") in
      let pushes = "push rbx\n" in
      let push_magic = "push SOB_NIL_ADDRESS\n" in
      let push_args = List.fold_right 
      (fun arg output -> 
        let arg_val = (generate consts fvars arg) ^ "push rax \n" in
        output ^ arg_val
      )
      rands "" in
      let push_n = Printf.sprintf "push %d\n" ((List.length rands)+1) in
      let op = (generate consts fvars op) in
      let op = op ^ "cmp byte [rax], T_CLOSURE \n" in
      let op = op ^ "jne " ^ lerror ^ "\n" in
      let op = op ^ "CLOSURE_ENV rbx, rax ; rbx conatins pointer to env\n" in
      let op = op ^ "push rbx\n" in
      let op = op ^ "CLOSURE_CODE rbx, rax ; rbx contains pointer to Lcode\n" in
      let op = op ^ "call rbx\n" in
      let clean = "add rsp , 8*1 ; pop env \n" in
      let clean = clean ^ "pop rbx ; pop arg count\n" in
      (* let clean = clean ^ "inc rbx ; one more for magic\n" in *)
      let clean = clean ^ "shl rbx , 3 ; rbx = rbx * 8 \n" in
      let clean = clean ^ "add rsp , rbx; pop args\n" in
      let case_error = lerror ^ ":\n" in
      let pops = "pop rbx\n" in
      let applic = pushes ^ push_magic ^ push_args ^ push_n ^ op ^ clean ^ case_error ^ pops in
      Printf.sprintf ";Applic ->\n %s ;<- Applic\n" applic  



    | ApplicTP'(op, rands) -> 
      let lerror = (label_generator "ERROR") in
      let lshift = (label_generator "SHIFT") in
      let push_magic = "push SOB_NIL_ADDRESS\n" in
      let push_args = List.fold_right 
      (fun arg output -> 
        let arg_val = (generate consts fvars arg) ^ "push rax \n" in
        output ^ arg_val
      )
      rands "" in
      let push_n = Printf.sprintf "push %d\n" ((List.length rands)+1) in
      let op = (generate consts fvars op) in
      let op = op ^ "cmp byte [rax], T_CLOSURE \n" in
      let op = op ^ "jne " ^ lerror ^ "\n" in
      let op = op ^ "CLOSURE_ENV r10, rax\n" in
      let op = op ^ "push r10 ; push env\n" in
      let op = op ^ "mov r12, rax; backup closure\n" in
      let op = op ^ "push qword [rbp + 8] ; old return address\n" in
      let op = op ^ "mov r10, qword [rbp]; backup for old rbp \n" in
      let shift = "; " ^ lshift ^ ":\n" in (* added as a comment in assembly *)
      let shift = shift ^ Printf.sprintf "SHIFT_FRAME %d, 0\n" ((List.length rands) + 5) (*with magic*) in
      let shift = shift ^ "CLOSURE_CODE rax, r12\n" in
      let shift = shift ^ "mov rbp, r10 ;reconstruct rbp\n" in
      let run_code = "jmp rax ; jmp to code\n" in
      let case_error = lerror ^ ":\n" in
      let output = push_magic ^ push_args ^  push_n ^ op ^ shift ^ run_code ^ case_error in
      Printf.sprintf "; ApplicTP ->\n %s ; <- ApplicTP\n" output
  ;;
end;;

