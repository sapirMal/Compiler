#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception DEBUG;;
exception S_comment_fail;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list

                                    (*to delete *)

  val nt_integer : int -> char list -> number * char list
  (* val nt_exp: char list -> number * char list
  val nt_scientific_notation: char list -> number * char list
  val nt_radix_notation: char list -> number * char list *)
  (* val nt_float: char list -> number * char list   *)
  (* val string_to_list: string -> char list
  val nt_delimiters: char list -> char * char list *)
  (* val nt_natural: char list -> int * char list *)
  (* val range_10_to_36: (char list -> char list * char list) list
  val nt_radix_base: char list -> int * char list
  val nt_digit_radix: char list -> int * char list
  val nt_float_radix_natural: int -> (char list -> int * char list) -> char list -> float * char list
  val nt_line_com: char list -> char * char list
  val nt_symbol_helper: char list -> sexpr * char list
  val nt_sexpr_comments: char list -> char * char list *)
    
  (* val nt_number : char list -> sexpr * char list
  val nt_boolean: char list -> sexpr * char list
  val nt_char: char list -> sexpr * char list
  val nt_string_meta_char: char list -> char * char list
  val nt_string: char list -> sexpr * char list
  val nt_symbol: char list -> sexpr * char list *)
  val nt_list: char list -> sexpr * char list
  val nt_dotted_list: char list -> sexpr * char list
  (* val nt_quoted: char list -> sexpr * char list
  val nt_quasi_quoted: char list -> sexpr * char list
  val nt_unquoted_spliced: char list -> sexpr * char list
  val nt_unquoted: char list -> sexpr * char list
  val nt_tagged_sexpr: char list -> sexpr * char list
  val nt_tag_ref: char list -> sexpr * char list *)
  val nt_sexpr: char list -> sexpr * char list

end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;



let ascii_0 = 48;;


let list_to_string_ci s =
  String.concat "" (List.map (fun ch -> String.make 1 (lowercase_ascii ch)) s);;

(* -------------------------------------------------------------------------------- *) 

(* TaggedSexpr parsers *)

let nt_sulamit = char '#';;
let nt_equal_sign = char '=';;              

(* quotes  *)

let nt_quasi_quote = char '`';;
let nt_unquote_spliced = word ",@";;
let nt_unquote = char ',';;

(* delimiters *)
  
let nt_left_paren = char '(';;
let nt_right_paren = char ')';;
let nt_quote = char '\'';;
let nt_quotes = char '\"';;
let nt_left_paren2 = char '{';;
let nt_right_paren2 = char '}';;
let nt_left_paren3 = char '[';;
let nt_right_paren3 = char ']';;
let nt_whitespace = range '\x00' '\x20' ;;
let delimiters_list = [nt_left_paren;nt_right_paren;nt_quote;nt_quotes
                       ;nt_left_paren2;nt_right_paren2;nt_left_paren3;nt_right_paren3;nt_whitespace];;

(* boolean *)
                  
let nt_true = word_ci "#t";;

let nt_false = word_ci "#f";;

(* char *)

let nt_char_prefix = word "#\\";;

let nt_named_char_list = [("newline", 10);
                          ("nul", 0);
                          ("page", 12);
                          ("return", 13);
                          ("space", 32);
                          ("tab", 9)];;

let nt_visible_chars = range (char_of_int 33) (char_of_int 127);;

(* number *)

(* Digit -> (0|...|9) *)
let nt_digit_0_to_9 =
  pack (const (fun ch -> ch >= '0' && ch <= '9'))
    (fun e -> (int_of_char e) - ascii_0);;

let nt_plus =
  (char '+');;

let nt_minus =
  (char '-');;

let nt_number_sign =
  pack (maybe (disj nt_plus nt_minus))
    (fun sign ->
        match sign with
     |Some '-' -> -1
     |_ -> 1);;

let nt_dot = char '.';;


let range_10_to_36 = List.map (fun num -> word(num))
                       ["10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"20";"21";"22";"23";"24";
                        "25";"26";"27";"28";"29";"30";"31";"32";"33";"34";"35";"36"];;

let nt_radix_base = disj
                      (pack (disj_list range_10_to_36)
                         (fun res -> int_of_string (list_to_string res)))
                      (pack (range '2' '9')
                               (fun c -> (int_of_char c) - ascii_0));;

let nt_digit_radix =
  disj (pack (range_ci 'A' 'Z')
             (fun e -> (int_of_char (lowercase_ascii e)) - 87))
    (nt_digit_0_to_9);;

(* string *)

let nt_meta_chars_list = [("\\r", 13); 
                          ("\\n", 10); 
                          ("\\t", 9);
                          ("\\f", 12); 
                          ("\\", 92); 
                          ("\\\"", 34)];;

let nt_string_literal_char = diff (nt_any) (disj (char '\\') (char '\"'));;

(* symbol *)

let nt_symbol_char_list = [range 'A' 'Z';
                           range 'a' 'z';
                           range '0' ':';
                           range '<' '?';
                           char '/';
                           char '$';
                           char '!';
                           range '*' '+';
                           char '-';
                           range '^' '_'];;

let nt_symbol_char = disj_list nt_symbol_char_list;;


(* --------------------------------------SEXPR-------------------------------------------- *)

let i = {contents = 0};;

let rec read_sexpr string = 
let (sexpr, rest) = nt_sexpr (string_to_list string) in
(match rest with
| [] -> sexpr
| _ -> raise X_no_match)
  
and read_sexprs string = 
  let (sexprs, rest) = (star nt_sexpr (string_to_list string)) in
  sexprs

and follow parser =
  let disj_delimiters = disj_list delimiters_list in
  let non_delimiters = diff nt_any disj_delimiters in
  let sexpr = not_followed_by parser non_delimiters in
  sexpr

and nt_sexpr s = 
  let nt_sexpr_list = [nt_boolean; nt_char; 
                       follow nt_number; nt_string; 
                       follow nt_symbol; nt_nil;
                       nt_list_or_dotted; nt_quoted; nt_quasi_quoted; 
                       nt_unquoted_spliced; nt_unquoted;
                       nt_tagged_sexpr; nt_tag_ref] in
  let sexpr = disj_list nt_sexpr_list in
  let sexpr = skipper sexpr in
  sexpr s
 

(* --------------------------------------LINE COMMENTS------------------------------------ *) 

and nt_line_com s = 
  let nt_semicolon = char ';' in
  let nt_end_line = char '\n' in
  let end_of_input = pack nt_end_of_input (fun _ -> '\n') in 
  let nt_end = disj nt_end_line end_of_input in
  let any_until_n = caten (star (diff nt_any nt_end)) nt_end in
  let line_com = caten nt_semicolon any_until_n in
  let line_com = pack line_com (fun e -> ' ') in 
  line_com s

(* --------------------------------------SEXPR COMMENT------------------------------------ *)

and nt_sexpr_comments s =
  let nt_prefix_s_comment = word "#;" in
  let nt_s_comment = caten nt_prefix_s_comment nt_sexpr in
  let nt_s_comment = pack nt_s_comment (fun e -> ' ') in
  nt_s_comment s

(* ------------------------------------------DELIMITERS----------------------------------- *)

and skipper parser s = 
  let skipping_list = [nt_whitespace; nt_line_com; nt_sexpr_comments] in
  let nt_skipper = disj_list skipping_list in
  let nt_skipper = star nt_skipper in
  let nt_skipper = caten nt_skipper (caten parser nt_skipper) in
  let nt_skipper = pack nt_skipper (fun (_,(exp,_)) -> exp) in
  nt_skipper s

(* ------------------------------------------NIL------------------------------------------ *)
and nt_nothing s = (Nil, s)

and nt_nil s =
  let niller = caten nt_left_paren (caten (skipper nt_nothing) nt_right_paren) in
  let niller = pack niller (fun _ -> Nil) in
  niller s

(* --------------------------------------BOOLEAN------------------------------------------ *) 
                        
(* Boolean -> #f | #t *)

and nt_boolean s = 
  let nt_t = pack nt_true (fun e -> Bool(true)) in
  let nt_f = pack nt_false (fun e -> Bool(false)) in
  let nt_bool = disj nt_t nt_f in
  nt_bool s

(* ------------------------------------CHAR----------------------------------------------- *)
                    
and named_char_to_char parser (name, ascii) =
  let named_to_char = parser name in
  let named_to_char = pack named_to_char (fun _ -> (char_of_int ascii)) in
  named_to_char

and nt_named_char s =
  let named_list = List.map (named_char_to_char word_ci) nt_named_char_list in
  let named_list = disj_list named_list in
  named_list s

(* Char -> Char_Prefix (Visible_Simple_Char | Named_Char )  *)

and nt_char s =
  let char_types = disj nt_named_char nt_visible_chars in
  let sexpr = caten nt_char_prefix char_types in
  let sexpr = pack sexpr (fun (_,e) -> Char(e)) in
  sexpr s

(* ---------------------------------------NUMBER------------------------------------------ *) 

(* Natural -> Digit+ *)

and nt_natural base s =
  let nat_num = 
    if base = 10
    then plus nt_digit_0_to_9
    else plus nt_digit_radix in
  let nat_num = pack nat_num (fun list -> List.fold_left (fun a b -> a * base + b) 0 list) in
  nat_num s

(* Integer -> (+|-)? Natural *)

and nt_integer base s =
  let int_num = caten nt_number_sign (nt_natural base) in
  let int_num = pack int_num (fun (sign, num) -> Int(sign * num)) in
  int_num s

(* Float -> Integer.Natural *)  
and nt_natural_float base s =
  let nat_num = 
    if base = 10
    then plus nt_digit_0_to_9
    else plus nt_digit_radix in
  let basef = 1.0 /. (float_of_int base) in
  let nat_num = pack nat_num 
  (fun list -> (List.fold_right 
                  (fun elem acc -> 
                      let e = (float_of_int elem) in
                      acc *. basef +. e)
                  list 0.0) *. basef) in
  nat_num s



and nt_float base s = 
  let float_num1 = caten nt_number_sign (nt_integer base) in
  let float_num2 = caten nt_dot (nt_natural_float base) in
  let float_num = caten float_num1 float_num2 in
  let float_num = pack float_num 
    (fun ((sign, int),(_,frac)) -> 
    (match int with
    | Int(num) ->
        (* let frac = {contents = (float_of_int nat)} in
        while !frac >= 1.0 do
          frac := !frac *. (1.0 /. (float_of_int base)) ;
        done; *)
        let float = (float_of_int sign) *. ((float_of_int num) +. frac) in
        Float(float)
    | _ -> raise X_no_match
    )) in
  float_num s

(* Scientific -> Number E\e Integer *)

and nt_scientific_notation s =
  let scientific_1 = caten (disj (nt_float 10) (nt_integer 10)) (char_ci 'E') in
  let scientific_2 = caten nt_number_sign (nt_integer 10) in
  let scientific = caten scientific_1 scientific_2 in
  let scientific = pack scientific 
    (fun ((num, _),(sign, int)) ->
      (match int with
      | Int(exp) ->
        let exp = 
          if sign == -1
          then 0.1 ** (float_of_int exp)
          else 10.0 ** (float_of_int exp) in
        (match num with
        | Float(x) -> 
          Float(x *. exp)
        | Int(x) ->
          Float((float_of_int x) *. exp)
        )
      | _ -> raise X_no_match
      )
    ) in
  scientific s

(* Radix -> #base R\r Float | Integer *)

and nt_radix_notation s =
  let radix = caten nt_sulamit nt_radix_base in
  let radix = caten radix (char_ci 'R') in
  let (base, rest) = pack radix (fun ((_,base),_) -> base) s in
  let (head, rest) as radix = disj (nt_float base) (nt_integer base) rest in
  radix

(* Number -> Integer | Float *)

and nt_number s =
  let num_list = [nt_radix_notation; nt_scientific_notation; (nt_float 10); (nt_integer 10)] in
  let num_list = disj_list num_list in
  let num_list = pack num_list (fun num -> Number(num)) in
  num_list s

 (* --------------------------------------STRING------------------------------------------ *) 

(* String Char -> (String Literal Char) | (String Meta Char) *)

and nt_string_char s = 
  let meta_chars = List.map (named_char_to_char word_ci) nt_meta_chars_list in
  let meta_chars = disj_list meta_chars in
  let string_char = disj nt_string_literal_char meta_chars in
  string_char s

(* String -> " <String Char>* " *)

and nt_string s =
  let string_chars = star nt_string_char in
  let sexpr_string = caten nt_quotes string_chars in
  let sexpr_string = caten sexpr_string nt_quotes in
  let sexpr_string = pack sexpr_string (fun ((_,sexp),_) -> String(list_to_string sexp)) in
  sexpr_string s

 (* ----------------------------------------SYMBOL---------------------------------------- *) 


(* Symbol -> (Symbol Char)+ *)  

and nt_symbol s =
  let sexpr_symbol = plus nt_symbol_char in
  let sexpr_symbol = pack sexpr_symbol (fun e -> Symbol(list_to_string_ci e)) in
  sexpr_symbol s

(* --------------------------------------LIST--------------------------------------------- *) 

and make_pairs final lst =
  (match lst with
    | [] -> final
    | e::rest -> Pair(e, make_pairs final rest)
  )

and nt_list_or_dotted s =
  let sexprs = plus nt_sexpr in
  let sexprs = caten sexprs (maybe (caten nt_dot nt_sexpr)) in
  let sexprs = caten nt_left_paren sexprs in
  let sexprs = caten sexprs nt_right_paren in
  let sexprs = pack sexprs 
    (fun ((_,(sexprs, maybe_dot)),_) ->
      match maybe_dot with
      | Some(dot, sexpr) -> (make_pairs sexpr sexprs)
      | None -> (make_pairs Nil sexprs)
    ) in
  sexprs s

(* List -> ( <sexpr>* )  *)

and nt_list s =
  let sexprs_list = star nt_sexpr in
  let sexprs_list = pack sexprs_list (make_pairs Nil) in
  let sexpr_list = caten nt_left_paren sexprs_list in
  let sexpr_list = caten sexpr_list nt_right_paren in
  let sexpr_list = pack sexpr_list (fun ((_,list),_) -> list) in
  sexpr_list s

(* --------------------------------------DOTTEDLIST--------------------------------------- *)        

and nt_dotted_list s =
  let sexprs_dotted = plus nt_sexpr in
  let sexpr_dotted = caten nt_left_paren sexprs_dotted in
  let sexpr_dotted = caten sexpr_dotted nt_dot in
  let sexpr_dotted = caten sexpr_dotted nt_sexpr in
  let sexpr_dotted = caten sexpr_dotted nt_right_paren in
  let sexpr_dotted = pack sexpr_dotted (fun ((((_, sexprs),_),sexpr),_) -> make_pairs sexpr sexprs) in
  sexpr_dotted s

(* --------------------------------------QUOTED------------------------------------------- *)        

and nt_quoted s = 
  let sexpr_quote = caten nt_quote nt_sexpr in
  let sexpr_quote = pack sexpr_quote (fun (_,expr) -> Pair(Symbol("quote"), Pair(expr, Nil))) in
  sexpr_quote s

and nt_quasi_quoted s = 
  let sexpr_qquote = caten nt_quasi_quote nt_sexpr in
  let sexpr_qquote = pack sexpr_qquote (fun (_,expr) -> Pair(Symbol("quasiquote"), Pair(expr, Nil))) in
  sexpr_qquote s

and nt_unquoted_spliced s = 
  let sexpr_uqs = caten nt_unquote_spliced nt_sexpr in
  let sexpr_uqs = pack sexpr_uqs (fun (_,expr) -> Pair(Symbol("unquote-splicing"), Pair(expr, Nil))) in
  sexpr_uqs s

and nt_unquoted s = 
  let sexpr_uq = caten nt_unquote nt_sexpr in
  let sexpr_uq = pack sexpr_uq (fun (_,expr) -> Pair(Symbol("unquote"), Pair(expr, Nil))) in
  sexpr_uq s

(* --------------------------------------TAGGEDEXPR--------------------------------------- *)

and check_legal_tag name sexpr =
  (match sexpr with
    |Pair(a,b) ->  
    Pair((check_legal_tag name a),(check_legal_tag name b))
    | TaggedSexpr(a,b) ->
      if (a = name)
      then raise X_this_should_not_happen
      else TaggedSexpr(a, check_legal_tag name b)            
    |_ -> sexpr)

and nt_tagged_sexpr s =
  let sexpr_tagged_sexpr = caten nt_sulamit nt_left_paren2 in
  let sexpr_tagged_sexpr = caten sexpr_tagged_sexpr nt_symbol in
  let sexpr_tagged_sexpr = caten sexpr_tagged_sexpr nt_right_paren2 in
  let sexpr_tagged_sexpr = pack sexpr_tagged_sexpr 
      (fun ((_,e),_) -> 
        (match e with
          | Symbol(name) -> name
          | _ -> raise X_no_match
        )
      ) in
  let sexpr_tagged_sexpr = caten sexpr_tagged_sexpr nt_equal_sign in
  let sexpr_tagged_sexpr = caten sexpr_tagged_sexpr nt_sexpr in
  let sexpr_tagged_sexpr = pack sexpr_tagged_sexpr 
      (fun ((name,_),expr) ->
        (name,expr)
      ) in
  let sexpr_tagged_sexpr = pack sexpr_tagged_sexpr
      (fun (name, expr) ->
        let sexpr = check_legal_tag name expr in
        TaggedSexpr(name, sexpr)
      ) in
  sexpr_tagged_sexpr s

(* --------------------------------------TAGREF------------------------------------------- *)

and nt_tag_ref s =
  let sexpr_tag = caten nt_sulamit nt_left_paren2 in
  let sexpr_tag = caten sexpr_tag nt_symbol in
  let sexpr_tag = caten sexpr_tag nt_right_paren2 in
  let sexpr_tag = pack sexpr_tag 
      (fun ((_,e),_) -> 
        (match e with
          | Symbol(name) -> TagRef(name)
          | _ -> raise X_no_match
        )
      ) in
  sexpr_tag s

;; 
end;; (* struct Reader *)

