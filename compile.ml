(* import the relevant ocaml libraries *)
open Printf
open Sexplib.Sexp
module Sexp = Sexplib.Sexp


(* DEFINE TYPES FOR 331 LANGUAGE *)
type op = 
   | Inc
   | Dec 

type binop = 
   | Plus
   | Minus
   | Times

type comp = 
   | Eq
   | Less
   | Great

type expr = 
   | ENum of int
   (* variable access *)
   | EBool of bool 
   | EId of string 
   | EOp of op * expr
   | EBinop of binop * expr * expr
   (* variable declaration *)
   | ELet of string * expr * expr list
   (* condition, true block, false block *) 
   | EIf of expr * expr * expr
   (* comparing two expressions *) 
   | EComp of comp * expr * expr 
   (* applying a function to two expressions *)
   | EApp of string * expr * expr 
   (* setting a variable to a value *)
   | ESet of string * expr
   (* while loop with condition and list of expressions *)
   | EWhile of expr * expr list
   (* make a pair *)
   | EPair of expr * expr
   (* access first value of pair *)
   | EFst of expr
   (* access second value of pair *)
   | ESnd of expr

(* (def (f x y) (+ x y)) *)
type def = | DFun of string * string * string * expr  

(* a program is a list of defs followed by an expresssion *)
type prog = def list * expr 

(* --------------------------------------------------------*)

(* environment for variables *)
type tenv = (string * int) list 

(* DEFINE TYPES FOR ASSEMBLY *)

(* registers *)
type reg = 
   (* scratch space and result *)
   | Rax
   (* stack pointer *)
   | Rsp
   (* temp storage *)
   | Rbx 
   (* heap pointer *)
   | Rdi 

(* arguments to instructions like add or mov *)
type arg = 
   | Const of int
   | Reg of reg
   | RegOffset of int * reg
   | Lab of string

(* type for assembly instructions *)
type instr = 
   (* mov: source, dest *)
   | IMov of arg * arg
   (* add: to-add, dest *)
   | IAdd of arg * arg 
   (* sub: to-sub, dest *)
   | ISub of arg * arg
   (* mul: to-mul, dest *)
   | IMul of arg * arg
   (* cmp: to_cmp, dest *)
   | ICmp of arg * arg 
   (* unconditional jmp to some label *)
   | IJmp of string 
   (* jump if cmp flag is equal *)
   | IJe of string 
   (* jump if cmp flag is not equal *)
   | IJne of string 
   (* jump if flag is set to less or equal *)
   | IJle of string
   (* jump if flag is set to greater or equal *)
   | IJge of string 
   (* the actual label *)
   | ILab of string 
   (* return *)
   | IRet 

(* -----------------------------------------------------------*)

(* HELPER FUNCTIONS TO TURN ASSEMBLY INTO STRINGS *)

(* turn a register into a string *)
let reg_to_string (r: reg) : string = 
   match r with
   | Rax -> "%rax"
   | Rsp -> "%rsp"
   | Rbx -> "%rbx"
   | Rdi -> "%rdi"
;;

(* turn an argument to an instruction into a string *)
let arg_to_string (a: arg) : string = 
   match a with 
   | Const(n) -> sprintf "$%d" n 
   | Reg(r) -> reg_to_string r 
   | RegOffset(n,r) -> sprintf "%d(%s)" n (reg_to_string r) 
   | Lab(s) -> sprintf "$%s" s 
;;

(* turn an instruction into a string *)
let instr_to_string (i:instr) : string = 
   match i with 
   | IMov(s,d) -> sprintf "mov %s, %s" (arg_to_string s) (arg_to_string d)
   | IAdd(to_add, dest) -> sprintf "add %s, %s" (arg_to_string to_add) (arg_to_string dest) 
   | ISub(to_sub, dest) -> sprintf "sub %s, %s" (arg_to_string to_sub) (arg_to_string dest) 
   | IMul(to_mul, dest) -> sprintf "imul %s, %s" (arg_to_string to_mul) (arg_to_string dest)
   | ICmp(to_cmp, dest) -> sprintf "cmp %s, %s" (arg_to_string to_cmp) (arg_to_string dest) 
   | IJmp(label) -> sprintf "jmp %s" label 
   | IJe(label) -> sprintf "je %s" label 
   | IJne(label) -> sprintf "jne %s" label
   | IJle(label) -> sprintf "jle %s" label
   | IJge(label) -> sprintf "jge %s" label 
   | ILab(label) -> sprintf "%s:" label 
   | IRet -> "ret"
;;

(* converts list of instructions into one nice assembly string *)
let rec instrs_to_string (is: instr list) : string = 
   match is with 
   | [] -> ""
   | hd :: tl -> (instr_to_string hd) ^ "\n  "  ^ (instrs_to_string tl) 
;;

(* global counter used to make fresh labels *)
(* the counter is a mutable integer -- it is a REFERENCE *)
let counter : int ref = ref 0;;

(* helper function to generate unique labels *)
let new_label (s: string) : string =

    (* get the current value of the counter *) 
    let cur : int  = !counter in  

    (* update the counter -- need ; since this is non-functional code *)
    counter := cur + 1;

    (* generate label string -- example: else3 *)
    sprintf "%s%d" s cur
;;

(* ---------------------------------------------------------------*)
(* find the first occurence of a var in the env *)
let rec find (env: tenv) (x: string) : int option = 
  match env with 
  | [] -> None
  | (s, i) :: tl -> if (s = x) then Some(i) else find tl x
;;

(* find a function name in a list of function definitions *)
let rec find_def (defs: def list) (x: string) : def option = 
  match defs with 
  | [] -> None
  | (DFun(fname, arg1, arg2, body)) :: tl -> 
       if fname = x then Some(DFun(fname, arg1, arg2, body))
       else find_def tl x 
;;

(* for stack math *)
let stackloc (i: int) : arg = RegOffset(i * -8,Rsp);;

(* ---------------------------------------------------------------*)
(* THE PARSER *)

(* wrapper for int_of_string ugliness for the parser *)
let int_of_string_opt (s: string) : int option = 
    try 
       Some(int_of_string s)
    with 
       Failure _ -> None 
;;

(* parser: string ---> Sexp ----> expr *)
let rec sexp_to_expr (se: Sexp.t) : expr = 
    match se with
    (* new base cases for the bool *) 
    | Atom("true") -> EBool(true)
    | Atom("false") -> EBool(false)
    | Atom(s) -> (match int_of_string_opt s with 
                 | Some(i) -> ENum(i)
                 | None -> EId(s))

    (* matching on a list of two elements *)
    (* matching on a case of the sexp and INTO the list *)
    | List([Atom("inc"); stuff]) -> EOp(Inc, sexp_to_expr stuff) 
    | List([Atom("dec"); stuff]) -> EOp(Dec, sexp_to_expr stuff) 
    | List([Atom("if"); se1; se2; se3]) -> 
                    EIf(sexp_to_expr se1, sexp_to_expr se2, sexp_to_expr se3)
    | List([Atom("="); se1; se2]) -> EComp(Eq, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("<"); se1; se2]) -> EComp(Less, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom(">"); se1; se2]) -> EComp(Great, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("+"); se1; se2]) -> EBinop(Plus, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("-"); se1; se2]) -> EBinop(Minus, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("*"); se1; se2]) -> EBinop(Times, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("set"); Atom(s); arg]) -> ESet(s,sexp_to_expr arg)
    | List([Atom("pair"); se1; se2]) -> EPair(sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("fst"); stuff]) -> EFst(sexp_to_expr stuff)
    | List([Atom("snd"); stuff]) -> ESnd(sexp_to_expr stuff)
    | List(Atom("while") :: arg1 :: body_list)  ->
          (* body_list is a list of S-expressions *)
          EWhile(sexp_to_expr arg1, seq_helper body_list)
    | List(Atom("let") :: List([Atom(x);value]) :: bodylist) ->
          (* body is now a list of S-expressions *)
          ELet(x,sexp_to_expr value, seq_helper bodylist)
    (* this case has to be at the end so it doesn't always match *)
    | List([Atom(f); arg1; arg2]) -> EApp(f, sexp_to_expr arg1, sexp_to_expr arg2)  
    | _ -> failwith "Parse Error: Illegal Expression"

(* takes list of sexps that make up the body of the let and make them into an list of expr *)
    and seq_helper (body_list: Sexp.t list) : expr list =
        match body_list with
        (* list of expressions should not be empty *)
        | [] -> failwith "Empty expression list"
        | [se] -> [sexp_to_expr se]
        | hd :: tl -> (* convert the head to an exp and cons to the rest of the list *)
                     (sexp_to_expr hd) :: seq_helper tl
;;


(* turn an sexp into a function def *)
let sexp_to_def (se: Sexp.t) : def = 
   match se with 
   | List([Atom("def"); List([Atom(fname); Atom(arg1name); Atom(arg2name)]); body]) -> 
                   DFun(fname, arg1name, arg2name, sexp_to_expr body)
   | _ -> failwith "Parse Error: Illegal Function Definition"  
;;

(* list of sexps should be converted to a program which is a list of defs and one expr *)
let rec parse_program (slist: Sexp.t list) : prog = 
    match slist with 
    | [] -> failwith "Parse Error: Empty Program"
    | [e] -> ([], sexp_to_expr e)
    | hd :: tl -> let defs, body = parse_program tl in 
                    (sexp_to_def hd :: defs, body)  
;;

(* -------------------------------------------------------------------*)

(* THE ACTUAL COMPILER *)

(* instruction generation for expressions *)
(* added a flag to track whether the current expression if it is an EApp could be a tail call *)
let rec expr_to_instrs (e: expr) (env: tenv) (si: int) (defs: def list) (is_tail_call : bool) : instr list  = 
   match e with 
   (* base case *)
   | EBool(b) -> if b then [IMov(Const(1),Reg(Rax))]
                 else [IMov(Const(0),Reg(Rax))]  
   | EId(x) -> (* try to find var in env *)
               (match find env x with 
               | None -> failwith ("Unbound identifier" ^ x)
               | Some(i) ->  (* i is the stack offset of this var *)
                             (* move from rsp-8*i to rax *)
                           [IMov(stackloc i,Reg(Rax))])
   | ENum(n) -> (* need %d is a format string, %% is literally the '%' character *)
                   [IMov(Const(n),Reg(Rax))]
   | EOp(op, e') -> (* recursively generate instructions *) 
                   let rec_call : instr list = expr_to_instrs e' env si defs false in
                   (* append appropriate instruction *)
                    (match op with 
                    | Inc -> rec_call @ [IAdd(Const(1),Reg(Rax))]
                    | Dec -> rec_call @ [ISub(Const(1),Reg(Rax))])

   | EBinop(op, e1, e2) -> binop_helper op e1 e2 env si defs is_tail_call
   
   | ESet(x,e') ->
      (* evaluate instructions for e *)
      let e_instrs  = expr_to_instrs e' env si defs false in
      (* the value we want to set x to is now in rax *)
      (* let's find where x is and move the new value to that spot (we want to clobber) *)
      (match find env x with
      | None -> failwith (sprintf "Unbound variable identifier %s" x)
      | Some(i) -> e_instrs @ [IMov(Reg(Rax), stackloc i)])

   | ELet(x, v, bodylist) ->
      (* get instructions for value  *)
      let v_instrs = expr_to_instrs v env si defs false in
      (* move the value from rax into the place reserved for it *)
      let store = [IMov(Reg(Rax), stackloc si)] in
      (* generate instrs for body, increment si not to clobber *)
      let body_instrs = seq_helper bodylist ((x, si) :: env)  (si + 1) defs false in
      (* combine all of the instructions *)
      v_instrs @ store @ body_instrs

   | EIf(e1,e2,e3) -> if_helper e1 e2 e3 env si defs is_tail_call

   | EComp(comp, e1, e2) ->  cmp_helper comp e1 e2 env si defs is_tail_call

   | EWhile(cond, e') -> while_helper cond e' env si defs is_tail_call

   | EPair(e1, e2) -> (* generate instructions for 1st value *)
                      let e1_instrs = expr_to_instrs e1 env si defs false in
                      (* generate instructions for 2nd value *)
                      (* don't need to increment si because not using stack *)
                      let e2_instrs = expr_to_instrs e2 env si defs false in 
                      (* put 1st value into available heap space *)
                      let store_e1 = [IMov(Reg(Rax), RegOffset(0, Rdi))] in
                      (* put 2nd value into next available heap space *)
                      let store_e2 = [IMov(Reg(Rax), RegOffset(8, Rdi))] in
                      (* save address of pair *)
                      let copy_adr = [IMov(Reg(Rdi), Reg(Rax))] in 
                      (* move rdi forward to so it represents next available heap space *)
                      let update_rdi = [IAdd(Const(16), Reg(Rdi))] in
                      e1_instrs @ store_e1 @ e2_instrs @ store_e2 @ copy_adr @ update_rdi 

   | EFst(e') -> (* evaluate e' -- this better be a pair *)
                 (* if it isn't a pair, the type checker will handle that *)
                 let e'_instrs = expr_to_instrs e' env si defs false in 
                 (* rax stores the address of the start of the pair *)
                 (* move value at the ADDRESS stored in rax into rax *)
                 let mov = [IMov(RegOffset(0, Rax), Reg(Rax))] in
                 e'_instrs @ mov 

   | ESnd(e') -> let e'_instrs = expr_to_instrs e' env si defs false in 
                 (* rax stores the address of the start of the pair *)
                 (* get value at the ADDRESS stored in rax + 8 into rax *)
                 let mov = [IMov(RegOffset(8, Rax), Reg(Rax))] in
                 e'_instrs @ mov 

   | EApp(f,e1,e2) ->  (* check if function is in list of definitions *)
                       (match find_def defs f with 
                       | None -> failwith ("Undefined function " ^ f) 
                       | Some(DFun(fname,arg1name,arg2name,body)) -> 
                       if is_tail_call then
                         (* don't need to do anything to the aftercall label or rsp *)
                         (* first arg can't overwrite stack space that second arg may need *)
                         let e1_instrs = expr_to_instrs e1 env si defs false in 
                         (* temporary storage for arg1 *)
                         (* move it so that arg2 can use the old value of arg1 *)
                         let arg1_temp = [IMov(Reg(Rax), stackloc si)] in
                         (* move arg1 to its final place in rsp-16 so consistent for callee *)
                         (* will do this AFTER we finish handling arg2 *)
                         let arg1_final = [IMov(stackloc si, Reg(Rax)); 
                                          IMov(Reg(Rax), stackloc 2)] in
                         (* don't overwrite 1st arg which is currently stored in si *)
                         let e2_instrs = expr_to_instrs e2 env (si + 1) defs false in
                         (* save arg2 into rsp-24 so it is consistent for callee *)
                         let save_arg2 = [IMov(Reg(Rax), stackloc 3)] in
                         (* jump to actual function code *)
                         let jump = [IJmp(f)] in
                         e1_instrs @ arg1_temp @ e2_instrs @ save_arg2 @ arg1_final @ jump 
                       else 
                       (* deal with arg1, don't clobber rsp and aftercall!  *)
                       let e1_instrs = expr_to_instrs e1 env (si + 2) defs false in
                       (* deal with arg2, don't clobber rsp, aftercall and arg1! *)
                       let e2_instrs = expr_to_instrs e2 env (si + 3) defs false in
                       (* make new label *)
                       let after_string = new_label "after" in
                       let after_label = [ILab(after_string)] in
                       (* move label on stack *)
                       let move = [IMov(Lab(after_string),Reg(Rbx)); 
                                  IMov(Reg(Rbx), stackloc si)] in
                       (* save old rsp *)
                       let save_rsp = [IMov(Reg(Rsp), stackloc (si + 1))] in
                       (* save arguments on stack *)
                       let save_arg1 = [IMov(Reg(Rax), stackloc (si + 2))] in
                       let save_arg2 = [IMov(Reg(Rax), stackloc (si + 3))] in
                       (* reset rsp to point to after_call *)
                       let reset_rsp = [ISub(Const(si * 8), Reg(Rsp))] in
                       (* go to function *)
                       let jump = [IJmp(f)] in
                       (* set rsp back *)
                       let rsp_back = [IMov(stackloc 2, Reg(Rsp))] in
                       move @ save_rsp @ e1_instrs @ save_arg1 @ e2_instrs @ save_arg2 @ 
                       reset_rsp @ jump @ after_label @ rsp_back)


(* go through and generate instructions for each expression in a list *)
and seq_helper (body_list: expr list) (env: tenv) (si: int) (defs: def list) 
   (is_tail_call : bool) : instr list =
        match body_list with
        | [] -> []
        | hd :: tl -> (expr_to_instrs hd env si defs false) @ 
                      (seq_helper tl env si defs is_tail_call)

and binop_helper (op: binop) (e1: expr) (e2: expr) (env: tenv) (si: int) (defs: def list) (is_tail_call : bool) : instr list = 
  (* generate instructions for e1 *)
  let e1_instrs = expr_to_instrs e1 env (si + 1) defs false in 
  (* generate instructions for e1, increment stack index not to clobber  *)
  let e2_instrs = expr_to_instrs e2 env si defs false in 
  (* move the left hand side from rax to temporary space on stack *)
  let e2_store = [IMov(Reg(Rax),stackloc si)] in
  (* evaluate e1 first so subtraction order works *)
  let up_to_op = e2_instrs @ e2_store @ e1_instrs in 
  (* specialize the op depending on what it is *)
  let op_instr = 
    (match op with 
    | Plus -> [IAdd(stackloc si, Reg(Rax))]
    | Minus -> [ISub(stackloc si, Reg(Rax))]
    | Times -> [IMul(stackloc si, Reg(Rax))])
  in up_to_op @ op_instr 
                    
and if_helper (e1: expr) (e2: expr) (e3: expr) (env: tenv) (si: int) (defs: def list) (is_tail_call: bool) : instr list = 
   (* generate condition instrs *)
   let c_instrs = expr_to_instrs e1 env si defs false in
   (* if the if is in tail position, the true/false branches also are *)
   (* generate true instrs *)
   let t_instrs = expr_to_instrs e2 env si defs is_tail_call in
   (* generate false instructions *)
   let f_instrs = expr_to_instrs e3 env si defs is_tail_call in
   (* set up strings for labels *)
   (* generate unique strings like else3 *)
   let else_string = new_label "else" in
   let after_string = new_label "after" in
   (* make labels *)
   let else_label = [ILab(else_string)] in
   let after_label = [ILab(after_string)] in
   (* make jumps *)
   let jmp = [IJmp(after_string)] in
   let je = [IJe(else_string)] in
   (* compare *)
   let cmp = [ICmp(Const(0),Reg(Rax))] in
   (* smush all instrs together *)
   c_instrs @ cmp @ je @ t_instrs @ jmp @ else_label @ f_instrs @ after_label
                                      
and cmp_helper (c: comp) (e1: expr) (e2: expr) (env: tenv) (si: int) (defs: def list) (is_tail_call : bool) : instr list =           
   (* generate instrs for e1 *)
   let e1_instrs = expr_to_instrs e1 env si defs false in 
   (* store e1 *)
   let e1_store = [IMov(Reg(Rax), stackloc si)] in
   (* generate instrs for e2 -> rax *)
   let e2_instrs = expr_to_instrs e2 env (si + 1) defs false in 
   (* comp *)
   let cmp = [ICmp(Reg(Rax), stackloc si)] in
   (* true instr *)
   let t = [IMov(Const(1), Reg(Rax))] in
   (* false instr *)
   let f = [IMov(Const(0), Reg(Rax))] in 
   (* make else label *)
   let else_string = new_label "else" in 
   let else_label = [ILab(else_string)] in
   (* make after label *)
   let after_string = new_label "after" in 
   let after_label = [ILab(after_string)] in 
   (* unconditional jump to skip over false instrs *)
   let jmp = [IJmp(after_string)] in 
   (* smush together some instrs *)
   let before_jump = e1_instrs @ e1_store @ e2_instrs @ cmp in
   let after_jump = t @ jmp @ else_label @ f @ after_label in
   (* different jumps based on what comparison it is *)
   (* jumping when the comparison is FALSE *)
   (match c with 
   | Eq -> before_jump @ [IJne(else_string)] @ after_jump 
   | Less -> before_jump @ [IJge(else_string)] @ after_jump
   | Great -> before_jump @ [IJle(else_string)] @ after_jump)
   (* could also do this which is a little cleaner: *)
   (* let right_jump = 
        (match c with 
        | Eq -> [IJne(else_string)]
        | Less -> [IJGe(else_string)] 
        | Great -> [IJLe(else_string)])
      in before_jump @ right_jump @ after_jump
   *)

and while_helper (cond: expr) (e': expr list) (env: tenv) (si: int) (defs: def list)
  (is_tail_call : bool) : instr list =
  (* first let's get the instructions for the condition *)
  let cond_instrs = expr_to_instrs cond env si defs false in
  (* let's do a compare with condition result which is in rax *)
  let compare = [ICmp(Const(0),Reg(Rax))] in
  (* let's make some labels *)
  let after = new_label "after" in
  let after_label = [ILab(after)] in
  let cond = new_label "cond" in
  let cond_label = [ILab(cond)] in
  (* we want to jump AFTER loop if compare is equal to 0 *)
  let jump_after = [IJe(after)] in
  (* now let's get the loop body instructions *)
  let body_instrs = seq_helper e' env si defs false in
  (* after done executing, need to jump back to condition ALWAYS *)
  let cond_jump = [IJmp(cond)] in
  (* now let's put it all together *)
  cond_label @ cond_instrs @ compare
     @ jump_after @ body_instrs @ cond_jump @ after_label
;;


(* instruction generation for function definition *)
let compile_def (d: def) (defs: def list) : instr list = 
    match d with 
    | DFun(name, argname1, argname2, body) -> 
       let body_instrs = expr_to_instrs body [(argname1, 2) ; (argname2, 3)] 4 defs true in
          [ILab(name)] @ body_instrs @ [IRet]
;;

(* compile a list of function definitions into one list of instructions *)
let rec compile_defs (defs: def list) (defs_copy : def list) : instr list = 
    match defs with
    | [] -> []
    | hd :: tl -> compile_def hd defs_copy @ compile_defs tl defs_copy
;; 

(* OPTIMIZATION CODE *)


(* function that will eliminate constants in the expression where possible *)
(* implements constant folding and dead code elimination *)
let rec constant_fold (e: expr) : expr = 
  match e with
  (* base cases where folding can happen *)
  | EOp(Inc, ENum(n)) -> ENum(n + 1)
  | EOp(Dec, ENum(n)) -> ENum(n - 1)
  | EOp(op, e') -> EOp(op, constant_fold e')
  | EBinop(Plus, ENum(n1), ENum(n2)) -> ENum(n1 + n2)
  | EBinop(Minus, ENum(n1), ENum(n2)) -> ENum(n1 - n2)
  | EBinop(Times, ENum(n1), ENum(n2)) -> ENum(n1 * n2)
  | EBinop(op, e1, e2) -> EBinop(op, constant_fold e1, constant_fold e2)
  | EComp(Eq, ENum(n1), ENum(n2)) -> EBool(n1 = n2)
  | EComp(Eq, EBool(b1), EBool(b2)) -> EBool(b1 = b2)
  | EComp(Less, ENum(n1), ENum(n2)) -> EBool(n1 < n2)
  | EComp(Great, ENum(n1), ENum(n2)) -> EBool (n1 > n2) 
  | EComp(comp, e1, e2) -> EComp(comp, constant_fold e1, constant_fold e2)
  (* dead code elimination - eliminate a branch of the if/else if possible *)
  | EIf(EBool(true), t, f) -> constant_fold t
  | EIf(EBool(false), t, f) -> constant_fold f 
  | EIf(c,t,f) -> EIf(constant_fold c, constant_fold t, constant_fold f)
  (* eliminate unecessary while loops *)
  | EWhile(EBool(false), b) -> EBool(false)
  (* boring recursive cases *)
  | ESet(x, e') -> ESet(x, constant_fold e')
  | ELet(x,v,blist) -> ELet(x, constant_fold v, List.map constant_fold blist)
  | EWhile(c, blist) -> EWhile(constant_fold c, List.map constant_fold blist)
  | EApp(f, e1, e2) -> EApp(f, constant_fold e1, constant_fold e2)
  (* base cases where no folding can happen *)
  | _ -> e
;;

(* helper function that actually replaces a variable with a constant *)
let rec replace (b: expr) (x: string) (w: expr) : expr = 
   match b with
   (* this is the important base case that actually does the replacing *) 
   | EId(y) -> if x = y then w else b
   | EOp(op, e') -> EOp(op, replace e' x w)
   | EBinop(op, e1, e2) -> EBinop(op, replace e1 x w, replace e2 x w)
   | EComp(comp, e1, e2) -> EComp(comp, replace e1 x w, replace e2 x w)
   | ESet(x, e') -> ESet(x, replace e' x w)
   | EIf(c, t, f) -> EIf(replace c x w, replace t x w, replace f x w)
   | ELet(y, v, blist) -> (* if nested lets bind same var *)
                       (* use of var in value exp of inner let refers to outer var *)
                       (* use of var in body exp of inner let refers to inner var *)
                       (* replace into the value exp but not into the body expression  *)
                       if y = x then ELet(y, replace v x w, blist)  
                       (* if the inner let binds a different var, 
                        * replace in value and body expression *)
                       else ELet(y, replace v x w, List.map (fun e -> replace e x w) blist)
   | EWhile(cond, blist) -> EWhile(replace cond x w, List.map (fun e -> replace e x w) blist)
   | EApp(f, e1, e2) -> EApp(f, replace e1 x w, replace e2 x w)
   | _ -> b
;;

(* implements constant propagation for let binding by replacing the bound var with constant *)
let rec constant_prop (e: expr) : expr = 
    match e with 
    (* only propagate constants into let bindings *)
    | ELet(x, ENum(n), blist) -> (* only replace into let if it has one expression in body *)
                                 if List.length blist = 1 then 
                                 replace (List.hd blist) x (ENum(n)) 
                                 else e 
    | ELet(x, EBool(t), blist) -> (* same as above *)
                                if List.length blist = 1 then 
                                replace (List.hd blist) x (EBool(t))
                                else e 
    (* recursive cases *)
    | EOp(op, e') -> EOp(op, constant_prop e')
    | EBinop(op, e1, e2) -> EBinop(op, constant_prop e1, constant_prop e2)
    | EComp(comp, e1, e2) -> EComp(comp, constant_prop e1, constant_prop e2)
    | EIf(c, t, f) -> EIf(constant_prop c, constant_prop t, constant_prop f)
    | EApp(f, e1, e2) -> EApp(f, constant_prop e1, constant_prop e2)
    | ESet(x, e') -> ESet(x, constant_prop e')
    | ELet(x, v, blist) -> ELet(x, constant_prop v, List.map constant_prop blist)
    | EWhile(c, blist) -> EWhile(constant_prop c, List.map constant_prop blist)
    (* otherwise leave expression unchanged *)
    | _ -> e 
;;


(* checks if expression contains any variables *)
let rec contains_var (e: expr) : bool = 
    match e with 
    (* the important base case *)
    | EId(x) -> true
    | ENum(n) -> false
    | EBool(b) -> false
    | ESet(x, e') -> contains_var e'
    | EOp(op, e') -> contains_var e'
    | EBinop(op, e1, e2) -> (contains_var e1) || (contains_var e2)
    | EComp(comp, e1, e2) -> (contains_var e1) || (contains_var e2)
    | EIf(c, t, f) -> (contains_var c) || (contains_var t) || (contains_var f)
    | EApp(f, e1, e2) -> (contains_var e1) || (contains_var e2) 
    | ELet(x, v, blist) -> (contains_var v) || (contains_var_list blist)
    | EWhile(c, blist) -> (contains_var c) || (contains_var_list blist)

(* applies function above to a list *)
and contains_var_list (elist: expr list) : bool = 
    match elist with 
    | [] -> false
    | hd :: tl -> (contains_var hd) || (contains_var_list tl)
;;

(* checks if a given var is set in a list of expressions *)
let rec is_var_set (elist: expr list) (var: string) : bool = 
    match elist with 
    | [] -> false
    | ESet(x, e') :: tl -> if x = var then true 
                           (* make sure there isn't a set hiding within the set *) 
                           else (is_var_set tl var) || (is_var_set [e'] var)
    | _ :: tl -> is_var_set tl var 
;;

(* find invariants in loop body *)
let rec invariants (elist: expr list) : expr list = 
    match elist with 
    | [] -> []
    (* only lets can be invariants *)
    | ELet(x, v, blist) :: tl  ->  (* does v contain another var *)
                                   (* is x later set in the loop *)
                                   (* also need to check if x is set in the body of the let *)
                                   if (contains_var v) || (is_var_set tl x) || (is_var_set blist x) then
                                      (* this let is not invariant, check rest of loop *)
                                      invariants tl 
                                   (* have found an invariant *)
                                   else ELet(x, v, blist) :: invariants tl  
    | _ :: tl -> invariants tl 
;;

(* remove the let binding associated with a var from loop body *)
let rec remove_let (elist: expr list) (var: string) : expr list = 
    match elist with 
    | [] -> []
    | ELet(x,v,b) :: tl -> if x = var then remove_let tl var
                     (* don't remove this let *)
                     else ELet(x,v,b) :: (remove_let tl var)
    | hd :: tl -> hd :: (remove_let tl var)
;;

(* helper function that actually does the hoisting *)
(* transforms a while into a let *)
let rec hoist_helper (invariants: expr list) (blist: expr list) (c: expr) : expr  = 
    match invariants with 
    | [] -> (* if there are no invariants, stay with original while loop *)
            EWhile(c, blist)
    | ELet(x,v,b) :: tl -> (* remove invariant out of loop body *)
                           let new_body = remove_let blist x in
                           (* make recursive call using new loop body *)
                           let rec_call = hoist_helper tl new_body c in
                           (* convert while into a let and pull invariant out *)
                           ELet(x,v,b @ [rec_call])
    (* should never hit this case *)
    | _ :: tl -> hoist_helper tl blist c 
;;



(* loop invariant hoisting *)
let rec hoist (e: expr) : expr = 
    match e with 
    | EWhile(c, blist) -> (* find invariants in blist *)
                          let invariants = invariants blist in
                          (* hoist them out of loop *)
                          hoist_helper invariants blist c 
    (* recursive cases *)                     
    | ESet(x, e') -> ESet(x, hoist e')
    | EOp(op, e') -> EOp(op, hoist e')
    | EBinop(op, e1, e2) -> EBinop(op, hoist e1, hoist e2)
    | EComp(comp, e1, e2) -> EComp(comp, hoist e1, hoist e2)
    | EIf(c, t, f) -> EIf(hoist c, hoist t, hoist f)
    | EApp(f, e1, e2) -> EApp(f, hoist e1, hoist e2)
    | ELet(x, v, blist) -> ELet(x, hoist v, List.map hoist blist)     
    | _ -> e
;;

(* does one round of optimization *)
(* keeps going while expression is changing *)
(* stops when expression can't be optimized anymore  (fixpoint) *)
let rec improve_expr (e: expr) : expr = 
        (* apply one round of optimization *)
        let optimized =  hoist (constant_prop (constant_fold e)) in
        (* if expression didn't change when optimized, stop improving it *)
        (* this is the base case of the recursion *)
        if optimized = e then e 
        (* otherwise, keep improving the expression by doing another round *)
        else improve_expr optimized 
;;


(* compiles a source program to an x86 string *)
let compile (program: Sexp.t list) : string =
  (* source program converted to function defs and expression *)
  let defs, body  = parse_program program in
  (* optimize body expression *)
  let optimized = improve_expr body in 
  (* generate code for defs *)
  let def_instrs : instr list = compile_defs defs defs in
  (* make def instrs string *)
  let def_str : string = instrs_to_string def_instrs in  
  (* generate code for the AST *)
  let expr_instrs : instr list = expr_to_instrs optimized [] 1 defs false in
  (* add a newline to the generated instructions *)
  let expr_str : string = instrs_to_string (expr_instrs @ [IRet]) in
  (* add the boilerplate to instructions to make it work *)
  sprintf "
  .text
  .globl our_code_starts_here
  %s
  our_code_starts_here:
  %s
  \n" def_str expr_str;;

  (* top-level-function -- code execution starts here *)
  let () =
    (* opens the file passed in on the command line  *)
    let input_file = (open_in (Sys.argv.(1))) in
    (* reads the file in and turns into in a list of sexps *)
    let input_program : Sexp.t list = (Sexp.input_sexps input_file) in
    (* compiles the file to an X86 string *)
    let program : string  = (compile input_program) in
    (* prints the resulting x86 string *)
    printf "%s\n" program
;;
