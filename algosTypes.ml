open Printf

let ($) f x = f x
let (<.>) f g x = f (g x)

module VarSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = string
  end )

 type expr = 
   One
 | Zero
 | Var of string
 | Inv of expr
 | Plus of expr * expr
 | Mult of expr * expr

type boolean = 
   Top
 | Bot
 | Lit of string
 | Neg of boolean
 | And of boolean * boolean
 | Or of boolean * boolean
 | Imp of boolean * boolean
 | Bicon of boolean * boolean

let rec vars1 expr varset =
  match expr with
    Var s -> VarSet.add s varset
  | Inv e1 -> vars1 e1 varset
  | Plus (e1,e2) -> VarSet.union (vars1 e1 varset) (vars1 e2 varset)
  | Mult (e1,e2) -> VarSet.union (vars1 e1 varset) (vars1 e2 varset)
  | _ -> VarSet.empty

let vars expr = vars1 expr VarSet.empty

let varset2string varset = VarSet.fold (fun element seed -> seed ^ " " ^ element) varset ""

let rec expr2string expr =
  match expr with
    One -> "1"
  | Zero -> "0"
  | Var v -> v
  | Inv expr1 -> "(" ^ "−" ^ (expr2string expr1) ^ ")"
  | Plus (expr1,expr2) -> "(" ^ (expr2string expr1) ^ " + " ^ (expr2string expr2) ^ ")"
  | Mult (expr1,expr2) -> "(" ^ (expr2string expr1) ^ " × " ^ (expr2string expr2) ^ ")"

let rec boolean2string boolean =
  match boolean with
    Top -> "⊤"
  | Bot -> "⊥"
  | Lit v -> v
  | Neg boolean1 -> "(" ^ "¬" ^ (boolean2string boolean1) ^ ")"
  | And (boolean1,boolean2) ->
    "(" ^ (boolean2string boolean1) ^ " ∧ " ^ (boolean2string boolean2) ^ ")"
  | Or (boolean1,boolean2) ->
    "(" ^ (boolean2string boolean1) ^ " ∨ " ^ (boolean2string boolean2) ^ ")"
  | Imp (boolean1,boolean2) ->
    "(" ^ (boolean2string boolean1) ^ " ⇒ " ^ (boolean2string boolean2) ^ ")"
  | Bicon (boolean1,boolean2) ->
    "(" ^ (boolean2string boolean1) ^ " ⇔ " ^ (boolean2string boolean2) ^ ")"

let print_expr expr = printf "%s\n" (expr2string expr)
let print_boolean boolean = printf "%s\n" (boolean2string boolean)

let rec boolean2expr b =
  match b with
    Top -> One
  | Bot -> Zero
  | Lit s -> Var s
  | Neg b1 -> Plus (One, Inv (boolean2expr b1))
  | And (b1,b2) -> (* (a * b) *)
    Mult ((boolean2expr b1), (boolean2expr b2))
  | Or (b1,b2) -> (* a + b + -(a * b) *)
    Plus ((boolean2expr b1), 
          (Plus ((boolean2expr b2), Inv (Mult ((boolean2expr b1),(boolean2expr b2))))))
  | Imp (b1,b2) -> (* 1 + -a + (a * b) *)
    Plus (One, 
         (Plus (Inv (boolean2expr b1), (Mult ((boolean2expr b1),(boolean2expr b2))))))
  | Bicon (b1,b2) -> (* (1 + -x1 + -x2 + (x1 * x2) + (x1 * x2)) *)
    Plus (One,
          Plus (Inv (boolean2expr b1),
         (Plus (Inv (boolean2expr b2),
         (Plus (Mult ((boolean2expr b1),(boolean2expr b2)),
               (Mult ((boolean2expr b1),(boolean2expr b2)))))))))


module rec Term : sig
  type t = 
    C1
  | C0
  | V of string
  | I of Term.t
  | P of int BlockMap.t | M of int BlockMap.t
  val compare: t -> t -> int
end
  = struct
    type t = 
    C1
  | C0
  | V of string
  | I of Term.t
  | P of int BlockMap.t | M of int BlockMap.t
    let compare = Pervasives.compare
  end
and BlockMap : Map.S with type key = Term.t
  = Map.Make(Term)

let rec term2string a = 
  match a with
    Term.C1 -> "1"
  | Term.C0 -> "0"
  | Term.V s -> s
  | Term.I term -> "-" ^ (term2string term)
  | Term.P map -> "(" ^ (BlockMap.fold (f " + ") map "") ^ ")"
  | Term.M map -> "(" ^ (BlockMap.fold (f " * ") map "") ^ ")"
and f op key elt acc =
  match key with
    Term.C1 -> if acc = "" then "1" else acc ^ op ^ "1" 
  | Term.C0 -> if acc = "" then "0" else acc ^ op ^ "0"
  | Term.V s -> if acc = "" then s else  acc ^ op ^ s 
  | Term.I arith -> 
    if acc = "" then 
      "-" ^ (term2string arith) 
    else 
     acc ^ op ^  "-" ^ (term2string arith)
  | Term.P set' -> 
    if acc = "" then 
      "(" ^ (BlockMap.fold (f " + ") set' "") ^ ")" 
    else 
     acc ^ op ^ "(" ^ (BlockMap.fold (f " + ") set' "") ^ ")" 
  | Term.M set' -> 
    if acc = "" then 
      "(" ^ (BlockMap.fold (f " * ") set' "") ^ ")" 
    else
     acc ^ op ^ "(" ^ (BlockMap.fold (f " * ") set' "") ^ ")"

let print_term t = printf "%s\n" (term2string t)

(*
let badd term block =
  match term with
    Term.I t1 -> 
      if BlockMap.mem t1 block then
	BlockMap.
*)

let rec expr2term expr = 
  match expr with
    One -> Term.C1
  | Zero -> Term.C0
  | Var s -> Term.V s
  | Inv expr -> Term.I (expr2term expr)
  | Plus (e1,e2) -> 
    let block =  BlockMap.singleton (expr2term e1) 1 in
    let block' = BlockMap.add (expr2term e2) 1 block in
    Term.P block'
  | Mult (e1,e2) -> 
    let block =  BlockMap.singleton (expr2term e1) 1 in
    let block' = BlockMap.add (expr2term e2) 1 block in
    Term.M block'

let x = (BlockMap.singleton (Term.V "a") 1);;
let x =  (BlockMap.add (Term.V "b") 1 x);;
let x1 = Term.M (BlockMap.add (Term.V "b") 1 x);;
let x2 = BlockMap.add (Term.V "c") 1 x
let y = (BlockMap.singleton x1 1)
let y = BlockMap.add (Term.V "c") 1 y
let y = BlockMap.add (Term.I (Term.M x2)) 1 y
let y1 = Term.P y
let z = BlockMap.singleton y1 1
let z = BlockMap.add (Term.V "d") 1 z
let z1 = Term.M z



(*
(((a × b) + (c + (−((a × b) × c)))) × d)

M[
  P[
    M[a;b];
    c;
    I[M[a;b;c]]
   ];
  d
 ]

((a × b) + c + −(a × b × c)) × d
*)
