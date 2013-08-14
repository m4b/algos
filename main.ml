(*
-- ἔνθ᾽ οἵ γ᾽ ἄλγε᾽ ἔχοντες ὑπὸ χθονὶ ναιετάοντες
-- εἵατ᾽ ἐπ᾽ ἐσχατιῇ, μεγάλης ἐν πείρασι γαίης,
-- δηθὰ μάλ᾽ ἀχνύμενοι, κραδίῃ μέγα πένθος ἔχοντες. 

-- and he made them live beneath the wide-pathed earth,
-- where they were afflicted, being set to dwell under the ground,
-- at the end of the earth, at its great borders,
-- in bitter anguish for a long time and with great grief at heart.
-- Hesiod, Theogony, 620
*)

open AlgosTypes
open OldTypes
open Printf

let ver = "2.0"
let ($) f x = f x
let (<.>) f g x = f (g x)

let rec mapExpr v e =
  match e with
    One -> Var v
  | Zero -> Zero
  | Var s when s = v -> Var s
  | Var s -> Mult (Var v, Var s)
  | Inv (Var s) when s = v -> Inv (Var s)
  | Inv (e1) -> Inv (mapExpr v e1)
  | Plus (e1,e2) -> Plus ((mapExpr v e1), (mapExpr v e2))
  | Mult (e1,Var s) as e -> 
    if s = v then 
      e
    else
      Mult (e1, Mult (Var s, Var v))
  | Mult (Var s, e1) as e-> 
    if s = v then 
      e
    else
      Mult (e1, Mult (Var s, Var v))
  | Mult (e1,e2) -> Mult ((mapExpr v e1), (mapExpr v e2))

let rec isProductForm e =
  match e with 
    Var v1 -> true
  | Zero -> true
  | One -> true
  | Inv (Var v1) -> true
  | Inv (Zero) -> true
  | Inv (One) -> true
  | Mult (e1, e2) when isProductForm e1 && isProductForm e2 -> true
  | _ -> false

let rec isSumProductForm e =
  match e with 
    Plus (e1, e2) when isProductForm e1 && isProductForm e2 -> true
  | _ -> false

let rec normalize e =
  match e with
    Mult (Plus (e1,e2), Plus (e3,e4)) -> 
      let e1' = normalize (Mult (e1,e3)) in
      let e2' = normalize (Mult (e1,e4)) in
      let e3' = normalize (Mult (e2,e3)) in
      let e4' = normalize (Mult (e2,e4)) in
      Plus (Plus (e1',e2'), Plus (e3', e4'))
  | Mult (Plus (e1,e2), Mult (e3,e4)) -> 
    let e1' = normalize (Mult (e1, Mult (e3,e4))) in
    let e2' = normalize (Mult (e2, Mult (e3,e4))) in
    Plus (e1',e2')
  | Mult (Var v1, (Mult (Var v2, Var v3) as e1)) as e' ->
    if v1 = v2 || v1 = v3 then
      e1
    else
      e'
  | Mult (Var v1, (Mult (e1, e2))) ->
    let e1' = normalize (Mult (e1, e2)) in
    normalize (Mult (Var v1, e1'))
  | Mult (Var v1, Var v2) as e1 -> 
    if v1 = v2 then Var v1 else e1
  | Mult (Var v1, (Inv (Var v2))) -> 
    if v1 = v2 then (Inv (Var v1)) else Inv (Mult (Var v1, Var v2))
  | Mult ((Inv (Var v2)), Var v1) -> 
    if v1 = v2 then (Inv (Var v1)) else Inv (Mult (Var v1, Var v2))
  | Mult (Var v1, One) -> Var v1
  | Mult (One, Var v1) -> Var v1
  | Mult (Var v1, Zero) -> Zero
  | Mult (Zero, Var v1) -> Zero
  | Plus (e1,e2) -> 
    let e1' = normalize e1 in 
    let e2' = normalize e2 in 
    Plus (e1', e2')
  | e1 -> e1
(*	
  | Mult (Var s, e1) as e-> 
    if s = v then 
      e
    else
      Mult (e1, Mult (Var s, Var v))
  | Mult (e1,e2) -> Mult ((mapExpr v e1), (mapExpr v e2))
*)

let rec solve e =
  match e with
    One -> One
  | Zero -> Zero
  | Var s -> Var s
  | Inv (Plus (e1,e2)) -> Plus (solve $ Inv (e1), solve $ Inv (e2))
  | Inv (Inv (e1)) -> solve e1
  | Plus (e1, Zero) -> solve e1
  | Plus (Zero, e1) -> solve e1
  | Plus (e1, Inv (e2)) when e1 = e2 -> Zero
  | Plus (Inv (e1), e2) when e1 = e2 -> Zero
  (* after product-sum normal form? *)
  | Mult (Zero, e1) -> Zero
  | Mult (e1, Zero) -> Zero
  | Mult (e1, One) -> solve e1
  | Mult (One, e1) -> solve e1
  | Mult (Var s1, Var s2) when s1 = s2 -> Var s1
  | Mult (e1, Var s) -> solve $ mapExpr s e1
  | Mult (Var s, e1) -> solve $ mapExpr s e1
  | etc -> etc


(* move major functions out of this *)
let rec parse () =
  print_string "<αλγος> ";
  flush stdout;
  try
    let line = input_line stdin in
    (try
       let res = (BooleanParser.boolean1 BooleanLexer.lex (Lexing.from_string line)) in
       begin 
	 print_string "Parsed: ";
	 print_boolean res;
	 let expr = boolean2expr res in
 	 let v = vars expr in
(*	 let term = expr2term expr in *)
	 Printf.printf "Variables(%d):%s\n" (VarSet.cardinal v) (varset2string v);
	 print_string "Algebraic form: ";
	 print_expr expr;
(*
	 print_string "Normalized form: ";
	 print_expr <.> normalize $ expr;
	 print_string "Term form: ";
	 print_term term;
*)
	 let oldAlgos = expr2algos expr in
	 print_string "Algos reduced form: ";
	 print_algos <.> reduce $ oldAlgos;
       end
     with
     | Parsing.Parse_error       -> print_string ("$P" ^ line ^ "\n")
(*     | _                         -> print_string ("$S " ^ line ^ "\n") *)
);
    flush stdout;
    parse ();
  with
    End_of_file -> 
      begin 
	print_string "Leaving algos.\n";
	flush stdout
      end

(* make more modular *)
let _ = 
  begin
    print_string $ "Welcome to αλγος " ^ ver ^ ":\n";
    parse ();
    exit 0;
  end
