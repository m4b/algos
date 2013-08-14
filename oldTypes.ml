open AlgosTypes

type algos = Un | Ni | Terminal of string | Expr of algos list | Anti of algos list | Times of algos list;;

exception BAD_MATCH

let rec expr2algos b =
  match b with
    One -> Un
  | Zero -> Ni
  | Var string -> Terminal string
  | Inv e -> Anti [expr2algos e]
  | Plus (e1,e2) -> Expr [(expr2algos e1);(expr2algos e2)]
  | Mult (e1,e2) -> Times [(expr2algos e1);(expr2algos e2)]

let rec algos2expr b =
  match b with
    Un -> One
  | Ni -> Zero
  | Terminal i -> Var i
  | Anti (e1::e2) -> Inv (algos2expr e1)
  | Expr (e1::e2::[]) -> Plus ((algos2expr e1),(algos2expr e2))
  | Expr (e1::e2) -> Plus ((algos2expr e1),(algos2expr (Expr e2)))
  | Times (e1::e2::[]) -> Mult ((algos2expr e1),(algos2expr e2))
  | Times (e1::e2) -> Mult ((algos2expr e1),(algos2expr (Times e2)))  
  | _ -> raise BAD_MATCH

let rec algos2string a = 
  match a with
    Un -> "1"
  | Ni -> "0"
  | Terminal i -> i
  | Anti []-> ""
  | Anti (e1::[]) -> "−" ^ (algos2string e1)
  | Anti es -> "−" ^ (algos2string (List.hd es))
  | Expr es -> 
    let f acc x = 
      if acc = "" then
	  algos2string x
      else
	(acc ^ " + " ^ (algos2string x)) in
   "(" ^ (List.fold_left f "" es) ^ ")"
  | Times es -> 
    let f acc x = 
      if acc = "" then
	algos2string x
      else
	(acc ^ " × " ^ (algos2string x)) in
   "(" ^ (List.fold_left f "" es) ^ ")"

let print_algos a = print_string $ (algos2string a) ^ "\n"

exception Non_lits_in_Times;;

let add_elem elem list =
  if List.mem elem list 
  then list 
  else 
    elem :: list;;

let nodup list = List.fold_right add_elem list [];;

let rec sheff (x) (y) =

  match x with

    Terminal(i) -> 
      (  
	match y with

	  Terminal(j) ->
	    
	    if i = j then let finalout = Expr([Un; Anti ([x])]) in finalout 

	    else 
	      
  	      let finalout = Expr([Un; Anti ([Times ([x; y])])]) in finalout 

	| Expr (y1) -> 
	  
          let finalout = Expr([Un; Anti ([Times ([x; Expr(y1)])])]) in finalout  

	| _ -> raise BAD_MATCH
      ) 						     
	
  | Expr (x1) -> 
    (
      match y with

        Terminal(j) ->


          let finalout = Expr([Un; Anti ([Times ([Expr(x1); y])])]) in finalout  

      | Expr(y1) ->


        let finalout = Expr([Un; Anti ([Times ([x; y])])]) in finalout  

      | _ -> raise BAD_MATCH
    )

  | _ -> raise BAD_MATCH
;;


let neg (x) = sheff x x;;

let fand (x) (y) = sheff (sheff x y) (sheff x y);;

let flor (x) (y) = sheff (sheff x x) (sheff y y);;

let imp (x) (y) = sheff x (sheff y y);;

let x1 foo bar  = Expr [Un; Anti[foo]; Anti[bar]; Times [foo; bar]];;

(* A & ~B *)

let x2 foo bar = Expr [foo; Anti [Times [foo; bar]]];;

(* ~B *) 

let x3 foo = Expr [Un; Anti [foo]];;

(* ~A & B *) 

let x4 foo bar = Expr [bar; Anti [Times [foo; bar]]];;

(* ~A  *)

let x5 foo = Expr [Un; Anti [foo]];;

(* ~(A <-> B) *)

let x6 foo bar = Expr [foo; bar; Anti [Times [foo; bar]]; Anti [Times [foo; bar]]];;

(* ~A \/ ~B *)

let x7 foo bar = sheff foo bar;;

(* A & B *)

let x8 foo bar = Times [foo; bar];;

(* A <-> B *)

let x9 foo bar = Expr [Un; Anti [foo]; Anti [bar]; Times [foo; bar]; Times [foo; bar]];;

(* A *)

let x10 foo = Terminal "a";;

(* B -> A *)

let x11 foo bar = Expr [Un; Anti [bar]; Times [foo; bar]];;

(* B *)

let x12 foo = Terminal "b";;

(* A -> B  *)

let x13 foo bar = Expr [Un; Anti [foo]; Times [foo; bar]];;

(* A \/ B *)

let x14 foo bar = Expr [foo; bar; Anti [Times [foo; bar]]];;

(* renames for easy use *)

let rand  = x8;;

let ror = x14;;

let rimp = x13;;

(* quick negation *)

let n x = Expr [Un; Anti [x]];;

let rec antipair (x) =

  match x with

    [] -> false

  | h::t as l -> 
    (
      match h with 

	Anti[i] ->
	  if List.mem i l then true
	  else antipair t

      | _ as i2 ->

	if ((List.mem i2 l) && (List.mem (Anti[i2]) l) ) then true
	else antipair t
    )
;; 

let rec expred (x:algos list) =

  match x with

    [] -> x

  | Expr (hd)::tl ->

    
    expred(hd)@expred(tl)
      
  | (_ as hd)::tl ->

    hd::expred(tl)
;;


exception Empty_list;;

let element_at l k = ( List.nth l ( k - 1 ) );;

let rec element_at_2 l k =
  match l with
    []      -> raise Empty_list
  |       h::t    -> if ( k = 1 ) then h else ( element_at_2 t ( k - 1 ) )
;;


let rec remove_at l i =
  match l with
    []	-> []
  |	h::t	-> if ( i = 1 ) then t else h::( remove_at t ( i - 1 ) )
;;

let rec anti_smasher x =

  match x with 

    [] -> []

  | hd::tl ->
    (
      match hd with

	Anti[(i as j)] ->

	  if List.mem i tl then 
	    (
	      
	      let len = List.length tl in
	      
	      anti_smasher(remove_at (tl) ((where2 (tl) (len) (j))))
	    )
	  else hd::anti_smasher(tl)

      | _ -> 
	
	if List.mem (Anti[hd]) tl

	then
	  (
	    
	    let len = List.length tl in

	    anti_smasher(remove_at (tl) ((where (tl) (len) (hd))))
	      
	  )
	else hd::anti_smasher(tl)
    )
and where (list) (n) (h) =

  if (element_at (list) (n)) = Anti[h] then n
  else where (list) (n-1) (h)

and where2 (list) (n) (h) =

  if (element_at (list) (n)) = (h) then n
  else where2 (list) (n-1) (h)

;;

let scrub (x) = 

  if antipair (x) then 

    anti_smasher(x)

  else x
;;


exception Times_lack_match_possible_impure_mult;;
exception Sort_lit_bugged;;


let islit (x) =
  match x with

    Terminal (j) -> true

  | _ -> false

;;

let rec foil (x) (y) =

  match x with

    [] -> x

  | hd :: tl ->

    (List.map (fun mem -> Times [hd; mem]) y)@foil tl y
;;

let sortlit (x) = 

  List.sort (fun x1 y1 -> match x1 with Terminal (i) -> (match y1 with Terminal (j) -> if i > j then 1 else 0 | _ -> raise Sort_lit_bugged) | _ -> raise Sort_lit_bugged) x
;;

let c = ref 0;;
let count x = 
  x := !x + 1
;;

let rec muld (x) =

  count c; 

  match x with

    [] -> x

  | Un::tail ->
    
    Un::muld(tail)

  | Ni::tail ->
    
    Ni::muld(tail)

  | Terminal(i)::tail ->

    Terminal(i)::muld(tail)

  | ((Anti (h2)) as a)::t2 ->
    
    if List.length h2 > 1 then 
      
      (	  
	muld((List.map (fun mem -> Anti[mem]) h2))@muld(t2);
      )
    else
      (
	match h2 with 

	  [Un] ->

	    a::muld(t2)

	| [Ni] ->
	  
	  Ni::muld(t2)

	| [Terminal j] ->

	  a::muld(t2)

	| [Anti(h3)] ->  
	  
	  muld(h3)@muld(t2)

	| [Times((h3::t3) as j)] ->

	  if List.for_all islit j && [h3] <> t3 then
	    (		  
	      Anti[Times(sortlit(j))]::muld(t2)
	    )
	  else
	    (		  
	      muld([Anti(muld([Times(h3::t3)]))])@muld(t2)
	    )

	| [Expr(h3)] ->  
	  
	  muld([Expr(muld((List.map (fun mem -> Anti[mem]) h3)))])@muld(t2)
	    
	| _ ->  
	  
	  Anti (muld (h2))::muld(t2)
      )

  (* **********MULT************** *)

  (* Begin Times cases, the majority of this function*)

  | Times(m2::m3)::tail when List.for_all islit (m2::m3) && List.tl (m2::m3) <> [] -> (* all lit guard *) 

    if [m2] = m3 then
      (		  	  
	m2::muld(tail)
      )
    else
      (
	
	if List.length (nodup(m2::m3)) = 1 then
	  (	      
	    m2::muld(tail)
	  )
	else
	  (	     
	    Times(sortlit(nodup(m2::m3)))::muld(tail)
	  )
      )

  | Times(m2::m3)::tail ->
    
    (
      match m2 with

	Un -> 
	  
	  (

	    match m3 with

	      [] -> 
		
		muld(tail)

	    |  [Un] ->
	      
	      Un::muld(tail)

	    | [Ni] ->
	      
	      Ni::muld(tail)
		
	    | [Terminal(z)] ->
	      
	      Terminal(z)::muld(tail)
		
	    | [Anti(z)] ->
	      
	      muld(Anti(muld(z))::muld(tail))
		
	    | [Times(z)] ->

	      if List.for_all islit (z)
	      then Times(sortlit(z))::muld(tail)
	      else
		(
		  
		  muld(Times(muld(z))::muld(tail))   
		)

	    | [Expr(z)] ->
	      
	      muld(Expr(scrub(muld(z)))::muld(tail))
		
	    | _ as z -> 
	      
	      Times(muld(z))::muld(tail)

	  )
	    
      | Ni ->
	
	Ni::muld(tail)

      | Terminal(j) ->
	
	(

	  match m3 with

	    [] -> 

	      
	      muld(tail)

	  |  [Un] ->
	    
	    Terminal(j)::muld(tail)

	  | [Ni] ->
	    
	    Ni::muld(tail)

	  | [Terminal(z)] ->

	    (* this case made redundant from the all Terminal guard match case, but left here *)

	    if [m2] = m3 then 
	      (		      
		m2::muld(tail)
	      )
	    else
	      (		      
		Times(sortlit([Terminal(j);Terminal(z)]))::muld(tail)
	      )

	  | [Anti(z)] ->
	    
	    if [m2] = z then 
	      (		      
		Anti(z)::muld(tail)
	      )
	    else
	      (
		
		match z with

		  [] -> 
		    
		    muld(tail)

		| [Un] ->
		  
		  Anti[m2]::muld(tail)

		| [Ni] ->
		  
		  Ni::muld(tail)
		    
		| [Terminal(j2)] ->
		  
		  Anti[Times(sortlit(m2::z))]::muld(tail)

		| [Anti(j2)] ->
		  
		  muld([Times(m2::j2)])@muld(tail)

		(* example when bug testing.

		   test expression:
		   muld [Times [Terminal 1; Anti [Anti [Terminal 1]]]];;
		*)

		| [Times((hd2::tl2) as j2)] ->
		  
		  if (List.for_all islit j2 && [hd2] <> tl2) then
		    (			      
		      Anti[Times(sortlit(nodup(m2::j2)))]::muld(tail)
		    )
		  else
		    (			      
		      Anti(muld([Times(m2::muld(z))]))::muld(tail)
		    )

		| [Expr(j2)] ->
		  
		  muld([Anti[Expr(muld(foil [m2] j2))]])@muld(tail)
		    
		| _ ->    
		  
		  muld([Anti(muld([Times([m2]@muld(z))]))])@muld(tail)

	      )

	  (* end Anti = m3 *)

	  | [Times((hd2::tl2) as z)] ->
	    
	    if [hd2] = tl2 && List.for_all islit z then
	      (		      
		muld([Times(m2::tl2)])@muld(tail)
	      )
	    else
	      (

		if List.for_all islit z then
		  ( 
		    if List.mem m2 z then
		      (			      
			Times(sortlit(z))::muld(tail)
		      )
		    else
		      (			      
			Times(sortlit(nodup(m2::z)))::muld(tail)
		      )
		  )
		else

		  (
		    if List.length z > 2 then
		      (			      
			Times(m2::z)::muld(tail)
		      )
		    else
		      (			      
			muld([Times(m2::muld(m3))])@muld(tail)
		      )
		  )
	      )

	  | [Expr(z)] ->
	    
	    Expr(muld((List.map (fun mem -> Times[Terminal(j); mem]) z)))::muld(tail)

	  | _ as z ->
	    
	    Times(m2::muld(z))::muld(tail)

	) (* END lit match m3 bracket *)  	
	  
      (* start m2 again  *)

      | Anti(j) ->

	(
	  match m3 with
	    
	    [] ->
	      
	      muld(tail)

	  | [Un] -> 
	    
	    muld([Anti(muld(j))])@muld(tail) 

	  | [Ni] ->
	    
	    Ni::muld(tail)

	  | [Terminal(z)] (* m3 = Terminal(z) *) ->

	    if j = [Terminal(z)] then 
	      (		      
		Anti(j)::muld(tail)
	      )
	    else
	      (
		
		match j with (* i.e., what m2 equals *)

		  [] -> 
   		    
		    muld(tail)

		| [Un] ->
		  
		  Anti(m3)::muld(tail)

		| [Ni] ->
		  
		  Ni::muld(tail)

		| [Terminal(j2)] ->
		  
		  Anti[Times(sortlit(j@m3))]::muld(tail)

		| [Anti(j2)] ->

 		  muld([Times(j2@m3)])@muld(tail)
		    
		| [Times((hd2::tl2) as j2)] (* j *) ->

		  if (List.for_all islit j2 && [hd2] <> tl2) then
		    (			      
		      Anti[Times(sortlit(nodup(j2@m3)))]::muld(tail)
		    )
		  else
		    (
		      Anti(muld([Times(m3@muld(j))]))::muld(tail)
		    )

		| [Expr(j2)](* = j in Anti[j] *) ->
		  
		  muld([Anti[Expr(muld(foil m3 j2))]])@muld(tail)			    			    
		| _ ->    

 		  Times(m2::m3)::muld(tail)
	      )

	  | [Anti(z)] (* m3 *) ->

	    muld([Times(j@z)])@muld(tail)

	  | [Times((hd2::tl2) as z)] (* m3 *) ->

	    (
	      match j with

		[] -> 
		  
		  muld(tail)

	      | [Un] -> 

		muld([Anti(muld(m3))])@muld(tail)

	      | [Ni] ->
		
		Ni::muld(tail)

	      | [Terminal(j2)] ->

		if (List.for_all islit z && [hd2] <> tl2) then
		  (
		    Anti[Times(sortlit(nodup(j@z)))]::muld(tail)
		  )
		else
		  (
		    Anti(muld([Times(j@muld(m3))]))::muld(tail)
		  )

	      | [Anti(j2)] (* j *) ->
		
		muld([Times(j2@muld(m3))])@muld(tail)
		  
	      | [Times((hd3::tl3) as j2)] (* j *) ->

		if List.for_all islit z && List.for_all islit j2 && sortlit z = sortlit j2 && [hd2] <> tl2 then
		  (
		    Anti(m3)::muld(tail)
		  )
		else 
		  (
		    Anti(muld([Times(muld(j)@muld(m3))]))::muld(tail)
		  )

	      | [Expr(j2)] (* j *) ->

		muld([Anti[Expr(muld(foil (muld m3) j2))]])@muld(tail)  

	      | _ -> raise BAD_MATCH
	    )
	      
	      
	  | [Expr(z)] (* m3 *) ->
	    
	    (
	      match j with

		[] -> 

		  muld(tail)

	      | [Un] ->

		muld([Anti[Expr(z)]])@muld(tail)

	      | [Ni] ->
		
		Ni::muld(tail)

	      | [Terminal(j2)] ->

		[Expr(muld(List.map (fun mem -> Times[Anti(muld(j)); mem]) z))]@muld(tail) 

	      | _ ->
		
		[Expr(muld(List.map (fun mem -> Times[Anti(muld(j)); mem]) z))]@muld(tail) 
	    )

	  | _ -> raise BAD_MATCH
	      
	    
	) (* end Anti = m2 bracket *)


      (* 	begin m2 bracket *)

      | Times((hd2::tl2) as z) ->
	
	(
	  match m3 with 

	    [Un] ->
	      
	      muld([m2])@muld(tail)

	  | [Ni] -> 
	    
	    Ni::muld(tail) 
	      
	  | [Terminal(j) as j2]->
	    
	    if [hd2] = tl2 && List.for_all islit z then
	      (
		
		muld([Times(hd2::m3)])@muld(tail)
	      )
	    else
	      (

		if List.for_all islit z then
		  ( 
		    if List.mem j2 z then
		      (
			
			Times(sortlit(z))::muld(tail)
		      )
		    else
		      (
			
			Times(sortlit(nodup(j2::z)))::muld(tail)
		      )
		  )
		else

		  (
		    if List.length z > 2 then
		      (
			
			Times(j2::z)::muld(tail)
		      )
		    else
		      (
			
			muld([Times(j2::muld([m2]))])@muld(tail)
		      )
		  )
	      )

	  | [Anti(j)] (* m3 *)->

	    (
	      match j with

		[] -> 

		  muld(tail)

	      | [Un] -> 

		muld([Anti(muld([m2]))])@muld(tail)
	      | [Ni] ->
		
		Ni::muld(tail)

	      | [Terminal(j2) as j3]  ->

		if [hd2] = tl2 && List.for_all islit z then
		  (
		    
		    muld([Anti[Times(hd2::j)]])@muld(tail)
		  )

		else		      
		  
		  (

		    if List.for_all islit z then
		      ( 
			if List.mem j3 z then
			  (
			    
			    Anti[Times(sortlit(z))]::muld(tail)
			  )
			else
			  (
			    
			    Anti[Times(sortlit(nodup(j@z)))]::muld(tail)
			  )
		      )
		    else

		      (
			if List.length z > 2 then
			  (

			    
			    Anti[Times(j@z)]::muld(tail)
			  )
			else
			  (
			    
			    muld([Anti(muld([Times(j@muld([m2]))]))])@muld(tail)
			      
			  )
		      )
		  )				

	      | [Anti(j2)] ->

		muld([Times(m2::j2)])@muld(tail)

	      | [Times(j2)] ->

		if List.for_all islit z & List.for_all islit j2 & sortlit z = sortlit j2 then
		  (				  
		    Anti[Times(sortlit(j2))]::muld(tail)
		  )
		else 
		  (				  
		    muld[Anti(muld([Times(m2::j)]))]@muld(tail)
		  )

	      | [Expr(j2)] ->

		muld[Anti(muld([Times(m2::j)]))]@muld(tail)				
	      | _ -> raise BAD_MATCH

	    )

	  | [Times((hd3::tl3) as j)] (* m3 *) ->
	    
	    if List.for_all islit z && List.for_all islit j && ([hd3] <> tl3 && [hd2] <> tl2) then

	      (
		(* checking for same lits, using sortlit *)
		if sortlit z = sortlit j then
		  (
		    
		    Times(sortlit(j))::muld(tail)

		  )
		else
		  (
		    
		    Times(sortlit(nodup(z@j)))::muld(tail)
		  )
	      )
	    else
	      (
		
		muld([Times(muld([m2])@muld(m3))])@muld(tail)
	      )

	  | [Expr(j)] (* m3 *) ->
	    
	    muld([Expr(muld(foil [m2] j))])@muld(tail)

	  | _ -> raise BAD_MATCH
	)	    

      | Expr(z) (*m2 *) ->

	(
	  match m3 with 

	    [Un] ->

	      muld([m2])@muld(tail)

	  | [Ni] ->
	    
	    Ni::muld(tail)

	  | [Terminal(j)] ->
	    
	    muld([Expr(muld(foil z m3))])@muld(tail) 
	  | [Anti(j)] ->
	    
	    (
	      match j with

	      | [Un] -> 	      

		muld([Anti[m2]])@muld(tail)
		  
	      | [Ni] -> 

		Ni::muld(tail)

	      | [Terminal(j2)] ->
		
		muld([Expr(muld(foil z m3))])@muld(tail)
	      | [Anti(j2)] ->

		muld([Times(m2::j2)])@muld(tail)

	      | [Times(j2)] ->

		muld([Expr(muld(foil z m3))])@muld(tail)
	      | [Expr(j2)] ->

		muld([Anti[Expr(muld(foil z j2))]])@muld(tail)

	      | _ -> raise BAD_MATCH
	    )

	  | [Times(j)] ->
	    
	    muld([Expr(muld(foil z m3))])@muld(tail)

	  | [Expr(j)] ->
	    
	    muld([Expr(muld(foil z j))])@muld(tail) 

	  | _ -> raise BAD_MATCH
	)

      | _ -> raise BAD_MATCH
	      
	    

    )  (* Else bracket, i.e., what m2 = *)

  (* ****************** END MULT ***************** *)	

  |  Expr(head::tail)::y ->

    (

      match head with
	
	Un ->
	  
	  Expr(head::muld(tail))::muld(y)
	    
      | Ni ->
	
	Expr(head::muld(tail))::muld(y)

      | Terminal(i2) ->
	
	Expr(head::muld(tail))::muld(y)	    

      | Anti(a3) ->
	
	Expr(muld([head])@muld(tail))::muld(y)
	  
      | Times(m1) ->

	Expr(muld([head])@muld(tail))::muld(y)

      | Expr(i3) ->

	Expr(muld(i3)@muld(tail))::muld(y)	    	      

    )

  | hd::tl -> 
    
    x

;;


let red_algos (x) = scrub (expred (x))

let r x = red_algos (muld (x))

let reconstitute x = 
  Expr x

let rr x = reconstitute (r [x])

let l_reconstitute x = 
  match x with
    [Terminal (i)] -> Terminal i
  | _ -> Expr(x)


let lrr x = l_reconstitute (r [x])

let eq foo bar = if (r [x9 (rr (foo)) (rr (bar))]) = [Un] then true else false

let sat x = if r x <> [] then "SAT" else "UNSAT"
let lrr_sat x = if lrr(x) <> Expr[] then "SAT" else "UNSAT"

let algosCompare a1 a2 =
  match a1 with
    Anti (Times a::[]) -> 
      begin
	match a2 with
	  Times a' -> if List.length a < List.length a' then 0 else 1
	| Anti (Times a'::[]) -> if List.length a < List.length a' then 0 else 1 
	| _ -> if a1 < a2 then 0 else 1
      end
  | Times a -> 
      begin
	match a2 with
	  Times a' -> if List.length a < List.length a' then 0 else 1
	| Anti (Times a'::[]) -> if List.length a < List.length a' then 0 else 1
	| _ -> if a1 < a2 then 0 else 1
      end
  | _ ->  if a1 < a2 then 0 else 1

let rec sortAlgos a1 =
  match a1 with
    Expr a -> Expr (List.sort algosCompare (List.map sortAlgos a))
  | Times a -> Times (List.sort algosCompare (List.map sortAlgos a))
  | a -> a

let rec sortAlgosList a1 =
  match a1 with
    Expr a -> (List.sort algosCompare a)
  | Times a -> (List.sort algosCompare a)
  | a -> [a]

let reduce a = sortAlgos <.> lrr $ a
