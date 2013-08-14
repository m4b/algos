{ open BooleanParser }

rule lex = parse
  | [' ' '\n' '\t'] { lex lexbuf }
  | ['a'-'z']+ ['0'-'9']* as v { LIT(v) }
  | '('             { OPEN } 
  | ')'             { CLOSE }
  | "⊤"|'1'|'T'     { TOP }
  | "⊥"|'0'|'F'     { BOT }
  | "¬"|'~'         { NEGATION }
  | "∧"|"/\\"       { CONJUNCTION }
  | "∨"|"\\/"       { DISJUNCTION }
  | "→"|"⇒"|"->"    { IMPLICATION }
  | "↔"|"⇔"|"<->"   { BICONDITIONAL }
  | eof             { EOF }
