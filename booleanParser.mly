%{ open AlgosTypes %}

%token <string> LIT
%token OPEN CLOSE
%token TOP BOT
%token NEGATION CONJUNCTION DISJUNCTION IMPLICATION BICONDITIONAL EOF

%start boolean1
%type <AlgosTypes.boolean> boolean1

%left IMPLICATION BICONDITIONAL 
%left CONJUNCTION DISJUNCTION
%right NEGATION

%%

boolean:
| TOP                                              { Top            }
| BOT                                              { Bot            }
| LIT                                              { Lit $1         }
| OPEN NEGATION boolean CLOSE                      { Neg $3         }
| NEGATION boolean                                 { Neg $2         }
| OPEN boolean CONJUNCTION boolean CLOSE           { And($2, $4)    } 
| boolean CONJUNCTION boolean                      { And($1, $3)    }
| OPEN boolean DISJUNCTION boolean CLOSE           { Or($2, $4)    }
| boolean DISJUNCTION boolean                      { Or($1, $3)    }
| OPEN boolean IMPLICATION boolean CLOSE           { Imp($2, $4)    }
| boolean IMPLICATION boolean                      { Imp($1, $3)    }
| OPEN boolean BICONDITIONAL boolean CLOSE         { Bicon($2, $4)  }
| boolean BICONDITIONAL boolean                    { Bicon($1, $3)  }

boolean1:
| boolean EOF { $1 };
