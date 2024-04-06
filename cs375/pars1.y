%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 10 Jan 24   */

/* Copyright (c) 2023 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12;
   30 Jul 13; 25 Jul 19 ; 28 Feb 22; 08 Jul 22; 13 Nov 23 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "pprint.h"
#include "parse.h"
#include "codegen.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%right thenthen ELSE // Same precedence, but "shift" wins.

%%

  program    :  PROGRAM IDENTIFIER LPAREN idlist RPAREN SEMICOLON lblock DOT { parseresult = makeprogram($2, $4, $7); }
             ;
  lblock     :  LABEL llist SEMICOLON cblock { $$ = $4; }
             |  cblock 
             ;
  llist      :  NUMBER COMMA llist { instlabel($1); }
             |  NUMBER { instlabel($1); }
             ;
  tblock     :  TYPE tlist vblock { $$ = $3; }
             |  vblock 
             ;
  tlist      :  typegroup SEMICOLON tlist 
             |  typegroup SEMICOLON 
             ;
  typegroup  :  IDENTIFIER EQ type { insttype($1, $3); }
             ;
  flist      :  field SEMICOLON flist { $$ = nconc($1, $3); }
             |  field 
             ;
  field      :  idlist COLON type { $$ = instfields($1, $3); }
             ;
  idlist     :  IDENTIFIER COMMA idlist { $$ = cons($1, $3); }
             |  IDENTIFIER  { $$ = cons($1, NULL); }
             ;
  cblock     :  CONST clist tblock {$$ = $3;}
             |  tblock 
             ;
  clist      :  IDENTIFIER EQ factor SEMICOLON clist {instconst($1, $3); }
             |  IDENTIFIER EQ factor SEMICOLON {instconst($1, $3); } 
             ;
  vblock     :  VAR varspecs block      { $$ = $3; }
             |  block
             ;
  varspecs   :  vargroup SEMICOLON varspecs 
             |  vargroup SEMICOLON 
             ;
  vargroup   :  idlist COLON type { instvars($1, $3); }
             ;
  type       :  simpletype 
             |  POINT IDENTIFIER  { $$ = instpoint($1, $2); }
             |  RECORD flist END  { $$ = instrec($1, $2); }
             |  ARRAY LBRACKET arr RBRACKET OF type  { $$ = instarray($3, $6); }
             ;
  arr        :  simpletype COMMA arr { $$ = cons($1, $3); }
             |  simpletype { $$ = cons($1, NULL); }
             ;
  simpletype :  IDENTIFIER    { $$ = findtype($1); }
             |  expr DOTDOT expr { $$ = instdotdot($1, $2, $3);}
             |  LPAREN idlist RPAREN { $$ = instenum($2); }
             ;
  block      :  BEGINBEGIN statement endpart { $$ = makeprogn($1,cons($2, $3)); }
             ;
  statement  :  BEGINBEGIN statement endpart { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  assignment 
             |  FOR assignment TO factor DO statement { $$ = makefor(1, $1, $2, $3, $4, $5, $6); }
             |  syscall 
             |  REPEAT s_list UNTIL compare { $$ = makerepeat($1, $2, $3, $4); } 
             |  label
             |  WHILE expr DO statement { $$ = makewhile($1, $2, $3, $4); }
             |  GOTO NUMBER { $$ = dogoto($1, $2); }
             ;
  label      :  NUMBER COLON statement { $$ = dolabel($1, $2, $3); }
             ;
  s_list     :  statement SEMICOLON s_list { $$ = cons($1, $3); }
             |  statement { $$ = cons($1, NULL); }
             ;
  compare    :  variable EQ term {$$ = binop($2, $1, $3);}
             ;
  syscall    :  IDENTIFIER LPAREN factorlist RPAREN  { $$ = makefuncall($2, $1, $3); } 
             ;
  factorlist :  expr COMMA factorlist { $$ = cons($1, $3); }
             |  expr { $$ = cons($1, NULL); }
             ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                   { $$ = NULL; }
             ;
  endif      :  ELSE statement        { $$ = $2; }         
             |  /* empty */                  { $$ = NULL; }  %prec thenthen  
             ;
  assignment :  variable ASSIGN expr     { $$ = binop($2, $1, $3); } 
             ;
  expr       :  expr PLUS term                 { $$ = binop($2, $1, $3); } 
             |  term
             |  MINUS term  { $$ = unaryop($1, $2); }
             |  expr MINUS term  { $$ = binop($2, $1, $3); } 
             |  expr NE term 
             |  expr LT term
             ;
  term       :  term TIMES factor             { $$ = binop($2, $1, $3); } 
             |  factor                         
             ;
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  variable 
             |  STRING
             |  NUMBER          
             |  syscall 
             |  NIL
             ;
  variable   : IDENTIFIER { $$ = findid($1); }
             | variable POINT { $$ = dopoint($1, $2); } 
             | variable DOT IDENTIFIER { $$ = reducedot($1, $2, $3); }
             | variable LBRACKET factorlist RBRACKET { $$ = arrayref($1, $2, $3, $4); }
             ;
%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.

   To add more flags, use the next power of 2: the next one would be 32.
   To turn on all flags, set DEBUG to the next power of 2, minus 1.
  */

#define DEBUG           0             /* set bits here for debugging, 0 = off  */
#define DB_CONS         1             /* bit to trace cons */
#define DB_BINOP        2             /* bit to trace binop */
#define DB_MAKEIF       4             /* bit to trace makeif */
#define DB_MAKEPROGN    8             /* bit to trace makeprogn */
#define DB_PARSERES     16            /* bit to trace parseresult */
#define DB_MAKEPROGRAM  32            /* bit to trace makeprog */
#define DB_FINDTYPE     64            /* bit to trace deftype */
#define DB_MAKEFUNCALL  128           /* bit to trace syscall */
#define DB_MAKEFOR      256           /* bit to trace makefor */
#define DB_COPYTOK      512           /* bit to trace copytok */

 int labelnumber = 0;  /* sequential counter for internal label numbers */
 int labellist[2048];

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

/* makenum makes a new integer number token with num as its value */
TOKEN makenum(int num) {
  TOKEN integer = talloc();
  integer->basicdt = INTEGER;
  integer->intval = num;
  integer->tokentype = NUMBERTOK;
  return integer;
}

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { 
    
    item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
    
  }

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { 
    if (rhs->whichval == (NIL - RESERVED_BIAS)) {
      rhs = makenum(0);
    }
    op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
    if (lhs->basicdt == REAL && rhs->basicdt == REAL) {
      op->basicdt = REAL;
    } else if (lhs->basicdt == REAL && rhs->basicdt == INTEGER) {
      op->basicdt = REAL;
      if (rhs->tokentype == NUMBERTOK) {
        rhs->basicdt = REAL;
        rhs->realval = (double) rhs->intval;
      } else {
        TOKEN flt = talloc();
        flt->tokentype = OPERATOR;
        flt->whichval = FLOATOP;
        flt->operands = rhs;
        lhs->link = flt;
      }
    } else if (lhs->basicdt == INTEGER && rhs->basicdt == REAL) {
      if (op->whichval != ASSIGNOP) {
        op->basicdt = REAL;
        if (lhs->tokentype == NUMBERTOK) {
          lhs->basicdt = REAL;
          lhs->realval = (double) lhs->intval;
        } else {
          TOKEN flt = talloc();
          flt->tokentype = OPERATOR;
          flt->whichval = FLOATOP;
          flt->operands = lhs;
          flt->link = rhs;
        }
      } else {
        op->basicdt = INTEGER;
        if (rhs->tokentype == NUMBERTOK) {
          rhs->basicdt = INTEGER;
          rhs->intval = (int) rhs->realval;
        } else {
          TOKEN flt = talloc();
          flt->tokentype = OPERATOR;
          flt->whichval = FIXOP;
          flt->operands = rhs;
          lhs->link = flt;
        }
      }
    }
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
    return op;
  }

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };
     return tok;
   }

/* install variables in symbol table */
void instvars(TOKEN idlist, TOKEN typetok)
  {  SYMBOL sym, typesym; int align;
     if (typetok->symtype) {
      typesym = typetok->symtype;
     }
     align = alignsize(typesym);
     while ( idlist != NULL )   /* for each id */
       {  sym = insertsym(idlist->stringval);
          sym->kind = VARSYM;
          sym->offset =     /* "next" */
              wordaddress(blockoffs[blocknumber],
                          align);
          sym->size = typesym->size;
          blockoffs[blocknumber] =   /* "next" */
                         sym->offset + sym->size;
          sym->datatype = typesym;
          sym->basicdt = typesym->basicdt;
          idlist = idlist->link;
        };
  }

TOKEN findid(TOKEN tok) { /* the ID token */

  
  SYMBOL sym = searchst(tok->stringval);
  tok->symentry = sym;
  if (sym->kind == CONSTSYM) {
    tok->tokentype = NUMBERTOK;
    tok->basicdt = sym->basicdt;
    if (sym->basicdt == INTEGER) {
      tok->intval = sym->constval.intnum;
    } else if (sym->basicdt == REAL) {
      tok->realval = sym->constval.realnum;
    }
    return tok;
  }
  
  SYMBOL typ = sym->datatype;
  tok->symtype = typ;
  if ( typ && (typ->kind == BASICTYPE ||
      typ->kind == POINTERSYM)) {
      
      tok->basicdt = typ->basicdt;
      }
  return tok; 
}

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) 
  {  
     TOKEN parameters = talloc();
     parameters->tokentype = OPERATOR;
     parameters->whichval = PROGNOP;
     parameters->operands = args;
     parameters->link = statements;
     name->link = parameters;
     TOKEN tok = talloc();
     tok->tokentype = OPERATOR;
     tok->whichval = PROGRAMOP;
     tok->operands = name;
     if (DEBUG & DB_MAKEPROGRAM)
       { printf("makeprogram\n");
         dbugprinttok(parameters);
         dbugprinttok(tok);
         dbugprinttok(name);
         dbugprinttok(args);
         dbugprinttok(statements);
       };
     return tok;
   }

/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN variable)
  {  
     // Uses symbol table class to find variable type
     variable->symtype = searchst(variable->stringval);
     if (variable->symtype && variable->symtype->kind == TYPESYM) {
      variable->symtype = variable->symtype->datatype;
     }
     if (DEBUG & DB_FINDTYPE)
       { printf("findtype\n");
         dbugprinttok(variable);
       };
     return variable;
   }

/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args)
  {  
     if (strcmp(fn->stringval, "new") == 0) {
      tok = talloc();
      tok->tokentype = OPERATOR;
      tok->whichval = ASSIGNOP;
      tok->operands = args;
      TOKEN method = talloc();
      method->tokentype = OPERATOR;
      method->whichval = FUNCALLOP;
      method->operands = fn;
      fn->link = makenum(args->symtype->basicdt);
      args->link = method;
      return tok;
     }
     fn->link = args;
     tok->tokentype = OPERATOR;
     tok->whichval = FUNCALLOP;
     tok->operands = fn;
     SYMBOL sym = searchst(fn->stringval);
     tok->symentry = sym;
     tok->symtype = sym->datatype;
     tok->basicdt = sym->datatype->basicdt;
     if (DEBUG & DB_MAKEFUNCALL)
       { printf("makefuncall\n");
         dbugprinttok(fn);
         dbugprinttok(args);
         dbugprinttok(tok);
       };
     return tok;
   }

/* copytok makes a new token that is a copy of origtok */
TOKEN copytok(TOKEN origtok) {
  TOKEN tok = talloc();
  tok->tokentype = origtok->tokentype;
  tok->whichval = origtok->whichval;
  tok->intval = origtok->intval;
  tok->basicdt = origtok->basicdt;
  tok->link = origtok->link;
  if (DEBUG & DB_COPYTOK)
    {
      printf("copytok\n");
      dbugprinttok(tok);
      dbugprinttok(origtok);
    }
  return tok;
}

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement)
  {  
     tok = makeprogn(talloc(), asg);
     //sets label
     TOKEN label = talloc();
     label->tokentype = OPERATOR;
     label->whichval = LABELOP;
     asg->link = label;
     //sets num
     TOKEN num = talloc();
     num->tokentype = NUMBERTOK;
     num->basicdt = INTEGER;
     num->intval = labelnumber;
     label->operands = num;
     labelnumber++;
     //less than or equal to operator
     TOKEN lessequal = talloc();
     lessequal->tokentype = OPERATOR;
     lessequal->whichval = LEOP;
     TOKEN ival1 = copytok(asg->operands);
     ival1->link = endexpr;
     lessequal->operands = ival1;
     //sets then
     TOKEN then = makeprogn(talloc(), statement);
     //sets if
     TOKEN if_val = makeif(talloc(), lessequal, then, NULL);
     label->link = if_val;
     //sets assignment
     TOKEN assign = talloc();
     assign->tokentype = OPERATOR;
     assign->whichval = ASSIGNOP;
     statement->link = assign;
     //sets increment
     TOKEN ival2 = copytok(asg->operands);
     TOKEN add = talloc();
     add->tokentype = OPERATOR;
     add->whichval = PLUSOP;
     ival2->link = add;
     TOKEN ival3 = copytok(asg->operands);
     // increment value
     TOKEN one = talloc();
     one->tokentype = NUMBERTOK;
     one->basicdt = INTEGER;
     one->intval = 1;
     ival3->link = one;
     add->operands = ival3;
     assign->operands = ival2;
     TOKEN goto_val = talloc();
     goto_val->tokentype = OPERATOR;
     goto_val->whichval = GOTOOP;
     TOKEN num2 = copytok(num);
     goto_val->operands = num2;
     assign->link = goto_val;
     return tok;
   }

/* instconst installs a constant in the symbol table */
void instconst(TOKEN idtok, TOKEN consttok) {
  SYMBOL symbol = insertsym(idtok->stringval);
  symbol->basicdt = consttok->basicdt;
  symbol->kind = CONSTSYM;
  if (consttok->basicdt == REAL) {
    symbol->constval.realnum = consttok->realval;
  } else if (consttok->basicdt == INTEGER) {
    symbol->constval.intnum = consttok->intval;
  }
}

/* unaryop links a unary operator op to one operand, lhs */
TOKEN unaryop(TOKEN op, TOKEN lhs) {
  op->operands = lhs;
  return op;
}

/* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
  // sets label
  TOKEN label = talloc();
  label->tokentype = OPERATOR;
  label->whichval = LABELOP;
  TOKEN num = talloc();
  num->tokentype = NUMBERTOK;
  num->basicdt = INTEGER;
  num->intval = labelnumber;
  label->operands = num;
  tok = makeprogn(tok, label);
  // makes body
  tokb = makeprogn(tokb, statements);
  label->link = tokb;
  // makes goto
  TOKEN goto_val = talloc();
  goto_val->tokentype = OPERATOR;
  goto_val->whichval = GOTOOP;
  goto_val->operands = num;
  TOKEN nul = makeprogn(talloc(), NULL);
  nul->link = goto_val;
  // makes if
  TOKEN if_val = makeif(talloc(), expr, nul, goto_val);
  tokb->link = if_val;
  labelnumber++;
  return tok;
}

/* nconc concatenates two token lists, destructively, by making the last link
   of lista point to listb.
   (nconc '(a b) '(c d e))  =  (a b c d e)  */
/* nconc is useful for putting together two fieldlist groups to
   make them into a single list in a record declaration. */
/* nconc should return lista, or listb if lista is NULL. */
TOKEN nconc(TOKEN lista, TOKEN listb) {
  TOKEN con = lista;
  while (con->link) {
    con = con->link;
  }
  con->link = listb;
  return con;
}

/* makearef makes an array reference operation.
   off is be an integer constant token
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  TOKEN ref = talloc();
  ref->tokentype = OPERATOR;
  ref->whichval = AREFOP;
  ref->operands = var;
  ref->symentry = var->symentry;
  var->link = off;
  return ref;
}

/* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
  // sets label
  TOKEN label = talloc();
  label->tokentype = OPERATOR;
  label->whichval = LABELOP;
  TOKEN num = talloc();
  num->tokentype = NUMBERTOK;
  num->basicdt = INTEGER;
  num->intval = labelnumber;
  label->operands = num;
  tok = makeprogn(tok, label);
  TOKEN body = makeprogn(tokb, statement);
  // makes goto
  TOKEN goto_val = talloc();
  goto_val->tokentype = OPERATOR;
  goto_val->whichval = GOTOOP;
  goto_val->operands = num;
  TOKEN nul = makeprogn(talloc(), NULL);
  nul->link = goto_val;
  // makes if
  TOKEN if_val = makeif(talloc(), expr, nul, goto_val);
  tokb->link = if_val;
  labelnumber++;
  return tok;
}

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high) {
  tok->symtype = symalloc();
  tok->symtype->basicdt = INTEGER;
  tok->symtype->lowbound = low;
  tok->symtype->highbound = high;
  tok->symtype->kind = SUBRANGE;
  tok->symtype->size = basicsizes[INTEGER];
  return tok;
}

/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  SYMBOL temp = var->symtype;
  int count = 0;
  int off = 0;
  while (temp) {
    if (strcmp(temp->namestring, field->stringval) == 0) {
      var->symentry = temp;
      off = temp->offset;
      break;
    }
    temp = temp->link;
  }
  dot = makearef(var, makenum(off), dot);
  return dot;
}

/* arrayref processes an array reference a[i]
   subs is a list of subscript expressions.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
  TOKEN size = makenum(arr->symtype->size / (arr->symtype->lowbound + arr->symtype->highbound - 1));
  if (subs->link) {
    TOKEN temp = copytok(subs);
    size->link = temp;
    temp->link = NULL;
  } else {
    size->link = subs;
  }
  TOKEN time = talloc();
  time->tokentype = OPERATOR;
  time->whichval = TIMESOP;
  time->operands = size;
  TOKEN neg = makenum(size->intval * -1);
  neg->link = time;
  TOKEN pos = talloc();
  pos->tokentype = OPERATOR;
  pos->whichval = PLUSOP;
  pos->operands = neg;
  TOKEN sub = makearef(arr, pos, tokb);
  if (subs->link) {
    sub->symtype = arr->symtype->datatype;
    return arrayref(sub, tok, subs->link, tokb);
  }
  return sub;
}

/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
  int label = -1;
  for (int i = 0; i < labelnumber; i++) {
    if (labellist[i] == labeltok->intval) {
      label = i;
      break;
    }
  }
  TOKEN lab = talloc();
  lab->tokentype = OPERATOR;
  lab->whichval = LABELOP;
  lab->operands = makenum(label);
  lab->link = statement;
  tok = makeprogn(tok, lab);
  return tok;
}

/* dogoto is the action for a goto statement.
   tok is a (now) unused token that is recycled. */
TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
  int label = -1;
  for (int i = 0; i < labelnumber; i++) {
    if (labellist[i] == labeltok->intval) {
      label = i;
      break;
    }
  }
  tok = talloc();
  tok->tokentype = OPERATOR;
  tok->whichval = GOTOOP;
  tok->operands = makenum(label);
  return tok;
}

/* dopoint handles a ^ operator.  john^ becomes (^ john) with type record
   tok is a (now) unused token that is recycled. */
TOKEN dopoint(TOKEN var, TOKEN tok) {
  tok->symtype = var->symtype;
  tok->tokentype = OPERATOR;
  tok->whichval = POINTEROP;
  tok->operands = var;
  var->link = NULL;
  return tok;
}

/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num) {
  labellist[labelnumber] = num->intval;
  labelnumber++;
}

/* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist) {
  TOKEN temp = copytok(idlist);
  int count = 0;
  while(temp) {
    instconst(temp, makenum(count));
    temp = temp->link;
    count++;
  }
  TOKEN sub = makesubrange(idlist, 0, count-1);
  return sub;
}

/* instdotdot installs a .. subrange in the symbol table.
   dottok is a (now) unused token that is recycled. */
TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  return makesubrange(dottok, lowtok->intval, hightok->intval);
}

/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok) {
  if (bounds->link) {
    typetok = instarray(bounds->link, typetok);
  }
  SYMBOL array = symalloc();
  array->datatype = typetok->symtype;
  array->lowbound = bounds->symtype->lowbound;
  array->highbound = bounds->symtype->highbound;
  array->kind = ARRAYSYM;
  array->size = typetok->symtype->size * (bounds->symtype->lowbound + bounds->symtype->highbound - 1);
  typetok->symtype = array;
  return typetok;
}

/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok) {
  TOKEN temp = idlist;
  while(temp) {
    temp->symtype = typetok->symtype;
    temp = temp->link;
  }
  return idlist;
}

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type.  rectok is just a trash token to be
   used to return the result in its symtype */
TOKEN instrec(TOKEN rectok, TOKEN argstok) {
  int count = 0;
  int first = 1;
  SYMBOL sym = symalloc(), prev = NULL;
  while (argstok) {
    SYMBOL rec = makesym(argstok->stringval);
    rec->offset = (count + alignsize(argstok->symtype) - 1) / alignsize(argstok->symtype) * alignsize(argstok->symtype);
    rec->datatype = argstok->symtype;
    rec->size = argstok->symtype->size;
    count = rec->size + rec->offset;
    if (first) {
      first = 0;
      sym->datatype = rec;
      prev = rec;
    } else {
      prev->link = rec;
      prev = rec;
    }
    rec->link = NULL;
    argstok = argstok->link;
  }
  sym->kind = RECORDSYM;
  sym->size = (count + 16 - 1) / 16 * 16;
  rectok->symtype = sym;
  
  return rectok;
}

/* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL point = symalloc();
  point->kind = POINTERSYM;
  point->basicdt = POINTER;
  point->size = basicsizes[POINTER];
  tok->symtype = point;
  return tok;
}

/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void  insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL type = searchins(typename->stringval);
  type->datatype = typetok->symtype;
  alignsize(typetok->symtype);
  type->kind = TYPESYM;
  type->size = typetok->symtype->size;
}

int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}

int main(void)          /*  */
  { int res;
    initsyms();
    res = yyparse();
    printstlevel(1);    /* to see level 0 too, change to:   printst();  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }
