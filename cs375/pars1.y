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
  program    : PROGRAM IDENTIFIER LPAREN idlist RPAREN SEMICOLON lblock DOT { parseresult = makeprogram($2, $4, $7); } ;
             ;
  sign       :  PLUS
             |  MINUS
             ;
  constant_type   :  sign IDENTIFIER     { $$ = unaryop($1, $2); }
                  |  sign NUMBER         { $$ = unaryop($1, $2); }
                  |  NUMBER
                  |  STRING
                  |  IDENTIFIER
                  ;
  idlist     :  IDENTIFIER COMMA idlist { $$ = cons($1, $3); }
             |  IDENTIFIER    { $$ = cons($1, NULL); }
             ;
  constant_list :  IDENTIFIER EQ constant_type SEMICOLON constant_list { instconst($1, $3); }
                  | IDENTIFIER EQ constant_type SEMICOLON { instconst($1, $3); }
                  ;        
             ;
  type_def   :   IDENTIFIER EQ type   {insttype($1, $3);}  
  type_list  :  type_def SEMICOLON type_list
             |  type_def SEMICOLON
             ;
  field      :  idlist COLON type             { $$ = instfields($1, $3); }
             ;
  field_list :  field SEMICOLON field_list   { $$ = nconc($1, $3); }
             |  field
             ;
  cblock     :  CONST constant_list type_block              { $$ = $3; }
             |  type_block
             ;
  lblock     :  LABEL nlist SEMICOLON cblock  { $$ = $4; }
             |  cblock
  type_block     :  TYPE type_list vblock       { $$ = $3; }
                  |  vblock
                  ;
  vblock     :  VAR varspecs block       { $$ = $3; }
             |  block
             ;
  statement_list     :  statement SEMICOLON statement_list      { $$ = cons($1, $3); }
                    |  statement          { $$ = cons($1, NULL); }
                    ;
  varspecs   :  vargroup SEMICOLON varspecs  
             |  vargroup SEMICOLON         {}  
             ;
  vargroup   :  idlist COLON type { instvars($1, $3); }
             ;
  type       :  simpletype
             |  array
             |  record
             |  POINT IDENTIFIER      { $$ = instpoint($1, $2);}
             ;
  nlist      :  NUMBER COMMA nlist  { instlabel($1); }
             |  NUMBER                { instlabel($1); }
             ;
  array      :  ARRAY LBRACKET simpletypelist RBRACKET OF type  { $$ = instarray($3, $6); }
  record     :  RECORD field_list END     {$$ = instrec($1, $2);}
  simpletype :  IDENTIFIER   { $$ = findtype($1); }
             |  LPAREN idlist RPAREN {$$ = instenum($2);}
             |  dotdottype
             ;
  simpletypelist :  simpletype COMMA simpletypelist { $$ = cons($1, $3); }
             |  simpletype                { $$ = cons($1, NULL); }
             ;
  dotdottype :  constant_type DOTDOT constant_type     {$$ = instdotdot($1, $2, $3);}
  block      :  BEGINBEGIN statement endpart   { $$ = makeprogn($1,cons($2, $3)); }  
             ;
  statement  :  BEGINBEGIN statement endpart   { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  assignment
             |  IDENTIFIER LPAREN expression_list RPAREN    { $$ = makefuncall($2, $1, $3); }
             |  FOR assignment TO expr DO statement   { $$ = makefor(1, $1, $2, $3, $4, $5, $6); }
             |  REPEAT statement_list UNTIL expr              { $$ = makerepeat($1, $2, $3, $4); }
             |  WHILE expr DO statement      {$$ = makewhile($1, $2, $3, $4);}
             |  goto
             |  NUMBER COLON statement     {$$ = dolabel($1, $2, $3);}
             ;
  goto       :  GOTO NUMBER   {$$ = dogoto($1, $2);}
  expression_list  :  expr COMMA expression_list           { $$ = cons($1, $3); }
                  |  expr
                  ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; } %prec thenthen
             ;
  assignment :  variable ASSIGN expr         { $$ = binop($2, $1, $3); }
             ;
  variable   :  IDENTIFIER                            { $$ = findid($1); }
             |  variable DOT IDENTIFIER                    {$$ = reducedot($1, $2, $3);}
             |  variable POINT                        { $$ = dopoint($1, $2);}
             |  variable LBRACKET expression_list RBRACKET {$$ = arrayref($1, $2, $3, $4);}
             ;
  binary_ops  :  PLUS | MINUS | OR | EQ | LT | GT | NE | LE | GE | IN;
  expr       :  term binary_ops expr          { $$ = binop($2, $1, $3); }
             |  sign term                          { $$ = unaryop($1, $2); };
             |  term
             ;
  term       : term TIMES factor              { $$ = binop($2, $1, $3); }
             | term DIVIDE factor              { $$ = binop($2, $1, $3); }
             | term DIV factor                 { $$ = binop($2, $1, $3); }
             | term MOD factor                 { $$ = binop($2, $1, $3); }
             | term AND factor                 { $$ = binop($2, $1, $3); }
             | factor
             ;
  factor     :  NUMBER
             |  NIL
             |  STRING
             |  LPAREN expr RPAREN             { $$ = $2; }      
             |  IDENTIFIER LPAREN expression_list RPAREN    { $$ = makefuncall($2, $1, $3); }
             |  NOT factor          { $$ = unaryop($1, $2); }
             |  variable
             ;
%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.

   To add more flags, use the next power of 2: the next one would be 32.
   To turn on all flags, set DEBUG to the next power of 2, minus 1.
  */

#define DEBUG        0             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

int labelnumber = 0;  /* sequential counter for internal label numbers */
int labels[50];
   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN unaryop(TOKEN op, TOKEN lhs) {
  op->operands = lhs;
  lhs->link = NULL;
  return op;  
}

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN nconc(TOKEN lista, TOKEN listb) {
  if (!lista) return listb; // Return listb directly if lista is NULL
  TOKEN current = lista;
  while (current->link != NULL) { // Traverse to the end of lista
    current = current->link;
  }
  current->link = listb;
  return lista; // Return the modified lista
}

TOKEN makeintc(int number) {
  TOKEN token = talloc();
  token->tokentype = NUMBERTOK;
  token->basicdt = INTEGER;
  token->intval = number;
  return token;
}

TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  if (!var) return NULL;
  TOKEN newArefOp;
  if (var->whichval != AREFOP) {
    newArefOp = makeop(AREFOP);
    newArefOp->operands = var;
    var->link = off;

    newArefOp->symentry = var->symentry;
    newArefOp->basicdt = var->symentry->datatype->basicdt;
  } else {
    TOKEN newPlusOp = makeop(PLUSOP);
    TOKEN currentOff = var->operands->link;

    newPlusOp->operands = currentOff;
    currentOff->link = off;

    var->operands->link = newPlusOp;
    var->basicdt = var->symentry->datatype->basicdt;
  }

  return var->whichval == AREFOP ? var : newArefOp;
}


TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
    // Create the beginning label for the loop
    TOKEN startLabel = makelabel();
    int startLabelNum = labelnumber - 1; // Assuming 'labelnumber' is globally maintained

    // Create a progn block that starts with this label
    TOKEN loopProgn = makeprogn(tok, startLabel);

    TOKEN gotoStart = makegoto(startLabelNum);
    statement->link = gotoStart;
    TOKEN loopBody = makeprogn(tokb, statement);

    TOKEN ifStatement = makeif(talloc(), expr, loopBody, NULL);
    startLabel->link = ifStatement;
    return loopProgn;
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {
    if (rhs->whichval == (NIL - RESERVED_BIAS)) {
      rhs = makeintc(0);
    }

    op->operands = lhs;
    lhs->link = rhs;
    rhs->link = NULL; // Ensure the operand list is properly terminated

    if (lhs->basicdt == INTEGER && rhs->basicdt == REAL && op->whichval == ASSIGNOP) {
        op->basicdt = INTEGER;
        printf("Rohan Vijay Mhetar \n");
        TOKEN fixRhs = makefix(rhs);
        lhs->link = fixRhs; // Correctly link the fixed rhs
    }

    else if (lhs->basicdt == REAL && rhs->basicdt == INTEGER && op->whichval == ASSIGNOP) {
        op->basicdt = REAL;
        TOKEN floatRhs = makefloat(rhs);
        lhs->link = floatRhs; // Correctly link the fixed rhs
    }
    else if (lhs->basicdt == REAL || rhs->basicdt == REAL) {
        op->basicdt = REAL;
        if (lhs->basicdt == INTEGER) {
            TOKEN floatLhs = makefloat(lhs);
            op->operands = floatLhs; // Update the lhs to the converted token
            floatLhs->link = rhs;
        }
        if (rhs->basicdt == INTEGER) {
            TOKEN floatRhs = makefloat(rhs);
            lhs->link = floatRhs; // Update the rhs in the operands chain
        }
    } else if (lhs->basicdt == INTEGER && rhs->basicdt == INTEGER) {
        op->basicdt = INTEGER; // Both operands are integer, no conversion needed
    }

    if (DEBUG & DB_BINOP) {
        printf("binop\n");
        dbugprinttok(op);
        dbugprinttok(lhs);
        dbugprinttok(rhs);
    }

    return op;
}

TOKEN makefloat(TOKEN tok) {
    if (tok->tokentype == NUMBERTOK) {
        tok->basicdt = REAL;
        tok->realval = (double) tok->intval;
    } else {
        TOKEN floatop = makeop(FLOATOP);
        floatop->operands = tok;
        tok = floatop;
    }
    return tok;
}


TOKEN makefix(TOKEN tok) {
    if (tok->tokentype == NUMBERTOK) {
        tok->basicdt = INTEGER;
        tok->intval = (int) tok->realval;
    } else {
        TOKEN fixop = makeop(FIXOP);
        fixop->operands = tok;
        tok = fixop;
    }
    return tok;
}

void instconst(TOKEN idtok, TOKEN consttok) {
    SYMBOL sym = insertsym(idtok->stringval);
    sym->kind = CONSTSYM;              
    sym->basicdt = consttok->basicdt;

    switch (sym->basicdt) {
        case REAL:
            sym->constval.realnum = consttok->realval; // Assign real number value
            break;
        case INTEGER:
            sym->constval.intnum = consttok->intval; // Assign integer value
            break;
    }
}


/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num) {
  labels[labelnumber++] = num->intval;  
}

TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
    TOKEN label = makelabel();
    tok = makeprogn(tok, label); // Start with a label

    TOKEN loopBody = makeprogn((TOKEN) talloc(), statements);
    label->link = loopBody; // Link the loop body to the label

    TOKEN gotoToken = makegoto(labelnumber - 1); // Goto token to loop back

    TOKEN noop = makeprogn((TOKEN) talloc(), NULL); // No-op for the 'then' part

    TOKEN ifStructure = makeif((TOKEN) talloc(), expr, noop, gotoToken);
    // Properly link the if structure after the loop body
    loopBody->link = makeprogn((TOKEN) talloc(), ifStructure);

    return tok;
}

TOKEN instenum(TOKEN idlist) {
    int ordValue = 0;
    TOKEN curId = copytok(idlist);

    while (curId) {
        instconst(curId, makeintc(ordValue++));
        curId = curId->link;
    }

    return makesubrange(copytok(idlist), 0, ordValue - 1);
}

TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  return makesubrange(dottok, lowtok->intval, hightok->intval);
}

TOKEN instarray(TOKEN bounds, TOKEN typetok) {
    if (bounds->link) {
        // Recursively handle nested array dimensions
        typetok = instarray(bounds->link, typetok);
    }

    SYMBOL subrange = bounds->symtype;
    SYMBOL typesym = typetok->symtype;
    SYMBOL arraysym = symalloc();

    arraysym->kind = ARRAYSYM;
    arraysym->datatype = typesym;
    arraysym->lowbound = subrange->lowbound;
    arraysym->highbound = subrange->highbound;

    if (bounds->link) {
        arraysym->size = (arraysym->lowbound + arraysym->highbound - 1) * typesym->size;
    } else {
        arraysym->size = (arraysym->highbound - arraysym->lowbound + 1) * typesym->size;
    }

    typetok->symtype = arraysym;

    return typetok;
}

TOKEN instfields(TOKEN idlist, TOKEN typetok) {
    //printf("come on bro i need to know \n");
    SYMBOL fieldType = typetok->symtype;

    for (TOKEN currentField = idlist; currentField != NULL; currentField = currentField->link) {
        currentField->symtype = fieldType;
    }

    return idlist; // Return the updated list of identifier tokens
}

TOKEN instrec(TOKEN rectok, TOKEN argstok) {
    // Allocate symbol table entry for the record
    SYMBOL recordSym = symalloc();
    recordSym->kind = RECORDSYM; // Set kind to record
    int totalOffset = 0; // Initialize total offset for field placement

    SYMBOL lastField = NULL; // Keep track of the last field added

    // Iterate through each field token, setting up its symbol entry
    for (TOKEN fieldToken = argstok; fieldToken != NULL; fieldToken = fieldToken->link) {
        int fieldAlign = alignsize(fieldToken->symtype);
        SYMBOL fieldSym = makesym(fieldToken->stringval);
        fieldSym->datatype = fieldToken->symtype;
        fieldSym->offset = wordaddress(totalOffset, fieldAlign);
        fieldSym->size = fieldToken->symtype->size;
        totalOffset = fieldSym->offset + fieldSym->size;

        if (lastField == NULL) {
            recordSym->datatype = fieldSym; // First field becomes datatype of record
        } else {
            lastField->link = fieldSym; // Link previous field to current
        }
        lastField = fieldSym; // Update last field to current
    }

    recordSym->size = wordaddress(totalOffset, 16);
    rectok->symtype = recordSym; // Attach the record symbol to the return token

    return rectok;
}

TOKEN instpoint(TOKEN tok, TOKEN typename) {
    //printf("has to be here right? \n\n\n");
    SYMBOL targetTypeSym = searchins(typename->stringval);

    SYMBOL pointerSym = symalloc();
    pointerSym->datatype = targetTypeSym; // Link to the target type symbol
    pointerSym->size = basicsizes[POINTER]; // Assign the standard size for a pointer
    pointerSym->basicdt = POINTER; // Set the basic data type as POINTER
    pointerSym->kind = POINTERSYM; // Specify the symbol kind as a pointer

    tok->symtype = pointerSym;

    return tok;
}

void insttype(TOKEN typename, TOKEN typetok) {
    // Look up the type name in the symbol table or insert it if not found
    //printf("at least we are here : %s %s\n", typename->stringval, typetok->stringval);
    SYMBOL newTypeSym = searchins(typename->stringval);
    newTypeSym->kind = TYPESYM;
    newTypeSym->datatype = typetok->symtype; // Link to the symbol table entry for the type
    newTypeSym->size = typetok->symtype->size; // Set the size based on the linked type
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

TOKEN makeop(int op) {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = op;
    return tok;
}

TOKEN copytok(TOKEN target) {
    TOKEN copy = talloc();
    *copy = *target;
    return copy;
}

TOKEN makelabel() {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = LABELOP;

    TOKEN numToken = talloc();
    numToken->tokentype = NUMBERTOK;
    numToken->basicdt = INTEGER;
    numToken->intval = labelnumber++;

    tok->operands = numToken;
    return tok;
}

TOKEN makegoto(int num) {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = GOTOOP;

    TOKEN numToken = talloc();
    numToken->tokentype = NUMBERTOK;
    numToken->basicdt = INTEGER;
    numToken->intval = num;

    tok->operands = numToken;
    return tok;
}

TOKEN makefor(int sign, TOKEN tok, TOKEN assign, TOKEN tokb, TOKEN expr, TOKEN tokc, TOKEN statements) {
    tok = makeprogn(talloc(), assign);

    TOKEN label = makelabel();
    assign->link = label;

    TOKEN body = talloc();
    body = makeprogn(body, statements);

    TOKEN loopCondition = makeop(sign == 1 ? LEOP : GEOP);
    loopCondition->operands = copytok(assign->operands);
    loopCondition->operands->link = expr;

    TOKEN ifCondition = makeif(talloc(), loopCondition, body, NULL);

    // Creating a chain for increment operation
    TOKEN incrementOperation = makeop(PLUSOP);
    incrementOperation->operands = copytok(assign->operands);
    TOKEN one = talloc();
    one->tokentype = NUMBERTOK;
    one->basicdt = INTEGER;
    one->intval = 1;
    incrementOperation->operands->link = one;

    TOKEN increment = makeop(ASSIGNOP);
    increment->operands = copytok(assign->operands);
    increment->operands->link = incrementOperation;


    //nested for loop
    if (statements->tokentype == OPERATOR && statements->whichval == PROGNOP) {
        TOKEN lastInChain = statements;
        while (lastInChain->link) {
          lastInChain = lastInChain->link;
        }
        lastInChain->link = increment;
    } else {
        body->operands->link = increment; // Appending increment to the do block directly
    }

    TOKEN gotoLabel = makegoto(label->operands->intval);
    increment->link = gotoLabel;

    label->link = ifCondition;

    return tok;
}

TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
    tok->tokentype = OPERATOR;
    tok->whichval = FUNCALLOP;
    tok->operands = fn;

    SYMBOL sym, typ;        /* symbol table entry and its type */

    sym = searchst(fn->stringval);
    tok->symentry = sym;
    typ = sym->datatype;
    tok->symtype = typ;
    tok->basicdt = sym->datatype->basicdt;

    if (strcmp(fn->stringval, "new") == 0) {
        tok = makeop(ASSIGNOP); // Change the operation to an assignment
        tok->operands = args; // Directly assign the arguments to the operation

        SYMBOL typsym = args->symtype->datatype;
        TOKEN sizeToken = makeintc(typsym->size);

        TOKEN funcallToken = talloc();
        funcallToken->tokentype = OPERATOR;
        funcallToken->whichval = FUNCALLOP;
        funcallToken->operands = fn;
        fn->link = sizeToken;
        args->link = funcallToken;
    } else if (strcmp(fn->stringval, "writeln") == 0) {
        if (args->basicdt == REAL) {
            strcpy(fn->stringval, "writelnf"); // Use floating-point version
        } else if (args->tokentype == STRINGTOK) {
            strcpy(fn->stringval, "writeln"); // Use string version (no change needed)
        } else {
            strcpy(fn->stringval, "writelni"); // Use integer version
        }
        fn->link = args; // Link the arguments to the function name token
    } else {
        // Default handling for all other functions
        fn->link = args; // Simply link the arguments to the function name token
    }

    return tok; // Return the constructed function call token.
}

TOKEN makesubrange(TOKEN tok, int low, int high) {
    // Allocate and set up the subrange symbol
    SYMBOL newSubrange = symalloc();
    newSubrange->kind = SUBRANGE;
    newSubrange->basicdt = INTEGER;
    newSubrange->lowbound = low;
    newSubrange->highbound = high;
    newSubrange->size = basicsizes[INTEGER];

    tok->symtype = newSubrange;

    return tok;
}

int findlabelnumber(int targetLabel) {
    for (int index = 0; index < labelnumber; ++index) {
        if (labels[index] == targetLabel) {
            return index; // Return the index at which the label was found
        }
    }
    return -1; // Return -1 to indicate the label was not found
}

TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
    SYMBOL fSym = var->symentry->datatype->datatype;
    int fOff = 0;

    while (fSym) {
        if (!strcmp(fSym->namestring, field->stringval)) {
            fOff = fSym->offset;
            var->symentry = fSym;
            break;
        }
        fSym = fSym->link;
    }

    return makearef(var, makeintc(fOff), dot);
}

TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
    int lowBound = arr->symtype->lowbound;
    int highBound = arr->symtype->highbound;
    int elementSize = arr->symtype->size / (highBound - lowBound + 1);
    int adjustedSize = -1 * elementSize * lowBound;

    // Create the times operation for subscript calculations
    TOKEN timesOp = makeop(TIMESOP);
    TOKEN eleSizeToken = makeintc(elementSize);
    eleSizeToken->link = copytok(subs); // Use a copy of subs for multiplication
    timesOp->operands = eleSizeToken;

    // Adjust for the low bound
    TOKEN adjustedSizeToken = makeintc(adjustedSize);
    adjustedSizeToken->link = timesOp;
    TOKEN plusOp = makeop(PLUSOP);
    plusOp->operands = adjustedSizeToken;

    // Handle recursive case for multi-dimensional arrays
    if (subs->link) {
        TOKEN subArrayRef = makearef(arr, plusOp, tokb);
        subArrayRef->symtype = arr->symtype->datatype; // Update symbol type
        return arrayref(subArrayRef, tok, subs->link, tokb); // Recursive call for next dimension
    } else {
        return makearef(arr, plusOp, tokb); // Directly return the array reference
    }
}

TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
    int labelIndex = findlabelnumber(labeltok->intval);
    if (labelIndex == -1) {
        printf("Error: User-defined label %d not found.\n", labeltok->intval);
    } else {
        labeltok = makeop(LABELOP);
        TOKEN labelIndexToken = makeintc(labelIndex);
        labeltok->operands = labelIndexToken;
        // Link the label operation to the statement
        labeltok->link = statement;
        // Use the recycled token to create a 'progn' token that encapsulates the label-statement
        tok = makeprogn(tok, labeltok);
    }

    return tok; // Return the 'progn' token with the label and statement
}

TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
    int labelIndex = findlabelnumber(labeltok->intval);
    if (labelIndex == -1) {
        printf("Error: User-defined label %d not found.\n", labeltok->intval);
    } else {
        tok = makegoto(labelIndex);
    }

    return tok; // Return the goto token, regardless of label validity
}

TOKEN dopoint(TOKEN var, TOKEN tok) {
    SYMBOL sym = var->symentry;
    tok->symentry = sym->datatype->datatype;
    tok->operands = var;

    return tok; // Return the token with the dereference operation applied.
}

TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
    TOKEN tok = talloc();
    tok->whichval = PROGRAMOP;
    tok->tokentype = OPERATOR;

    TOKEN linker = makeprogn(talloc(), args);
    linker->link = statements;
    name->link = linker;
    tok->operands = name;
    return tok;
}

TOKEN findtype(TOKEN tok) {
    SYMBOL s = searchst(tok->stringval);

    if (s->kind == TYPESYM) {
      s = s->datatype;
    }

    tok->symtype = s;
    return tok;
}

TOKEN findid(TOKEN tok) { /* the ID token */
    SYMBOL sym = searchst(tok->stringval);
    tok->symentry = sym;
    if (sym->kind == CONSTSYM) {
        tok->tokentype = NUMBERTOK;
        tok->basicdt = sym->basicdt;
       
        switch (sym->basicdt) {
            case REAL:
                tok->realval = sym->constval.realnum;
                break;
            case INTEGER:
                tok->intval = sym->constval.intnum;
                break;
        }
        return tok;
    }

    SYMBOL typ = sym->datatype;
    tok->symtype = typ;
    if (typ->kind == BASICTYPE || typ->kind == POINTERSYM) {
        tok->basicdt = typ->basicdt;
    }
    return tok;
}

void instvars(TOKEN idlist, TOKEN typetok)
  {
    SYMBOL sym, typesym; int align;
     typesym = typetok->symtype;
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
    printf("yyparse result = %8d\n", res);
    printstlevel(1);    /* to see level 0 too, change to:   printst();  */
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /*
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }
