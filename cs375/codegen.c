/* codgen.c       Generate Assembly Code for x86         07 May 18   */

/* Copyright (c) 2018 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "symtab.h"
#include "lexan.h"
#include "genasm.h"
#include "codegen.h"
#include "pprint.h"

void genc(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */
int registers[64];
int integer[64];
int real[64];
int pointer[64];
int instantiate[64];

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */

void gencode(TOKEN pcode, int varsize, int maxlabel)
  {  
     integer[EQOP] = CMPL;
     integer[LEOP] = CMPL;
     integer[LTOP] = CMPL;
     integer[GEOP] = CMPL;
     integer[NEOP] = CMPL;
     integer[GTOP] = CMPL;
     integer[OROP] = ORL;
     integer[PLUSOP] = ADDL;
     integer[ANDOP] = ANDL;
     integer[DIVIDEOP] = DIVL;
     integer[MINUSOP] = SUBL;
     integer[TIMESOP] = IMULL;

     real[EQOP] = CMPSD;
     real[LEOP] = CMPSD;
     real[LTOP] = CMPSD;
     real[GEOP] = CMPSD;
     real[NEOP] = CMPSD;
     real[GTOP] = CMPSD;
     real[PLUSOP] = ADDSD;
     real[DIVIDEOP] = DIVSD;
     real[MINUSOP] = SUBSD;
     real[TIMESOP] = MULSD;
     real[NOTOP] = NEGSD;

     pointer[EQOP] = CMPQ;
     pointer[LEOP] = CMPQ;
     pointer[LTOP] = CMPQ;
     pointer[GEOP] = CMPQ;
     pointer[NEOP] = CMPQ;
     pointer[GTOP] = CMPQ;
     pointer[OROP] = ORQ;
     pointer[PLUSOP] = ADDQ;
     pointer[MINUSOP] = SUBQ;
     pointer[TIMESOP] = IMULQ;
     pointer[ANDOP] = ANDQ;
     pointer[NOTOP] = NOTQ;
     pointer[OROP] = ORQ;

     instantiate[EQOP] = JE;
     instantiate[NEOP] = JNE;
     instantiate[LTOP] = JL;
     instantiate[LEOP] = JLE;
     instantiate[GEOP] = JGE;
     instantiate[GTOP] = JG;

     TOKEN name, code;
     name = pcode->operands;
     code = name->link->link;
     nextlabel = maxlabel + 1;
     stkframesize = asmentry(name->stringval,varsize);
     genc(code);
     asmexit(name->stringval);
  }

/* Trivial version: always returns RBASE + 0 */
/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind)
  {
    /*     ***** fix this *****   */
     if (kind != 3) {
        for (int i = RBASE; i < RMAX; i++) {
            if (registers[i] == 0) {
                registers[i] = 1;
                return i;
            }
        }
     }
     for (int i = FBASE; i < FMAX; i++) {
        if (registers[i] == 0) {
            registers[i] = 1;
            return i;
        }
    }
    return RBASE;
  }

/* test if there is a function call within code: 1 if true, else 0 */
int funcallin(TOKEN code) {
  if (code->whichval == FUNCALLOP) {
    return 1;
  }
  if (code->link) {
    return funcallin(code->link);
  }
  return 0;
}

/* Generate code for a function call */
int genfun(TOKEN code) {
  TOKEN op = code->operands;
  TOKEN lhs = op->link;
  while (lhs) {
    genarith(lhs);
    lhs = lhs->link;
  }
  asmcall(op->stringval);
  SYMBOL str = searchst(op->stringval);
  if (str->datatype->basicdt == INTEGER) {
    return EAX;
  } else if (str->datatype->basicdt == REAL) {
    return XMM0;
  } 
  return RAX;
}

/* Generate code for array references and pointers */
/* In Pascal, a (^ ...) can only occur as first argument of an aref. */
/* If storereg < 0, generates a load and returns register number;
   else, generates a store from storereg. */
int genaref(TOKEN code, int storereg) {
  int reg = genarith(code->operands->link);
  asmop(CLTQ);
}

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  {   int num, reg, arith;
     if (DEBUGGEN)
       { printf("genarith\n");
	 dbugprinttok(code);
       };
      switch ( code->tokentype ) { 
        case NUMBERTOK:
           switch (code->basicdt) { 
              case INTEGER:
                reg = getreg(HALFWORD);
                num = code->intval;
                if (num <= MAXIMMEDIATE && num >= MINIMMEDIATE) {
                  asmimmed(MOVL, num, reg);
                }
                break;
              case REAL:
                reg = getreg(FLOAT);
                int label = nextlabel++;
                makeflit(code->realval, label);
                asmldflit(MOVSD, label, reg);
                break;
             }
             break;
        case IDENTIFIERTOK:
           switch(code->basicdt) {
            case INTEGER:
              reg = getreg(HALFWORD);
              asmld(MOVL, code->symentry->offset - stkframesize, reg, code->stringval);
              break;
            case REAL:
              reg = getreg(FLOAT);
              asmld(MOVSD, code->symentry->offset - stkframesize, reg, code->stringval);
              break;
            case POINTER:
              reg = getreg(HALFWORD);
              asmld(MOVQ, code->symentry->offset - stkframesize, reg, "");
              break;
           }
           break;
        case OPERATOR:
           switch(code->whichval) {
              case AREFOP:
                reg = genaref(code, 0);
                break;
              case FUNCALLOP:
                reg = genfun(code);
                break;
              case FIXOP:
                reg = getreg(HALFWORD);
                arith = genarith(code->operands);
                asmfloat(arith, reg);
                registers[arith] = 0;
                break;
              case FLOATOP:
                reg = getreg(FLOAT);
                arith = genarith(code->operands);
                asmfloat(arith, reg);
                registers[arith] = 0;
                break;
              default:
                reg = genarith(code->operands);
                if (code->operands->link) {
                  arith = genarith(code->operands->link);
                  if (code->operands->link && funcallin(code->operands->link)) {
                    asmsttemp(reg);
                    registers[arith] = 0;
                    asmldtemp(reg);
                  }
                  if (code->basicdt == INTEGER) {
                    asmrr(integer[code->whichval], arith, reg);
                  } else if (code->basicdt == REAL) {
                    asmrr(real[code->whichval], arith, reg);
                  }
                  registers[arith] = 0;
                } else {
                  arith = getreg(FLOAT);
                  asmfneg(reg, arith);
                  reg = arith;
                  registers[arith] = 0;
                }
                break;
           }
           break;
       }
       return reg;
    }


/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
  {  TOKEN tok, lhs, rhs;
     int reg, offs;
     SYMBOL sym;
     if (DEBUGGEN)
       { printf("genc\n");
	 dbugprinttok(code);
       };
     if ( code->tokentype != OPERATOR )
        { printf("Bad code token");
	  dbugprinttok(code);
	};
  for (int i = 0; i < 64; i++) { 
    registers[i] = 0;
  }
  switch ( code->whichval ) { 
    case PROGNOP:
      tok = code->operands;
      while ( tok != NULL ) {  
        genc(tok);
        tok = tok->link;
      };
      break;
    case ASSIGNOP:                   /* Trivial version: handles I := e */
      lhs = code->operands;
      rhs = lhs->link;
      reg = genarith(rhs);              /* generate rhs into a register */
      sym = lhs->symentry;              /* assumes lhs is a simple var  */
      offs = sym->offset - stkframesize; /* net offset of the var   */
      switch (code->basicdt) {           /* store value into lhs  */ 
          case INTEGER:
            asmst(MOVL, reg, offs, lhs->stringval);
            break;
          case REAL:
            asmst(MOVSD, reg, offs, lhs->stringval);
            break;
        };
      break;
	 case FUNCALLOP:
     genfun(code);
	   break;
	 case GOTOOP:
     asmjump(JMP, code->operands->intval);
	   break;
	 case LABELOP:
     asmlabel(code->operands->intval);
	   break;
	 case IFOP:
     tok = code->operands;
     lhs = tok->link;
     rhs = lhs->link;
     reg = genarith(tok);
     int label = nextlabel++;
     asmjump(instantiate[tok->whichval], label);
     if (rhs) {
      genc(rhs);
     }
     int label2 = nextlabel++;
     asmjump(JMP, label2);
     asmlabel(label);
     genc(lhs);
     asmlabel(label2);
	   break;
	 };
  }
