/* lex1.c         14 Feb 01; 31 May 12; 11 Jan 18; 20 Jan 24       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2024 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"

extern int CHARCLASS[];

static char* opprnt[]  = {" ", "+", "-", "*", "/", ":=", "=", "<>", "<", "<=",
                          ">=", ">",  "^", ".", "and", "or", "not", "div",
                          "mod", "in", "if", "goto", "progn", "label",
                          "funcall", "aref", "program", "float"};
static char *delprnt[] = { "  ", ",", ";", ":", "(", ")", "[", "]",
                           ".."} ;
static char *resprnt[] = { " ", "array", "begin", "case", "const", "do",
                           "downto", "else", "end", "file", "for",
		           "function", "goto", "if", "label", "nil",
                           "of", "packed", "procedure", "program", "record",
                           "repeat", "set", "then", "to", "type",
		           "until", "var", "while", "with" };

/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
   */

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks ()
  {
    int c;
    while ((c = peekchar()) != EOF) {
      if ((c == ' ' || c == '\n' || c == '\t')) {
        getchar();
      } else if (c == '{' || (c == '(' && (peek2char()) == '*')) {
        if (c == '(') {
          getchar();
        } 
        getchar(); 
        while (((c = peekchar()) != EOF) && (c != '}') && (c != '*' || (peek2char()) != ')')) {
          getchar();
        }
        if (c != EOF) {
          if (c == '*') {
            getchar();
          } 
          getchar(); 
        }
      } else {
        return; 
      }
    }
  }

/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok) 
  {
    int c;
    int count = 0;
    char s[15];
    while ((c = peekchar()) != EOF && CHARCLASS[c] == ALPHA) {
      if (count < 15) {
        s[count] = c;
      } else if (count == 15) {
        s[count] = '\0';
      }
      getchar();
      count++;
    }
    if (count < 15) {
      s[count] = '\0';
    }
    for (int i = 0; i < sizeof(opprnt) / sizeof(opprnt[i]); i++) {
      if (!strcmp(s, opprnt[i])) {
        tok->whichval = i;
        tok->tokentype = OPERATOR;
        return tok;
      }
    }
    for (int i = 0; i < sizeof(resprnt) / sizeof(resprnt[i]); i++) {
      if (!strcmp(s, resprnt[i])) {
        tok->whichval = i;
        tok->tokentype = RESERVED;
        return tok;
      }
    }
    strcpy(tok->stringval, s);
    tok->tokentype = IDENTIFIERTOK;
    return tok;
  }

TOKEN getstring (TOKEN tok)
  {
    int c;
    int count = 0;
    char s[15];
    getchar();
    while ((c = peekchar()) != EOF && c != '\n') {
      if (c == '\'' && peek2char() == '\'') {
        getchar();
      }
      if (count < 15) {
        s[count] = c;
      } else if (count == 15) {
        s[count] = '\0';
      }
      getchar();
      count++;
    }
    if (count <= 15) {
      s[count-1] = '\0';
    }
    tok->tokentype = STRINGTOK;
    strcpy(tok->stringval, s);
    return tok;
  }

TOKEN special (TOKEN tok)
  {
    int c;
    int count = 0;
    char s[2];
    while ((c = peekchar()) != EOF && CHARCLASS[c] == SPECIAL) {
      s[count] = getchar();
      count++;
    }
    s[count] = '\0';
    for (int i = 0; i < sizeof(opprnt) / sizeof(opprnt[i]); i++) {
      if (!strcmp(s, opprnt[i])) {
        tok->whichval = i;
        tok->tokentype = OPERATOR;
        return tok;
      }
    }
    for (int i = 0; i < sizeof(delprnt) / sizeof(delprnt[i]); i++) {
      if (!strcmp(s, delprnt[i])) {
        tok->whichval = i;
        tok->tokentype = DELIMITER;
        return tok;
      }
    }
    return tok;
  }

/* Get and convert unsigned numbers of all types. */
TOKEN number (TOKEN tok)
  { 
    long num = 0;
    double flt;
    int  c, charval;
    int negative = 0;
    int special = 0;
    int place = 0;
    int count = -1;
    int exp = 0;
    int err = 0;
    
    while ( (c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {   
      c = getchar();
      charval = (c - '0');
      num = num * 10 + charval;
      if (num > 2147483647) {
        exp++;
        tok->tokentype = NUMBERTOK;
        tok->basicdt = INTEGER;
        tok->intval = num /= 10;
        err = 1;
      } else {
        count++;
      }
    }
    if (c == '.' && CHARCLASS[peek2char()] == NUMERIC) {
      place = 1;
      special = getchar();
      while ( (c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
        c = getchar();
        charval = (c - '0');
        double tiny = (double) charval;
        for (int i = 0; i < place; i++) {
          tiny /= 10;
        }
        place++;
        flt += tiny;
      }
      place = 0;
    }
    if (c == 'e') {
      special = special == '.' ? 1 : 'e';
      getchar();
      if (peekchar() == '-' || peekchar() == '+') {
        if (peekchar() == '-') {
          negative = 1;
          exp *= -1;
        }
        getchar();
      }
      while ( (c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
        c = getchar();
        charval = (c - '0');
        place = place * 10 + charval;
      }
      place += exp;
    }
    if (special == '.') {
      flt += num;
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = flt;
      return tok;
    } else if (special == 'e') {
      flt = num;
      if (negative) {
        for (int i = 0; i < place; i++) {
          flt /= 10;
        }
      } else {
        for (int i = 0; i < place; i++) {
          flt *= 10;
        }
      }
      if (place < -38 || place > 38) {
        tok->tokentype = NUMBERTOK;
        tok->basicdt = REAL;
        tok->realval = 0;
        printf("Floating number out of range\n");
        return tok;
      }
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = flt;
      return tok;
    } else if (special) {
      flt += num;
      for (int i = 0; i < count; i++) {
        flt /= 10;
        place--;
      }
      if (place < -38 || place > 38) {
        tok->tokentype = NUMBERTOK;
        tok->basicdt = REAL;
        tok->realval = 0;
        printf("Floating number out of range\n");
        return tok;
      }
      if (negative) {
        for (int i = 0; i < place; i++) {
          flt /= 10;
        }
      } else {
        for (int i = 0; i < place; i++) {
          flt *= 10;
        }
      }
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = flt;
      return tok;
    } else if (err) {
      printf("Integer number out of range\n");
      return tok;
    }
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    tok->intval = num;
    return (tok);
  }

