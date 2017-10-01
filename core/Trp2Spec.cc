/***************************************************************************
Copyright (c) 2012, Martin Suda
Max-Planck-Institut für Informatik, Saarbrücken, Germany

Copyright (c) 2006 - 2011, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***************************************************************************/

#define TRANSLATE 0    // 0 no-translate, 2 - gore, 3 - workbench

#if (TRANSLATE == 2)

#define EXTENSION ".gore"

#elif (TRANSLATE == 3)

#define EXTENSION ".wb"

#endif

#include "core/Trp2Spec.h"

#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#include <string>
#include <map>

using namespace Minisat;
     
static void
msg (const char *fmt, ...)
{
  va_list ap;
  fputs ("[trp2spec] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
wrn (const char *fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fputs ("[trp2spec] WARNING ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
die (const char *fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fputs ("*** [trp2spec] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  exit (1);
}

typedef enum {
  TOKEN_NONE,
  TOKEN_EOF,
  TOKEN_LPAR,
  TOKEN_RPAR,
  TOKEN_LBR,
  TOKEN_RBR,
  TOKEN_COMMA,
  TOKEN_DOT,
  TOKEN_TEXT,
  TOKEN_WHITE,
  TOKEN_ERROR
} TokenType;

#define IDENTBUF_SIZE 32

#if TRANSLATE   
static FILE *out_file;
#endif

static FILE *file;
static unsigned line_no;
static char last_char;
static TokenType last_token;
static char last_ident[IDENTBUF_SIZE];

static TokenType classifyNextChar(char* char_read) {
  char c;
  
  if (last_char != '\0') {
    c = last_char;
    last_char = '\0';       //last_char read once
  } else
    c = getc(file);

  *char_read = c;
    
  switch (c) {
    case EOF:
      return TOKEN_EOF;
      
    case '(':
      return TOKEN_LPAR;
     
    case ')':
      return TOKEN_RPAR;
      
    case '[':
      return TOKEN_LBR;
        
    case ']':
      return TOKEN_RBR;      
  
    case ',':
      return TOKEN_COMMA;    
     
    case '.':
      return TOKEN_DOT;         
     
    default:
      if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c == '_'))
        return TOKEN_TEXT;
      
      if (c == ' '  || c == '\t' || c == '\r') 
        return TOKEN_WHITE;
        
      if ( c == '\n') {
        line_no++;
        return TOKEN_WHITE;
      }
        
      return TOKEN_ERROR;
  }
}

static void lexPutback(char c) {
  last_char = c; // to be read again!
  if (c == '\n') //undo the line number
    line_no--;
}

static void lexInit() {
  line_no = 1;
  last_char = '\0';
  last_token = TOKEN_NONE;  
}

static void lexNextToken() {
  char last_read;
  
  while ((last_token = classifyNextChar(&last_read)) == TOKEN_WHITE);

  if (last_token == TOKEN_TEXT) {
    int i = 0;
    last_ident[i++] = last_read;
  
    while ((last_token = classifyNextChar(&last_read)) == TOKEN_TEXT) {
      last_ident[i++] = last_read;
      if (i == IDENTBUF_SIZE)
        die("Identifier too long.");
    }
          
    last_ident[i] = '\0';           
    lexPutback(last_read);                  
    last_token = TOKEN_TEXT;
  }    
}

static bool check(TokenType type) {
  return (last_token == type);
}

static bool check(const char * id) {
  return (last_token == TOKEN_TEXT) && (strcmp(id,last_ident) == 0);
}


static void expect(TokenType type) {
  if (!check(type))
    die("Syntax error on line %u, expected token %d\n",line_no,type);
}

static void expect(const char * id) {
  if (!check(id))
    die("Syntax error on line %u, expected string '%s'\n",line_no,id);
}

static std::map<std::string,int> identifiers;
static Names* pvarNames;

Var trp_ReadId() {
  expect(TOKEN_TEXT);
  
#if (TRANSLATE == 2)
  fprintf(out_file,"%s",last_ident);
#elif (TRANSLATE == 3)
  fprintf(out_file,"%s",last_ident);  
#endif
  
  if (identifiers.find(last_ident) == identifiers.end()) { // new id  
    // we start numbering from 1, so that 0 (which cannot be negated safely) is never used
    Var var = identifiers.size()+1;
    // first var's index is, however, the zero-th slot here, that's fine since we in the end shift back to start from 0
    pvarNames->push_back(std::string(last_ident));
    identifiers[last_ident] = var;
    return var;
  } else 
    return identifiers[last_ident];  
}

Lit trp_ReadLiteral() {
  Var var;
  
  if (check("not")) {

#if (TRANSLATE == 2)  
  fprintf(out_file,"~(");
#elif (TRANSLATE == 3)  
  fprintf(out_file,"~(");  
#endif  
  
    lexNextToken();    
    if (check(TOKEN_LPAR)) { //not(atom)
      lexNextToken();
      var = trp_ReadId();
      lexNextToken(),expect(TOKEN_RPAR); 
    } else { // not atom  -- allowed but ugly
      var = trp_ReadId();
    }
    
#if (TRANSLATE == 2)  
  if (sign) fprintf(out_file,")");
#elif (TRANSLATE == 3)  
  if (sign) fprintf(out_file,")");  
#endif
           
    return mkLit(var,true);
  } else {
    var = trp_ReadId();  
    
    return mkLit(var,false);
  }
}

void trp_ReadClauseCore(bool universal,vec<Lit>& data, Lit& event_lit, bool& had_next) {
  data.clear();
  event_lit = lit_Undef;
  had_next = false;
     
  expect("or");
  
#if (TRANSLATE == 2)    
      fprintf (out_file, " ( False");
#elif (TRANSLATE == 3)
      fprintf (out_file, " ( false"); 
#endif   
  
  lexNextToken(),expect(TOKEN_LPAR);
  lexNextToken(),expect(TOKEN_LBR);
  
  // we are now in the literal list
  while (true) {
    Lit lit;
  
    lexNextToken();
    if (check(TOKEN_RBR))
      break;
    
    expect(TOKEN_TEXT);
    if (check("sometime")) {
      if (!universal)
        die("sometime in a initial clause.\n");
    
      if (had_next)
        die("sometime in a step clause.\n");
    
      if (event_lit != lit_Undef)
        die("more then one eventuality literal in a clause.\n");

#if (TRANSLATE == 2)    
      fprintf (out_file, " | F ( ");
#elif (TRANSLATE == 3)
      fprintf (out_file, " v F ( "); 
#endif       
        
      lexNextToken(),expect(TOKEN_LPAR);
      
      lexNextToken();
      lit = trp_ReadLiteral();
      
      lexNextToken(),expect(TOKEN_RPAR);     
      
#if (TRANSLATE == 2)    
      fprintf (out_file, " )");
#elif (TRANSLATE == 3)
      fprintf (out_file, " )"); 
#endif 
      
      event_lit = lit;      
    } else if (check("next")) {
      had_next = true;
    
      if (!universal)
        die("next in a initial clause.\n");
    
      if (event_lit != lit_Undef)
        die("next in an eventuality clause.\n");
    
#if (TRANSLATE == 2)    
      fprintf (out_file, " | X ( ");
#elif (TRANSLATE == 3)
      fprintf (out_file, " v X ( "); 
#endif       
    
      lexNextToken(),expect(TOKEN_LPAR);
      
      lexNextToken();
      lit = trp_ReadLiteral();
      
      lexNextToken(),expect(TOKEN_RPAR);     
      
#if (TRANSLATE == 2)    
      fprintf (out_file, " )");
#elif (TRANSLATE == 3)
      fprintf (out_file, " )"); 
#endif       
      
      lit.x = -lit.x;  // special hack to encode primed literals before we know the size of the signature!
      data.push(lit);
    } else {   //possibly negated identifier 
#if (TRANSLATE == 2)    
      fprintf (out_file, " | ");
#elif (TRANSLATE == 3)
      fprintf (out_file, " v "); 
#endif      
    
      lit = trp_ReadLiteral();
      
      data.push(lit);
    }
    
    lexNextToken();
    if (!check(TOKEN_COMMA))
      break;   
  }
  expect(TOKEN_RBR);
  
#if (TRANSLATE == 2)    
      fprintf (out_file, " ) ");
#elif (TRANSLATE == 3)
      fprintf (out_file, " ) "); 
#endif     
  
  lexNextToken(),expect(TOKEN_RPAR);
}

void trp_LoadSpec(const char* input_name,
                  int &signature_size, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step,
                  Names& varNames) {
  if (input_name)
    file = fopen (input_name, "r");
  else
    file = stdin;
    
  if (!file) die ("failed to read '%s'", input_name);
  
#if TRANSLATE
  if (input_name) {
    char* output_name;
    
    output_name = (char*)malloc(sizeof(char)*(strlen(input_name)+strlen(EXTENSION)+1));
    
    output_name = strcat(strcpy(output_name,input_name),EXTENSION);
    
    out_file = fopen (output_name, "w");
    if (!out_file) die ("failed to write '%s'", output_name);
  
    free (output_name); 
  } else
    die("Input file name must be specified for translattion.\n");
#endif
  
  lexInit();
  identifiers.clear();
  varNames.clear();
  pvarNames = &varNames;
  
  lexNextToken(),expect("and");
  lexNextToken(),expect(TOKEN_LPAR);
  lexNextToken(),expect(TOKEN_LBR);
  
#if (TRANSLATE == 2)    
      fprintf (out_file, "True");
#elif (TRANSLATE == 3)
      fprintf (out_file, "solve(true"); 
#endif   
  
  // we are now in the clause list  
  while (true) {
    Lit event_lit;
    vec<Lit> clause;
    bool has_next;
  
    lexNextToken();
    if (check("always")) {
#if (TRANSLATE == 2)    
      fprintf (out_file, " & G");
#elif (TRANSLATE == 3)
      fprintf (out_file, " & G"); 
#endif     
      lexNextToken(),expect(TOKEN_LPAR);
    
      lexNextToken(),trp_ReadClauseCore(true,clause,event_lit,has_next);
    
      if (event_lit == lit_Undef) {
        if (has_next) {          
          step.push(clause);          
          //printf("Step clause:");      
        } else {                   
          universal.push(clause);          
          //printf("Universal clause:");      
        }
      } else {
        clause.push(event_lit); //let us store the event_lit as the last literal
        goal.push(clause);      // abusing goal clauses for storing eventuality clauses
      }
    
      lexNextToken(),expect(TOKEN_RPAR);
    } else if (check("or")) {
#if (TRANSLATE == 2)    
      fprintf (out_file, " & ");
#elif (TRANSLATE == 3)
      fprintf (out_file, " & "); 
#endif      
    
      trp_ReadClauseCore(false,clause,event_lit,has_next);
      
      assert(event_lit == lit_Undef);
      assert(!has_next);
      
      initial.push(clause);            
      //printf("Initial clause:");
    } else
      break;
           
    lexNextToken();
    if (!check(TOKEN_COMMA))
      break;
    
    //for (int i = 0; i < clause.size(); i++)
    //  printf("%d, ",clause[i].x);
    //printf("\n");
  }
  expect(TOKEN_RBR);
  
  lexNextToken(),expect(TOKEN_RPAR);
  lexNextToken(),expect(TOKEN_DOT);
  
#if (TRANSLATE == 2)
      fprintf (out_file, "\n");           // newline for the last clause
#elif (TRANSLATE == 3)
      fprintf (out_file, ");\nquit;\n"); //close the solve call and quit
#endif  
  
  signature_size = identifiers.size();
          
  //special treatment of the goal literals
  if (goal.size() > 0 &&  
     (goal.size() > 1 || goal[0].size() > 1)) { // single single-literal eventuality clause can be kept as is
    vec<Lit> clause;
    Var master = ++signature_size;  // we keep playing the game that 0 is not a variable index, and nextting is done via negation
  
    for (int i = 0; i < goal.size(); i++) {
      vec<Lit> &event_clause = goal[i];
      Lit event_lit = event_clause.last();
      Lit lit;
      
      Var s = ++signature_size;
      Var t = ++signature_size;
      
      // the first is the event_clause itself + one additional literal: if the goal doesn't hold now, we start tracking
      event_clause.push(mkLit(t));
      universal.push(event_clause);
      
      clause.clear(); //if tracking and not goal next, keep on tracking      
      clause.push(mkLit(t,true));      
      lit = event_lit;
      lit.x = -lit.x; // "nexted"
      clause.push(lit);
      lit = mkLit(t);
      lit.x = -lit.x; // "nexted"
      clause.push(lit);
      step.push(clause);
      
      clause.clear();
      clause.push(mkLit(s,true));      
      clause.push(mkLit(t,true));      
      lit = mkLit(s);
      lit.x = -lit.x; // "nexted"
      clause.push(lit);
      step.push(clause);
      
      //master resets s
      clause.clear();
      clause.push(mkLit(master,true));
      clause.push(mkLit(s));
      universal.push(clause);
      
      //master collects results - checks
      clause.clear();      
      clause.push(mkLit(s,true));
      lit = mkLit(master,true);
      lit.x = -lit.x; // "nexted"      
      clause.push(lit);      
      step.push(clause);         
    }  
        
    goal.clear();
    
    // single unconditional eventuality clause
    clause.clear();
    clause.push(mkLit(master));
    goal.push(clause);
  }

  // finally, since we know the signature size we can update semantics of next-literals
  // we also start using variable 0, now
  
  for (int i = 0; i < initial.size(); i++) {
    vec<Lit> &clause = initial[i];
    for (int j = 0; j < clause.size(); j++)
      clause[j].x -= 2;
  }

  for (int i = 0; i < goal.size(); i++) {
    vec<Lit> &clause = goal[i];
    for (int j = 0; j < clause.size(); j++)
      clause[j].x -= 2;
  }
  
  for (int i = 0; i < universal.size(); i++) {
    vec<Lit> &clause = universal[i];
    for (int j = 0; j < clause.size(); j++)
      clause[j].x -= 2;
  }  
  
  for (int i = 0; i < step.size(); i++) {
    vec<Lit> &clause = step[i];
    for (int j = 0; j < clause.size(); j++) {
      if (clause[j].x < 0) {
        Lit lit;
        lit.x = -clause[j].x-2;      
        clause[j] = mkLit(var(lit)+signature_size,sign(lit));
      } else {
        clause[j].x -= 2;
      }
    }
  }  
  
  if (input_name)
    fclose (file);
    
#if TRANSLATE   
  fclose (out_file); 
  exit(0);
#endif         
}
