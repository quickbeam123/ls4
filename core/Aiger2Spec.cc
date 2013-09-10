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

#define TRANSLATE 0   // 0 no-translate, 1 - trp, 2 - gore, 3 - workbench

#if (TRANSLATE == 1)

#define EXTENSION ".trp"

#elif (TRANSLATE == 2)

#define EXTENSION ".gore"

#elif (TRANSLATE == 3)

#define EXTENSION ".wb"

#endif

#include "core/Aiger2Spec.h"

using namespace Minisat;

#include <string.h>
#include <stdlib.h>
#include <limits.h>
#include <stdarg.h>

extern "C" {
#include "aiger.h"
}

static void
msg (const char *fmt, ...)
{
  va_list ap;
  fputs ("[aig2spec] ", stdout);
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
  fputs ("[aig2spec] WARNING ", stdout);
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
  fputs ("*** [aig2spec] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  exit (1);
}

#if TRANSLATE

static void
fprint_litname (FILE * file, aiger_t *aiger, unsigned lit)
{
  unsigned sign = aiger_sign(lit);
  unsigned var = aiger_lit2var(lit);
  
#if (TRANSLATE == 1)  
  if (sign) fprintf(file,"not(");
#elif (TRANSLATE == 2)  
  if (sign) fprintf(file,"~(");
#elif (TRANSLATE == 3)  
  if (sign) fprintf(file,"~(");  
#endif
  
  if (var == 0)
    fprintf(file,"z%d",var);
  else if (var <= aiger->num_inputs)
    fprintf(file,"i%d",var);
  else if (var - aiger->num_inputs <= aiger->num_latches)
    fprintf(file,"l%d",var - aiger->num_inputs);
  else if (var - aiger->num_inputs - aiger->num_latches <= aiger->num_ands)
    fprintf(file,"a%d",var - aiger->num_inputs - aiger->num_latches);
  else 
    fprintf(file,"g%d",var - aiger->num_inputs - aiger->num_latches - aiger->num_ands);

  if (sign) fprintf(file,")");    
}

#endif

static inline void aiger_NextEventuality(unsigned lit, int signature_size, int *eventuality_idx, Clauses *step, Clauses *universal, Clauses *goal,vec<Lit> *cur_clause, FILE *file,aiger_t *aiger) {
#if (TRANSLATE == 0)  
  unsigned master = aiger_var2lit(signature_size-1);
  
  if (*eventuality_idx == 0) { // the first guy gets treated differently
    ++*eventuality_idx;
    
    //master implies goal
    cur_clause->push(mkLit(aiger_lit2var(master),!aiger_sign(master)));
    cur_clause->push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
    universal->push(*cur_clause);
    cur_clause->clear();    
  
    // master infinitely often
    cur_clause->push(mkLit(aiger_lit2var(master),aiger_sign(master)));
    goal->push(*cur_clause);
    cur_clause->clear();
  } else {
    unsigned track = aiger_var2lit(signature_size-(++(*eventuality_idx)));
  
    //master and not goal imply tracking 
    cur_clause->push(mkLit(aiger_lit2var(master),!aiger_sign(master)));
    cur_clause->push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
    cur_clause->push(mkLit(aiger_lit2var(track),aiger_sign(track)));
    universal->push(*cur_clause);
    cur_clause->clear();    
  
    //tracking and not goal next imply tracking next
    cur_clause->push(mkLit(aiger_lit2var(track),!aiger_sign(track)));
    cur_clause->push(mkLit(aiger_lit2var(lit)+signature_size,aiger_sign(lit)));
    cur_clause->push(mkLit(aiger_lit2var(track)+signature_size,aiger_sign(track)));
    step->push(*cur_clause);
    cur_clause->clear();    
    
    //master next and not goal next imply not having tracked (previously)
    cur_clause->push(mkLit(aiger_lit2var(master)+signature_size,!aiger_sign(master)));
    cur_clause->push(mkLit(aiger_lit2var(lit)+signature_size,aiger_sign(lit)));
    cur_clause->push(mkLit(aiger_lit2var(track),!aiger_sign(track)));
    step->push(*cur_clause);
    cur_clause->clear();   
  }  
#elif (TRANSLATE == 1)
  if ((*eventuality_idx)++ > 0)
    fprintf (file,",\n");
  
  fprintf (file, "always(or([sometime("),
  fprint_litname(file, aiger, lit),               
  fprintf (file, ")]))");  // no comma or newline for eventuallity clauses
  
#elif (TRANSLATE == 2) 
  fprintf (file, "& G(F("),
  fprint_litname(file, aiger, lit),               
  fprintf (file,"))"); 
#elif (TRANSLATE == 3) 
  fprintf (file, "& G(F("),
  fprint_litname(file, aiger, lit),               
  fprintf (file,"))");
#endif
}

void aiger_LoadSpec(const char* input_name, int reversed, int pg, int verbose, int kth_property, int parse_liveness, int reach_as_live,
                    int &signature_size, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  const char *error;
  int recheck;
  unsigned i, * refs, lit, rhs0, rhs1, next, reset;  
  aiger_t *aiger;
  
  aiger_symbol *the_output = 0;
  aiger_symbol *the_justice = 0;

  FILE *file = 0;
    
  aiger = aiger_init ();

  if (input_name)
    error = aiger_open_and_read_from_file (aiger, input_name);
  else
    error = aiger_read_from_file (aiger, stdin);

  if (error)
    die ("%s: %s", input_name ? input_name : "<stdin>", error);

#if TRANSLATE
  if (reversed)
    die("Reversion not supported for translation.\n");
    
  if (!parse_liveness)
    die("Pure reachability not supported for translation.\n");
    
  if (input_name) {
    char* output_name;
    
    output_name = (char*)malloc(sizeof(char)*(strlen(input_name)+strlen(EXTENSION)+1));
    
    output_name = strcat(strcpy(output_name,input_name),EXTENSION);
    
    file = fopen (output_name, "w");
    if (!file) die ("failed to write '%s'", output_name);
  
    free (output_name); 
  } else
    die("Input file name must be specified for translattion.\n");
#endif
    
  assert(!reach_as_live || parse_liveness);
    
  // hacky:
  if (kth_property == -2) { // just print the ids and abort    
    for (i = 0; i < (parse_liveness && !reach_as_live ? aiger->num_justice : aiger->num_outputs + aiger->num_bad); i++)
      printf("%s -id=%d\n",input_name ? input_name : "", i);
    exit (0);
  }
    
  if (verbose)
     msg ("read MILOABCJF %u %u %u %u %u %u %u %u %u", 
       aiger->maxvar,
       aiger->num_inputs,
       aiger->num_latches,
       aiger->num_outputs,
       aiger->num_ands,
       aiger->num_bad,
       aiger->num_constraints,
       aiger->num_justice,
       aiger->num_fairness);
         
  if (parse_liveness && reversed)
    die ("cannot reverse liveness properties");
         
  // analyze the input and select the_output gate
  if (parse_liveness && !reach_as_live) { // for liveness          
    if (aiger->num_outputs > 0)
      wrn ("ignoring outputs");
      
    if (aiger->num_bad > 0)
      wrn ("ignoring bad state properties");
  
    if (!aiger->num_justice)
      die ("no justice property specified");
  
    if (kth_property < 0) { // pick the only one         
      if (aiger->num_justice > 1)
        die ("more than one justice property specified");
    
      the_justice = aiger->justice;
    
    } else { // pick the selected one
      if ((unsigned)kth_property >= aiger->num_justice)
        die("property index out of range");
    
      the_justice = aiger->justice + kth_property;
    }

    if (verbose)
      msg ("picking justice property of size %u",the_justice->size);
    
  } else { // for reachability  
    if (aiger->num_outputs > 0 && aiger->num_bad > 0) {
      wrn ("the problem combines both simple outputs and explicit bad state properties%s",kth_property >= 0 ? ".\n Reindexed in this order" : "");
    }
  
    if (aiger->num_outputs + aiger->num_bad == 0)
      die ("no output or bad state property specified");
         
    if (kth_property < 0) { // pick the only one
      if (aiger->num_outputs + aiger->num_bad > 1)
        die ("more than one output or bad state property specified");  
    
      if (aiger->num_outputs)    
        the_output = aiger->outputs;
      else
        the_output = aiger->bad;
    
    } else { // pick the selected one
      if ((unsigned)kth_property >= aiger->num_outputs + aiger->num_bad)
        die ("property index out of range");
    
      if ((unsigned)kth_property < aiger->num_outputs)
        the_output = aiger->outputs + kth_property;
      else
        the_output = aiger->bad + (kth_property - aiger->num_outputs);
    }    
     
    if (aiger->num_justice) 
      wrn ("ignoring justice properties");
      
    if (aiger->num_fairness) {
      if (reach_as_live)
        wrn ("reachability to liveness: will include fairness constraints (infinite trace semantics!)");
      else
        wrn ("ignoring fairness constraints (finite trace semantics!)");
    }
    
    if (aiger->num_constraints && reach_as_live)
      wrn ("reachability to liveness: will include environment constraints (infinite trace semantics!)");
  }
  
  // currently prepared clause
  vec<Lit> cur_clause;
  
  aiger_reencode (aiger);

  signature_size = aiger->maxvar+1; //one additional var for the "constant zero"       
 
  unsigned goal_reached = 0; // initialized just to get rid of compiler warning
 
  if (parse_liveness) {
    if (reach_as_live)  // one var for the "goal reached" marker
      goal_reached = aiger_var2lit(signature_size++);
       
    // each eventuality needs an additional variable: the first one for the master, the others for their respective trackers
    signature_size += (reach_as_live ? 1 : the_justice->size) + aiger->num_fairness;
  }
 
  if (!parse_liveness && the_output->lit == 0) {
    if (verbose) msg ("trivially unsat");      
#if (TRANSLATE == 0)
    universal.push(cur_clause); // the empty clause
    cur_clause.clear();
#elif (TRANSLATE == 1)
    fprintf (file, "and([or([])]).\n");
#elif (TRANSLATE == 2)
  fprintf (file, "False\n");
#elif (TRANSLATE == 3)
  fprintf (file, "false\n");  
#endif
  } else if (!parse_liveness && the_output->lit == 1) {
    if (verbose) msg ("trivially sat");     
#if (TRANSLATE == 0)
    // empty input
#elif (TRANSLATE == 1)
    fprintf (file, "and([]).\n");
#elif (TRANSLATE == 2)
    fprintf (file, "True\n");
#elif (TRANSLATE == 3)
    fprintf (file, "true\n");    
#endif    
  } else {
  
      refs = (unsigned*)calloc (2*(aiger->maxvar+1), sizeof *refs);
      
      if (parse_liveness && !reach_as_live) {
        // all the literals of the selected justice property
        for (i = 0; i < the_justice->size; i++) {
          lit = the_justice->lits[i];
          refs[lit]++;
        }
      } else {
        // the one selected output      
        lit = the_output->lit;
        refs[lit]++;
      }
      
      if (parse_liveness) {
        // all the fairness constraints
        for (i = 0; i < aiger->num_fairness; i++) {
          lit = aiger->fairness[i].lit;
          refs[lit]++;
        }
      }
                 
      // all the contraints - in any case
      for (i = 0; i < aiger->num_constraints; i++) {
        lit = aiger->constraints[i].lit;
        refs[lit]++;
      }
                 
      recheck = 1;
            
      while (recheck) 
  {
    recheck = 0;
  
    // propagate through and-gates
    i = aiger->num_ands; 
    while (i--)
    {
      lit  = aiger->ands[i].lhs;
      if (refs[lit]) 
        {
          refs[aiger->ands[i].rhs0]++;
          refs[aiger->ands[i].rhs1]++;
        }
      if (refs[aiger_not (lit)]) 
        {
          refs[aiger_not (aiger->ands[i].rhs0)]++;
          refs[aiger_not (aiger->ands[i].rhs1)]++;
        }
    }
    
    // new requests from affected latches?
    for (i = 0; i < aiger->num_latches; i++)
    {
      lit = aiger->latches[i].lit;  
      next = aiger->latches[i].next;
      if (refs[lit] && !refs[next]) {
        refs[next]++;
        recheck++;
      }
      
      if (refs[aiger_not (lit)] && !refs[aiger_not (next)]) {
        refs[aiger_not (next)]++;
        recheck++;
      } 
    }
  }

      if (!pg)
	{
	  for (lit = 2; lit <= 2*aiger->maxvar+1; lit++)
	    refs[lit] = INT_MAX;
	}

  //starting the conjuction
#if (TRANSLATE == 0)

#elif (TRANSLATE == 1)
      fprintf (file, "and([\n");  
#elif (TRANSLATE == 2)
      fprintf (file, "True");      
#elif (TRANSLATE == 3)
      fprintf (file, "solve(true");        
#endif      
      
      // the always_zero_variable
      if (refs[0] || refs[1]) {
#if (TRANSLATE == 0)
        cur_clause.push(mkLit(0,true)); // negated zero
        universal.push(cur_clause);
        cur_clause.clear();
#elif (TRANSLATE == 1)
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, 1), //writing true produces not(z0)
        fprintf (file, "])),\n");
#elif (TRANSLATE == 2)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, 1), //writing true produces not(z0)
        fprintf (file, " )");
#elif (TRANSLATE == 3)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, 1), //writing true produces not(z0)
        fprintf (file, " )");        
#endif                                                         
      }
                            
      // the and-gates
      for (i = 0; i < aiger->num_ands; i++)
	{
    lit  = aiger->ands[i].lhs;
    rhs0 = aiger->ands[i].rhs0;
    rhs1 = aiger->ands[i].rhs1;
	  if (refs[lit])
	    {               
#if (TRANSLATE == 0)      
        cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));  
        cur_clause.push(mkLit(aiger_lit2var(rhs1),aiger_sign(rhs1)));  
        universal.push(cur_clause);
        cur_clause.clear();
      
        cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));
        cur_clause.push(mkLit(aiger_lit2var(rhs0),aiger_sign(rhs0)));
        universal.push(cur_clause);
        cur_clause.clear();                         
#elif (TRANSLATE == 1)
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, aiger_not (lit)),        
        fprintf (file, ","),
        fprint_litname(file, aiger, aiger->ands[i].rhs1),
        fprintf (file, "])),\n");
      
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, aiger_not (lit)),        
        fprintf (file, ","),
        fprint_litname(file, aiger, aiger->ands[i].rhs0),
        fprintf (file, "])),\n");
#elif (TRANSLATE == 2)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger_not (lit)),        
        fprintf (file, " | "),
        fprint_litname(file, aiger, aiger->ands[i].rhs1),
        fprintf (file, " )");
      
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger_not (lit)),        
        fprintf (file, " | "),
        fprint_litname(file, aiger, aiger->ands[i].rhs0),
        fprintf (file, " )");
#elif (TRANSLATE == 3)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger_not (lit)),        
        fprintf (file, " v "),
        fprint_litname(file, aiger, aiger->ands[i].rhs1),
        fprintf (file, " )");
      
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger_not (lit)),        
        fprintf (file, " v "),
        fprint_litname(file, aiger, aiger->ands[i].rhs0),
        fprintf (file, " )");        
#endif
	    }
	  if (refs[lit+1])
	    {
#if (TRANSLATE == 0)        
        cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        cur_clause.push(mkLit(aiger_lit2var(rhs1),!aiger_sign(rhs1)));
        cur_clause.push(mkLit(aiger_lit2var(rhs0),!aiger_sign(rhs0)));
        universal.push(cur_clause);
        cur_clause.clear();
#elif (TRANSLATE == 1)
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, lit),        
        fprintf (file, ","),
        fprint_litname(file, aiger, aiger_not(aiger->ands[i].rhs1)),
        fprintf (file, ","),
        fprint_litname(file, aiger, aiger_not(aiger->ands[i].rhs0)),
        fprintf (file, "])),\n");  
#elif (TRANSLATE == 2)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, lit),        
        fprintf (file, " | "),
        fprint_litname(file, aiger, aiger_not(aiger->ands[i].rhs1)),
        fprintf (file, " | "),
        fprint_litname(file, aiger, aiger_not(aiger->ands[i].rhs0)),
        fprintf (file, " )");  
#elif (TRANSLATE == 3)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, lit),        
        fprintf (file, " v "),
        fprint_litname(file, aiger, aiger_not(aiger->ands[i].rhs1)),
        fprintf (file, " v "),
        fprint_litname(file, aiger, aiger_not(aiger->ands[i].rhs0)),
        fprintf (file, " )");         
#endif
	    }
	}
  
      // the latches
      for (i = 0; i < aiger->num_latches; i++)
  {
    lit   = aiger->latches[i].lit;
    reset = aiger->latches[i].reset;
    next  = aiger->latches[i].next;
    
    // init (reset)
    if ((reset == 0) && refs[lit])
      {
#if (TRANSLATE == 0)            
        cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));
        (reversed ? goal : initial).push(cur_clause);
        cur_clause.clear();
#elif (TRANSLATE == 1)   
        fprintf (file, "or(["),
        fprint_litname(file, aiger, aiger_not (lit)),
        fprintf (file, "]),\n");
#elif (TRANSLATE == 2)     
        fprintf (file, "& "),
        fprint_litname(file, aiger, aiger_not (lit));
#elif (TRANSLATE == 3)     
        fprintf (file, "& "),
        fprint_litname(file, aiger, aiger_not (lit));        
#endif        
      }
    else if ((reset == 1) && refs[aiger_not (lit)])
      {
#if (TRANSLATE == 0)      
        cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        (reversed ? goal : initial).push(cur_clause);
        cur_clause.clear();
#elif (TRANSLATE == 1) 
        fprintf (file, "or(["),
        fprint_litname(file, aiger, lit),
        fprintf (file, "]),\n");
#elif (TRANSLATE == 2) 
        fprintf (file, "& "),
        fprint_litname(file, aiger, lit);
#elif (TRANSLATE == 3) 
        fprintf (file, "& "),
        fprint_litname(file, aiger, lit);        
#endif
      }
    else ; // undefined = no constraint
    
    // next value
	  if (refs[lit])
	    {
#if (TRANSLATE == 0)      
        if (reversed) {
          cur_clause.push(mkLit(aiger_lit2var(next)+signature_size,aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));
        } else {
          cur_clause.push(mkLit(aiger_lit2var(next),aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit)+signature_size,!aiger_sign(lit)));
        }
        step.push(cur_clause);
        cur_clause.clear();
#elif (TRANSLATE == 1)
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, aiger->latches[i].next),
        fprintf (file, ",next("),
        fprint_litname(file, aiger, aiger_not (lit)),
        fprintf (file, ")])),\n");
#elif (TRANSLATE == 2) 
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger->latches[i].next),
        fprintf (file, " | X( "),
        fprint_litname(file, aiger, aiger_not (lit)),
        fprintf (file, " ))");       
#elif (TRANSLATE == 3) 
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger->latches[i].next),
        fprintf (file, " v X( "),
        fprint_litname(file, aiger, aiger_not (lit)),
        fprintf (file, " ))");         
#endif
      }
      
    if (refs[lit+1])
	    {
#if (TRANSLATE == 0)       
        if (reversed) {
          cur_clause.push(mkLit(aiger_lit2var(next)+signature_size,!aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        } else {
          cur_clause.push(mkLit(aiger_lit2var(next),!aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit)+signature_size,aiger_sign(lit)));
        }
        step.push(cur_clause);
        cur_clause.clear();               
#elif (TRANSLATE == 1)     
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, aiger_not(aiger->latches[i].next)),
        fprintf (file, ",next("),
        fprint_litname(file, aiger, lit),
        fprintf (file, ")])),\n");
#elif (TRANSLATE == 2)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger_not(aiger->latches[i].next)),
        fprintf (file, " | X( "),
        fprint_litname(file, aiger, lit),
        fprintf (file, " ))");
#elif (TRANSLATE == 3)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, aiger_not(aiger->latches[i].next)),
        fprintf (file, " v X( "),
        fprint_litname(file, aiger, lit),
        fprintf (file, " ))");        
#endif 
      }       
  }
      
       // the contraints -- unit clauses
      for (i = 0; i < aiger->num_constraints; i++) {
        lit = aiger->constraints[i].lit;
#if (TRANSLATE == 0)        
        cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        universal.push(cur_clause);
        cur_clause.clear();
#elif (TRANSLATE == 1)
        fprintf (file, "always(or(["),
        fprint_litname(file, aiger, lit),
        fprintf (file, "])),\n");
#elif (TRANSLATE == 2)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, lit),
        fprintf (file, " )");        
#elif (TRANSLATE == 3)
        fprintf (file, "& G( "),
        fprint_litname(file, aiger, lit),
        fprintf (file, " )");         
#endif
      }
      
      if (parse_liveness) {
        int eventuality_idx = 0;
      
        if (reach_as_live) { // the_output to multigoal trick                 
          lit = the_output->lit;  // the goal to reach once

#if (TRANSLATE == 0)              
          // initialize the tracking        
          cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
          cur_clause.push(mkLit(aiger_lit2var(goal_reached),!aiger_sign(goal_reached)));
          initial.push(cur_clause);
          cur_clause.clear();         
          
          // keep tracking if not sat
          cur_clause.push(mkLit(aiger_lit2var(goal_reached),aiger_sign(goal_reached)));
          cur_clause.push(mkLit(aiger_lit2var(lit)+signature_size,aiger_sign(lit)));
          cur_clause.push(mkLit(aiger_lit2var(goal_reached)+signature_size,!aiger_sign(goal_reached)));
          step.push(cur_clause);
          cur_clause.clear();
#elif (TRANSLATE == 1)
          // initialize the tracking
          fprintf (file, "or(["),
          fprint_litname(file, aiger, lit),
          fprintf (file, ","),
          fprint_litname(file, aiger, goal_reached+1 /* negated */),                   
          fprintf (file, "]),\n");
          
          // keep tracking if not sat
          fprintf (file, "always(or(["),
          fprint_litname(file, aiger, goal_reached),
          fprintf (file, ",next("),
          fprint_litname(file, aiger, goal_reached+1 /* negated */),
          fprintf (file, "),next("),                   
          fprint_litname(file, aiger, lit),
          fprintf (file, ")])),\n");
#elif (TRANSLATE == 2)
          // initialize the tracking
          fprintf (file, "& ("),
          fprint_litname(file, aiger, lit),          
          fprintf (file, " | X( "),
          fprint_litname(file, aiger, goal_reached+1 /* negated */),            
          fprintf (file, " ))");
          
          // keep tracking if not sat
          fprintf (file, "& G("),
          fprint_litname(file, aiger, goal_reached),
          fprintf (file, " | X( "),
          fprint_litname(file, aiger, goal_reached+1 /* negated */),
          fprintf (file, ") | X( "),
          fprint_litname(file, aiger, lit),
          fprintf (file, " ))");          
#elif (TRANSLATE == 3)
          // initialize the tracking
          fprintf (file, "& ("),
          fprint_litname(file, aiger, lit),          
          fprintf (file, " v X( "),
          fprint_litname(file, aiger, goal_reached+1 /* negated */),            
          fprintf (file, " ))");
          
          // keep tracking if not sat
          fprintf (file, "& G("),
          fprint_litname(file, aiger, goal_reached),
          fprintf (file, " v X( "),
          fprint_litname(file, aiger, goal_reached+1 /* negated */),
          fprintf (file, ") v X( "),
          fprint_litname(file, aiger, lit),
          fprintf (file, " ))");            
#endif          
          aiger_NextEventuality(goal_reached,signature_size,&eventuality_idx,&step,&universal,&goal,&cur_clause,file,aiger);
                          
        } else {
          // the justice properties       
          for (i = 0; i < the_justice->size; i++)
            aiger_NextEventuality(the_justice->lits[i],signature_size,&eventuality_idx,&step,&universal,&goal,&cur_clause,file,aiger);
        }
        
        // and the fairness
        for ( i=0; i < aiger->num_fairness; i++) {
          aiger_NextEventuality(aiger->fairness[i].lit,signature_size,&eventuality_idx,&step,&universal,&goal,&cur_clause,file,aiger);
        }
      } else {
        //the unit goal clause
        cur_clause.push(mkLit(aiger_lit2var(the_output->lit),aiger_sign(the_output->lit)));
        (reversed ? initial : goal).push(cur_clause);
        cur_clause.clear();      
      }
      
#if (TRANSLATE == 0)       

#elif (TRANSLATE == 1)     
      fprintf (file, "\n]).\n");  // close the clause list
#elif (TRANSLATE == 2)
      fprintf (file, "\n");     // newline for the last clause
#elif (TRANSLATE == 3)
      fprintf (file, ");\nquit;\n"); //close the solve call and quit
#endif
      
      free (refs);
    }
     
  aiger_reset (aiger);
  
#if TRANSLATE   
  fclose (file); 
  exit(0);
#endif     
}