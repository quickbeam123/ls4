/*****************************************************************************************[Main.cc]
Copyright (c) 2012, Martin Suda
Max-Planck-Institut für Informatik, Saarbrücken, Germany
 
LS4 sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
LS4 are exactly the same as Minisat on which it is based on. (see below).

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"
#include "mtl/Sort.h"

#include "simp/SimpSolver.h"

#include "core/Aiger2Spec.h"
#include "core/Trp2Spec.h"

#include <set>

// #pragma GCC diagnostic warning "-Wparentheses"

using namespace Minisat;

static StringOption opt_format     ("INPUT", "format", "Input format: currently either <aiger> or <trp>. Default <trp>.", "trp");

static BoolOption opt_pg           ("AIGER", "pg","Plaisted-Greenbaum CNF encoding.", true);
static BoolOption opt_reach_as_live("AIGER", "r2l","Reduce reachability to liveness (but with inifinite trace semantics!).", false);
static IntOption  opt_kth_property ("AIGER", "id","Pick a particular property from Multi-Property input (indexing from 0).\n"
                                                 "-1 picks the only one and aborts if there is no such.\n"
                                                 "-2 just prints the ids of all available and aborts.", -1, IntRange(-2, INT32_MAX));
                                                 
static BoolOption opt_verbose    ("MAIN", "verbose", "Verbose output.", true);                                                 
static BoolOption opt_elimination("MAIN", "simp", "Perform variable elimination before actual solving.", true);

static BoolOption opt_printModel ("MAIN", "model","Print model (currently only works for trp inputs).", true);

//=================================================================================================

class MarkingSolver : public Solver {
  public:
    uint32_t model_hash;         // actually a little ugly to put it here, because it is not related to marking at all (accessed, updated an used only externally)
  
    MarkingSolver();
    ~MarkingSolver();
  
    void initilazeSignature(int number_of_basic_vars);              // the solver may allocate additional variables to serve as markers; so after this called newVar shouldn't be called anymore   
    bool addClause (const vec<Lit>& ps, const vec<int>& markers);   // Add a clause to the solver, enriched with a set of markers (markers must be registered beforehand);
    
    bool solve (const vec<Lit>& assumps);                            // implicitly enriches the supplied assumps by marker literals for the active / disabled markers respectively
    void preprocessConflict(vec<Lit>& conflict, vec<int>& markers);  // splits the derived conflict clause into the "core clause" over user supplied assumption and the marker
        
    void invalidateMarker(int id);    // all clauses with the given marker are removed from the solver 
                                      // (remove doesn't necessarily mean deleted, they can be implicitly removed by assuming the respective marker variable is true;
                                      // the solver may later decide to really delete such clauses, and to recycle the respective variable for a newly requested marker)
                                      // (can be called even on previously unregistered marker, in which case this in no-op)          
  protected:
    static const int var_Unused = -1;
    static const int var_Invalidated = -2;  

    void ensureMarkerRegistered(int id);  
    
    int base_marker_index;
    int invalidated_vars;    
    vec<Var> id2var;       // vector indexed by ids, storing either var_Undef, or the variable currently assigned to marker with the given id
    vec<int> var2id;       // vector indexed by "variables above base_marker_index",
                           // storing either the id of the marker the variable represents,
                           //   or var_Unused for an available variable,
                           //   or var_Invalidated for a variable which may still appear in some clauses inside the solver, but they should be assumed true (to keep them out of the search)      
};

const int MarkingSolver::var_Unused;
const int MarkingSolver::var_Invalidated;

MarkingSolver::MarkingSolver() : base_marker_index(0), invalidated_vars(0) {}
MarkingSolver::~MarkingSolver() {}

void MarkingSolver::initilazeSignature(int number_of_basic_vars) {
  for (int i = 0; i < number_of_basic_vars; i++ )       
    newVar();
    
  base_marker_index = nVars();
}

void MarkingSolver::ensureMarkerRegistered(int id) {
  int i;

  if (id2var.size() <= id) { // grow to needed size
    for (int i = id2var.size(); i <= id; i++)
      id2var.push(var_Undef);
  }

  if (id2var[id] != var_Undef) //already registered
    return;  

  //look for an unused variable
  for (i = 0; i < var2id.size(); i++)
    if (var2id[i] == var_Unused)
      break;
  
  if (i == var2id.size()) {
    newVar();  //allocate the variable
    var2id.push(var_Unused);
  }
  
  assert(var2id[i] == var_Unused);
  
  id2var[id] = i;
  var2id[i] = id;
}

void MarkingSolver::invalidateMarker(int id) {
  if (id >= id2var.size() || id2var[id] == var_Undef)
    return;

  assert(id2var[id] >= 0);
  assert(var2id[id2var[id]] == id);
  
  var2id[id2var[id]] = var_Invalidated;
  id2var[id] = var_Undef;
  
  if (invalidated_vars++ > base_marker_index / 2) { //just a heuristical fraction :: TODO: swich to the new minisat instead!
    // printf("Marker cleanup!\n");
    // delete all clauses mentioning an invalidated marker
    for (int i = 0; i < var2id.size(); i++) 
      if (var2id[i] == var_Invalidated) {
        assert(assigns[base_marker_index+i] == l_Undef);
        assigns[base_marker_index+i] = l_True;
      }
  
    removeSatisfied(clauses);
    removeSatisfied(learnts);    
  
    for (int i = 0; i < var2id.size(); i++) 
      if (var2id[i] == var_Invalidated) {
        assigns[base_marker_index+i] = l_Undef;
        var2id[i] = var_Unused;
      }
  
    invalidated_vars = 0;
    checkGarbage();
    rebuildOrderHeap();    
  } 
}

bool MarkingSolver::addClause(const vec<Lit>& ps, const vec<int>& markers) {
  ps.copyTo(add_tmp);
  for (int i = 0; i < markers.size(); i++) {
    ensureMarkerRegistered(markers[i]);
    
    assert(id2var[markers[i]] >= 0);
    
    add_tmp.push(mkLit(base_marker_index+id2var[markers[i]]));
  }  
  return addClause_(add_tmp);
}

bool MarkingSolver::solve(const vec<Lit>& assumps) {  
  budgetOff();
  assumps.copyTo(assumptions);
  
  for (int i = 0; i < var2id.size(); i++)  
    if (var2id[i] != var_Unused)
      assumptions.push(mkLit(base_marker_index+i,var2id[i] != var_Invalidated));

  return solve_() == l_True;
}

void MarkingSolver::preprocessConflict(vec<Lit>& out_conflict, vec<int>& out_markers) {
  out_conflict.clear();
  out_markers.clear();
  
  for (int i = 0; i < conflict.size(); i++) {
    Lit l = conflict[i];
    Var v = var(l);
    if (v < base_marker_index)
      out_conflict.push(l);
    else {
      assert(!sign(l));
      assert(var2id[v-base_marker_index] >= 0);
      out_markers.push(var2id[v-base_marker_index]);
    }         
  }
}

//=================================================================================================

typedef std::set< vec<Lit> > Layer;

struct SolvingContext {
  struct Block {
    vec< MarkingSolver* > solvers;
    vec< Layer* >  layers;
    int phase;
    int goal_clause_cnt;  // to keep track what needs to be added (because of leaps)
    
    Block() : phase(-1) {}
    
    ~Block() {
      for (int i = 0; i < solvers.size(); i++)
        delete solvers[i];
      for (int i = 0; i < layers.size(); i++)
        delete layers[i]; 
    }
  };
  
  int sigsize;
  Clauses goal_clauses;
  Clauses rest_clauses;
  
  vec<Block*> blocks;
  int solver_called;
  int learned_clauses;
  int leaped_clauses;
  
  bool discoveredModel;
  int model_block, model_layer;    // block index and layer index when repetition found
  int model_block2, model_layer2;  // the earlier place with the same model
  
  SolvingContext() : solver_called(0), learned_clauses(0), leaped_clauses(0), discoveredModel(false) /*, lastDrawingSize(0)*/  {}
  
  ~SolvingContext() {
    for (int i = 0; i < blocks.size(); i++)
      delete blocks[i];
    if (opt_verbose)
      printf("Solver called %d times (learned %d clauses). %d clauses leaped.\n",solver_called,learned_clauses,leaped_clauses);
  }

  void extendTheLastBlock(Block& block, int idx) {
    assert(idx == blocks.size()-1);
    assert(&block == blocks[idx]);
  
    vec<int> marker;
  
    block.solvers.push(new MarkingSolver()); // adding one new solver  
    MarkingSolver &solver = *block.solvers.last();
  
    solver.initilazeSignature(2*sigsize+1);      // sigsize for lower, sigsize for upper, and one for the initial marker (goal markers are done inside)
                      
    for (int i = 0; i < rest_clauses.size(); i++)
      solver.addClause(rest_clauses[i],marker /*empty*/);
  
    block.phase++; //now phase serves as an index to the layer we are about to introduce next
    marker.push(idx);
  
    if (block.layers.size() < block.solvers.size())  //the layers can sometimes be already larger, in that case we don't extend
      block.layers.push(new Layer());
    else {    
      //printf("Layers already present -- reinserting learned stuff!\n");
            
      {  // to current  -- this is even necessary for corretness (in the presence of goal clauses over \Sigma \cup \Sigma' arising from variable elimination)
        Layer& cur_layer = *block.layers[block.phase];
      
        for (Layer::iterator it = cur_layer.begin(); it != cur_layer.end(); it++)
          solver.addClause(*it,marker);
      }
      
      // to all previous if possible -- otherwise we would learn them again, probably
      int solver_idx = 0;
      int block_idx = idx - 1;
      for (int i = block.phase+1; i < block.layers.size(); i++) {
        Layer& cur_layer = *block.layers[i];
        
        assert(block_idx >= 0);
        assert(blocks[block_idx]->solvers.size()>solver_idx);
        
        MarkingSolver &cur_solver = *blocks[block_idx]->solvers[solver_idx];
        
        solver_idx++;
        if (solver_idx == blocks[block_idx]->solvers.size()) {
          solver_idx = 0;
          block_idx--;
        }
        
        for (Layer::iterator it = cur_layer.begin(); it != cur_layer.end(); it++)
          cur_solver.addClause(*it,marker);      
      }
    }
  }
  
  Block& prepareNewBlock() {     
    int idx = blocks.size();
    blocks.push(new Block());
    Block& block = *blocks.last();

    extendTheLastBlock(block,idx);                   //will add the non-goal clauses    
    MarkingSolver &solver = *block.solvers.last();   //last is the first here

    vec<int> markers;
    markers.push(idx);
    
    //we add the goal clauses here
    for (int i = 0; i < goal_clauses.size(); i++)        
      solver.addClause(goal_clauses[i],markers);        
    
    block.goal_clause_cnt = goal_clauses.size();         
    return block;
  }
  
  int distanceToGoal(int block_idx, int layer_idx, int goal_block_idx) {
    assert(block_idx <= goal_block_idx);
    int dist = layer_idx;
    for (int i = block_idx+1; i <= goal_block_idx; i++)
      dist += blocks[i]->phase+1;
    return dist;
  }
  
  void invalidateMarkersInLowBlocks(int last_block_idx) {
    //printf("invalidateMarkersInLowBlocks(last_block_idx=%d)\n",last_block_idx);
    assert(last_block_idx == blocks.size()-1);
    for (int i = 0; i < last_block_idx; i++) {
      Block &block = *blocks[i];
      for (int j = 0; j < block.solvers.size(); j++)
        block.solvers[j]->invalidateMarker(last_block_idx);
    }
  }
  
  void enrichByNewLeaps(int block_idx, SolvingContext::Block &cur_block, int layer_idx, MarkingSolver &cur_solver) {
    if (layer_idx > 0)
      return;
        
    markers_tmp.clear();
    markers_tmp.push(block_idx);
    for (int i = cur_block.goal_clause_cnt; i < goal_clauses.size(); i++)
      cur_solver.addClause(goal_clauses[i],markers_tmp);

    cur_block.goal_clause_cnt = goal_clauses.size();  
  }
  
  //int lastDrawingSize;
  
  void drawMA(int block_idx, int layer_idx) {    
  /*
    int drawn = 0;
    printf("\r");
    for (int i = 0; i < block_idx; i++)
      for (int j = blocks[i].phase-1; j >= 0; j++)
        if (j == 0)
          drawn++, printf("G");
        else
          drawn++, printf("*");
    
    for (int j = blocks[block_idx].phase-1; j >= layer_idx; j++)
        if (j == 0)
          drawn++, printf("G");
        else
          drawn++, printf("*");

    for (int i = drawn; i < lastDrawingSize; i++)
      printf(" ");
    lastDrawingSize = drawn;
  */
    //printf("\r");
    for (int i = 0; i < block_idx; i++)
      printf("b[%d]",blocks[i]->phase);
    printf("b[%d/%d]",layer_idx,blocks[block_idx]->phase);      
    for (int i = block_idx+1; i < blocks.size(); i++)
      printf("b[%d]",blocks[i]->phase);
    printf("\n");
  }
  
  vec<Lit> conflict_tmp;
  vec<int> markers_tmp;
  
  void iterativeSearch();
  int decideUnderMA(int block_idx, int layer_idx, vec<Lit> &our_ma, MarkingSolver *prev_solver);   
      
  void printModel(int low_block_idx, int low_layer_idx, int high_block_idx, int high_layer_idx) {
  
    if (low_block_idx >= 0)
      printf("low_block_idx=%d, low_layer_idx=%d, high_block_idx=%d, high_layer_idx=%d\n",low_block_idx,low_layer_idx,high_block_idx,high_layer_idx);
  
    for (int i = 0; i <= high_block_idx; i++) {
      for (int j = 0; j < blocks[i]->phase; j++)
        printf("*");
      printf("G");
    }
    printf("\n");
    
    if (low_block_idx >= 0)
      for (int i = 0; i <= high_block_idx; i++) {
        for (int j = blocks[i]->phase; j >= 0; j--)
          if ((i == low_block_idx && j == low_layer_idx) || (i == high_block_idx && j == high_layer_idx))
            printf("*");
          else
            printf(" ");                      
      }
    printf("\n");          
  }
  
};

void printClause(const vec<Lit> &clause, const vec<int> &markers) {
  for (int i = 0; i < clause.size(); i++)      
    printf("%s%d ",sign(clause[i])?"-":"",var(clause[i]));
  
  printf(" || ");
  
  for (int i = 0; i < markers.size(); i++)      
    printf("%d ",markers[i]);
      
  printf("\n");
}

void printLayer(const Layer& layer) {
  vec<int> marker;
  for (Layer::const_iterator it = layer.begin(); it != layer.end(); ++it) {
    printClause(*it,marker);
  }
}

void printIStars(int i) {
  for (int j = 0; j < i; j++)
    printf("*");
  printf("\n");
}

/*
void callingSolver(int i, vec<Lit>& ma, MarkingSolver& solver) {
  printf("Calling solver %d\n",i);
  printf("Under ma: "); printClause(ma);
  printf("Clauses inside are: \n");
  
  Clauses clauses;
  solver.copyOutClauses(clauses);
  for (int i = 0; i < clauses.size(); i++) {
    printClause(clauses[i]);
  }
}
*/
int SolvingContext::decideUnderMA(int block_idx, int layer_idx, vec<Lit> &our_ma, MarkingSolver *prev_solver)
/*
  returns 0 for conflict 
  returns 1 for solved
  returns 2 for leaping
*/
{  
  SolvingContext::Block &cur_block = *blocks[block_idx];    
  MarkingSolver &cur_solver = *cur_block.solvers[layer_idx];
      
  vec<Lit> ma;
               
  // printf("decideUnderMA(block_idx=%d[%d],layer_idx=%d[%d])\n",block_idx,blocks.size(),layer_idx,cur_block.phase+1);
               
  while (/*callingSolver(i,our_ma,solver),*/
         /*drawMA(block_idx,layer_idx),*/
         enrichByNewLeaps(block_idx,cur_block,layer_idx,cur_solver),
         solver_called++,cur_solver.simplify(),cur_solver.solve(our_ma)) {
    //printf("solver[%d].nLearnts = %d, solver[%d].nClauses = %d\n",i,solver.nLearnts(),i,solver.nClauses());
   
    // build the new model assumption and at the same time prepare for the test of model repetiton
    uint32_t hash = 0;
    ma.clear();
    for (int j = 0; j < sigsize; j++) {
      assert(cur_solver.model[j+sigsize] != l_Undef); //we have done compression, so there should be no "holes"
      
      // TODO: use the information about bridge here
      
      ma.push(mkLit(j,cur_solver.model[j+sigsize] == l_False));
      
      //printf("m[%d]=%d",j,cur_solver.model[j+sigsize] == l_False);
                 
      if (cur_solver.model[j+sigsize] == l_True)
        hash ^= 1 << (j & 31);
    }        
    //printf("\n");
    cur_solver.model_hash = hash; // save the hash    
    ma.push(mkLit(2*sigsize, false)); // L_initial assumed true => turning on step clauses, turning off initial clauses 

    // model repetition check
    for (int i = 0; i < block_idx; i++) {  //all the models of lower blocks are eligible
      SolvingContext::Block &other_block = *blocks[i];
      
      //printf("i=%d\n",i);
      
      for (int j = 0; j < other_block.solvers.size(); j++) {
        MarkingSolver &otherSolver = *other_block.solvers[j];
      
        //printf("j=%d\n",j);
      
        if (otherSolver.model_hash != hash)
          continue; 
          
        //have a closer look
        for (int k = 0; k < sigsize; k++)
          if (cur_solver.model[k+sigsize] != otherSolver.model[k+sigsize])
            goto nextSolver;
      
        discoveredModel = true;
        model_block2 = i;
        model_layer2 = j;
        model_block = block_idx;
        model_layer = layer_idx;
        
        printf("SAT: model found\n");
        /*
        if (opt_verbose) {
          printModel(i,j,block_idx,layer_idx);  // TODO: model for cuhanoi7.aig looks suspicious - investigate
        }
        */
        return 1;
        
        nextSolver: ;
      }
    }
    
    int new_layer_idx;
    int new_block_idx;
    
    if (layer_idx == 0) {
      new_block_idx = block_idx + 1;
      if (new_block_idx == blocks.size()) {
        // printf("Other block sat - extending!\n");
        prepareNewBlock();
      }
      new_layer_idx = blocks[new_block_idx]->phase;
    } else {
      new_block_idx = block_idx;
      new_layer_idx = layer_idx - 1;
    }
        
    int subcall = decideUnderMA(new_block_idx,new_layer_idx,ma,&cur_solver);
    
    if (subcall == 1) // true means the problem is solved (we just get out of the recursion)
      return 1;
    
    if (subcall == 2 && block_idx >= blocks.size())  // jumping away after Leap
      return 2;    
  }

  cur_solver.preprocessConflict(conflict_tmp,markers_tmp);
  
  //printf("Derived conflict clause: "); printClause(conflict_tmp,markers_tmp);
  
  if (conflict_tmp.size() == 0 || (conflict_tmp.size() == 1 && conflict_tmp[0] == mkLit(2*sigsize))) {  //the empty clause case     
    if (conflict_tmp.size() == 0 && markers_tmp.size() == 0) {
      printf("UNSAT: unconditional empty clause derived, in fact a (*,*)-clause.\n");        
      return 1;
    } 
    
    if (conflict_tmp.size() == 0 && markers_tmp.size() == 1) {
      printf("UNSAT: unconditional empty clause derived, in fact a (*,%d)-clause for block %d.\n",distanceToGoal(block_idx,layer_idx,markers_tmp[0]),markers_tmp[0]); 
      return 1;      
    }
    
    if (conflict_tmp.size() == 1 && markers_tmp.size() == 0) {
      printf("UNSAT: unconditional empty clause derived, in fact a (0,*)-clause.\n");        
      return 1;
    }
    
    assert(blocks.size()-1 > 0 || (markers_tmp.size() == 1 && markers_tmp[0] == 0)); // if we are in block 0 then it's the old (reachability) style extension
    
    int last_involved_idx = max(markers_tmp,-1);                                    
      
    // doesn't need to be the last block in the presence of environment constraints
    while (last_involved_idx != blocks.size()-1) {
      // printf("Removing an extra block!\n");
      invalidateMarkersInLowBlocks(blocks.size()-1);
      delete blocks.last();
      blocks.pop();   
    }    
    
    // printf("Empty clause!%s",last_involved_idx > 0 ? " - could have learned a no-good: " : ": "); printClause(conflict_tmp,markers_tmp);
    
    // printModel(-1,-1,blocks.size()-1,-1);
    
    invalidateMarkersInLowBlocks(last_involved_idx);
    extendTheLastBlock(*blocks[last_involved_idx],last_involved_idx);

    // printModel(-1,-1,blocks.size()-1,-1);    
    
    // TODO: could potentially learn a nogood combo of distances (BUT: the proof would need to be saved as well???)   
         
  } else { // the regular non-empty clause case
    assert(block_idx > 0 || layer_idx < blocks[block_idx]->phase);
           
    // convert it to the upper signature and possibly remove the step marker
    int i,j;
    for (i = 0, j = 0; i < conflict_tmp.size(); i++) {
      if (var(conflict_tmp[i]) == 2*sigsize) {
        assert(sign(conflict_tmp[i]));        
        // the step clause marker doesn't go into learned clauses
      } else {
        assert(var(conflict_tmp[i])<sigsize);
        conflict_tmp[j++] = mkLit(var(conflict_tmp[i])+sigsize,sign(conflict_tmp[i]));
      }
    }
    conflict_tmp.shrink(i-j);                  
           
    if (markers_tmp.size() == 0) { // universal clause
    
      //printf("Learning a universal clause: "); printClause(conflict_tmp,markers_tmp);
    
      // TODO: we don't have the span restriction here, so alternatively, we could go around and put this everywhere
      rest_clauses.push(conflict_tmp);
    } else if (markers_tmp.size() == 1) { // learning     
      int target_block_idx = markers_tmp[0];
      int target_layer_idx = 1+distanceToGoal(block_idx,layer_idx,target_block_idx);    
    
      //printf("Learning(block_idx=%d,layer_idx=%d)\n",block_idx,layer_idx);    
      //printf("Learning(target_block_idx=%d,target_layer_idx=%d)\n",target_block_idx,target_layer_idx);    

      Block &target_block = *blocks[target_block_idx];
      
      if (target_layer_idx >= target_block.layers.size()) {
        //printf("Overextending layers!\n");
        target_block.layers.push(new Layer());
      }
      
      assert(target_layer_idx < target_block.layers.size()); //one addition is enough!      
      Layer &target_layer = *target_block.layers[target_layer_idx];
            
      sort(conflict_tmp);
      target_layer.insert(conflict_tmp);
      
      if (target_block_idx == blocks.size()-1) {       // the layer is in the last block (TODO: we could potentially also detect non-last block Leaps!!!)        
        //printf("Layer repetition check(block=%d)\n",block_idx);
        //printf("target_layer(target_layer_idx=%d)\n",target_layer_idx); printLayer(target_layer);        
        
        for (int i = 1 /*zeroth is always empty*/; i <= target_block.phase; i++) {
          //printf("other layer(%d)\n",i); printLayer(*target_block.layers[i]);
          if ((i != target_layer_idx) && (*target_block.layers[i] == target_layer)) { // not the same index, but the same content        
            if (target_block_idx == 0) {
              printf("UNSAT: repetition detected!\n");
              if (opt_verbose)
                printf("Layer %d equal to current layer %d!\n",i,target_layer_idx);
              return 1;
            }
          
            // LEAPing!!!
            //printf("Leap!\n");
            int larger;
            int diff;
            int leap_idx;
     
            if (target_layer_idx > i) {
              larger = target_layer_idx;
              diff = target_layer_idx - i;
            } else {
              larger = i;
              diff = i - target_layer_idx;
            }
                         
            leap_idx = larger - larger % diff;            
            Layer &source_layer = *target_block.layers[leap_idx];

            for (Layer::iterator it = source_layer.begin(); it != source_layer.end(); it++) {                  
              leaped_clauses++;
              goal_clauses.push(*it);
            }

            invalidateMarkersInLowBlocks(target_block_idx);
            
            // CAREFULL -- we are about to delete objects to which there are still references on the stack !!!
            assert(target_block_idx == blocks.size()-1);
            delete blocks.last();
            blocks.pop();
            
            // if that is really the case - we need to bubble up silently
            if (block_idx >= blocks.size())
              return 2;
            else 
              return 0; // don't learn the guy the normal way in any case, the marker is dead!
          }
        }      
      }           
    }
      
    // put it into the previous solver    
    assert(prev_solver != NULL);
    learned_clauses++;
    //printf("Learning clause from(block_idx=%d[%d],layer_idx=%d[%d]) ",block_idx,blocks.size(),layer_idx,cur_block.phase+1); printClause(conflict_tmp,markers_tmp);    
    prev_solver->addClause(conflict_tmp,markers_tmp);    
  }
     
  return 0; 
}

void SolvingContext::iterativeSearch()
{
  SolvingContext::Block &zero_block = prepareNewBlock(); // also inserts the right clauses     
    
  vec<Lit> ma;
  ma.push(mkLit(2*sigsize,  true)); // not (L_initial)  
     
  while (/*printf("Phase\n"),*/!decideUnderMA(0,zero_block.phase,ma,NULL));
}

void insertClause(SimpSolver &solver, vec<Lit> &clause, int sigsize, bool shifted, Lit litToAdd = lit_Undef) {
  vec<Lit> prepared;
  int shift = shifted ? sigsize : 0;
  
  for (int j=0; j < clause.size(); j++) {
    Lit l = clause[j];  
    prepared.push(mkLit(var(l)+shift,sign(l)));
  }
  
  if (litToAdd != lit_Undef)
    prepared.push(litToAdd);
      
  solver.addClause(prepared); // printClause(prepared);  
}

inline void printLits(const vec<Lit> &lits) {
  for (int i = 0; i < lits.size(); i++)
    printf("%s%d ",sign(lits[i])?"-":"",var(lits[i]));
  printf("\n");
}

static void printState(vec<bool>& cur_model, Names& varNames, int idx, bool isGoal) {
  printf("State %d",idx);
  if (isGoal) {
    printf(" (goal) ");
  }
  printf(": [");
  for (int n = 0; (n < cur_model.size()) && (n < (int)varNames.size()); n++) {
    if (n > 0)
      printf(", ");
    if (cur_model[n]) {
      printf("%s",varNames[n].c_str());
    } else {
      printf("not(%s)",varNames[n].c_str());
    }
  }
  printf("]\n");
}

static void verifyStep(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step, vec<bool>& cur_model, vec<bool>& prev_model, bool isInitial, bool isGoal) {
  if (isInitial) { // check initial
    for (int i = 0; i < initial.size(); i++) {
      for (int j = 0; j < initial[i].size(); j++)
        if (cur_model[var(initial[i][j])] != sign(initial[i][j]))
          goto next_initial_clause;
      
      printf("Initial clause UNSAT: "); printLits(initial[i]);
      assert(false);
      
      next_initial_clause: ;
    }
  }

  if (isGoal) { // check goal
    for (int i = 0; i < goal.size(); i++) {
      for (int j = 0; j < goal[i].size(); j++)
        if (cur_model[var(goal[i][j])] != sign(goal[i][j]))
          goto next_goal_clause;
      
      printf("Goal clause UNSAT: "); printLits(goal[i]);
      assert(false);
      
      next_goal_clause: ;
    }
  }
  
  // check universal
  {
    for (int i = 0; i < universal.size(); i++) {
      for (int j = 0; j < universal[i].size(); j++)
        if (cur_model[var(universal[i][j])] != sign(universal[i][j]))
          goto next_universal_clause;
      
      printf("Universal clause UNSAT: "); printLits(universal[i]);
      assert(false);
      
      next_universal_clause: ;
    }
  }
  
  // check step
  if (!isInitial) {
    for (int i = 0; i < step.size(); i++) {
      for (int j = 0; j < step[i].size(); j++)
        if (var(step[i][j]) < sigsize) {
          if (prev_model[var(step[i][j])] != sign(step[i][j]))
            goto next_step_clause;
        } else {
          if (cur_model[var(step[i][j])-sigsize] != sign(step[i][j]))
            goto next_step_clause;
        }
      
      printf("Step clause UNSAT: "); printLits(step[i]);
      assert(false);
      
      next_step_clause: ;
    }
  }
}

void analyzeSpec(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step, Names& varNames) {
  SolvingContext context;
    
  // preprocessing
  int new_sigsize;
  SimpSolver simpSolver;
    
  //TODO: play with these guys -- and possibly also with other params of minisat ...
  
  //simpSolver.use_asymm = true;
  //simpSolver.grow = 10;
  
  // 0,1,...,sigsize-1           the basic signature
  // sigsize,...,2*sigsize-1     the primed signature
  // 2*sigsize                   the initial marker
  // 2*sigsize+1                 the goal marker
  for (int j = 0; j < 2*sigsize+2; j++)
    simpSolver.newVar();

  // initial clauses
  for (int j = 0; j < initial.size(); j++) {
    //vec<int> empty; printf("Initial clause: "); printClause(initial[j],empty);
    insertClause(simpSolver,initial[j],sigsize,true,mkLit(2*sigsize));  // marked as initial
  }
  
  // goal clauses
  for (int j = 0; j < goal.size(); j++) {
    //vec<int> empty; printf("Goal clause: "); printClause(goal[j],empty);
    insertClause(simpSolver,goal[j],sigsize,true,mkLit(2*sigsize+1));   // marked as goal
  }
  
  // universal clauses
  for (int j = 0; j < universal.size(); j++) {
    //vec<int> empty; printf("Universal clause: "); printClause(universal[j],empty);
    insertClause(simpSolver,universal[j],sigsize,true);  //universals are unmarked
  }
  
  // step clauses
  for (int j = 0; j < step.size(); j++) {
    //vec<int> empty; printf("Step clause: "); printClause(step[j],empty);
    insertClause(simpSolver,step[j],0,false,mkLit(2*sigsize,true));  // marked as incompatible with initial
  }
  
  // freeze the markers, and all variables from lower signature
  simpSolver.setFrozen(2*sigsize,true);
  simpSolver.setFrozen(2*sigsize+1,true);
  for (int i = 0; i < sigsize; i++) // don't eliminate lower signature variables (it is trivial, and it spoils the statistics)
    simpSolver.setFrozen(i,true);
  for (int j = 0; j < step.size(); j++)
    for (int i = 0; i < step[j].size(); i++)
      if (var(step[j][i])<sigsize) {
        simpSolver.setFrozen(var(step[j][i]),true); // here we do it again, but who cares
        simpSolver.setFrozen(var(step[j][i])+sigsize,true); //and this is the important part
      }
  
  int before = simpSolver.nClauses();    // in fact, we don't see the number of unit clauses here !!!
  
  if (opt_elimination ? !simpSolver.eliminate(true) : !simpSolver.simplify()) {
    printf("UNSAT: solved by variable elimantion!\n");
    return;
  }
  
  Clauses simpClauses;
  simpSolver.copyOutClauses(simpClauses);
  
  vec<Var> renaming;
  vec<Var> inv_renaming;
  
  for (int i = sigsize; i < 2*sigsize+2; i++) { // the two markers didn't get eliminated!
    renaming.push();
    
    if (!simpSolver.isEliminated(i)) {
      renaming.last() = inv_renaming.size();
      inv_renaming.push(i-sigsize);
    } else {
      renaming.last() = var_Undef;
    }
  }
  
  new_sigsize = inv_renaming.size() - 2; //the two markers don't count
  context.sigsize = new_sigsize;
  
  if (opt_verbose) {
    printf("Eliminated %d variables -- new sigsize: %d.\n",simpSolver.eliminated_vars,new_sigsize);
    printf("Simplified from %d to %d clauses.\n",before,simpSolver.nClauses());
  }
  
  for (int i = 0; i < simpClauses.size(); i++ ) {
    vec<Lit>& clause = simpClauses[i];

    int j,k;
    bool goal = false;
    
    for (j = 0, k = 0; j < clause.size(); j++) {
      Lit l = clause[j];
      Var v = var(l);

      if (v == 2*sigsize+1) { // we remeber it, but newly don't keep explicitly anymore (will later use MarkingSolver instead)
        assert(!sign(l));
        goal = true;
      } else {
        clause[k++] = l;
      }
    }
    clause.shrink(j-k);  //one literal potentially missing

    // apply the renaming
    for (int j = 0; j < clause.size(); j++) {
      Lit l = clause[j];
      Var v = var(l);

      if (v < sigsize)
        clause[j] = mkLit(renaming[v],sign(l));
      else {
        clause[j] = mkLit(renaming[v-sigsize]+new_sigsize,sign(l));
      }
    }
    
    //vec<int> empty; printf("%s clause: ",goal ? "Goal" : "Normal"); printClause(clause,empty);
    
    Clauses& target = (goal ? context.goal_clauses : context.rest_clauses);

    int idx = target.size();
    target.push();
    clause.moveTo(target[idx]);
  }
  
  context.iterativeSearch();
  
  if (context.discoveredModel && opt_printModel) {
    
    vec<bool> prev_model;
    vec<bool> cur_model;
    vec<bool> rep_model; int rep_idx = -1;
    vec<bool> rep_succ; bool rep_succ_goal = false;
    
    int len = 0;
    int len2 = 0;
    for (int i = 0; i <= context.model_block; i++) {
      int toAdd = context.blocks[i]->phase+1;
      len += toAdd;
      if (i <= context.model_block2)
        len2 += toAdd;
    }
    len -= context.model_layer;
    len2 -= context.model_layer2;
    
    // printf("A laso-model of shape %d-%d.\n",len,len2); // wouldn't work in general (see the rep_succ trick)
    int idx = 0;
    
    // we do model reconstruction, model checking and model printing at the same time
    for (int i = 0; i <= context.model_block; i++) {
      SolvingContext::Block& cur_block = *context.blocks[i];
    
      for (int j = cur_block.phase; j >= 0; j--) {
        MarkingSolver& cur_solver = *cur_block.solvers[j];
        
        //clear the model in simpSolver
        simpSolver.model.clear();
        simpSolver.model.growTo(simpSolver.nVars());
        for (int n = 0; n < simpSolver.nVars(); n++)
          simpSolver.model[n] = l_Undef;
      
        if (prev_model.size()) {
          assert(prev_model.size() == sigsize);
          for (int n = 0; n < sigsize; n++) {
            simpSolver.model[n] = lbool(prev_model[n]);
          }

          // non-initial marker
          simpSolver.model[2*sigsize] = l_True;
        } else { // the initial marker
          simpSolver.model[2*sigsize] = l_False;
        }
      
        // the goal marker
        simpSolver.model[2*sigsize+1] = (j==0) ? l_False : l_True;
      
        // and the actual new stuff
        for (int n = 0; n < new_sigsize; n++) {
          simpSolver.model[sigsize + inv_renaming[n]] = cur_solver.model[new_sigsize+n];
        }
        
        simpSolver.extendModel();
      
        cur_model.clear();
        for (int n = sigsize; n < 2*sigsize; n++) {
          assert(simpSolver.model[n] != l_Undef);
          
          cur_model.push(simpSolver.model[n]==l_True);
        }
        
        printState(cur_model,varNames,idx,j==0);
        
        verifyStep(sigsize,initial,goal,universal,step,cur_model,prev_model,!prev_model.size(),j==0);
        cur_model.copyTo(prev_model);
        
        if (i == context.model_block2 && j == context.model_layer2) {
          cur_model.copyTo(rep_model);
          rep_idx = idx;
        }
        
        if (idx == rep_idx+1) {
          cur_model.copyTo(rep_succ);
          rep_succ_goal = (j==0);
        }
        
        if (i == context.model_block && j == context.model_layer) {
          if (cur_model != rep_model) {
            // printf("rep_succ trick\n");
            // formally, let's take one more step
            verifyStep(sigsize,initial,goal,universal,step,rep_succ,cur_model,false,rep_succ_goal);
            printState(rep_succ,varNames,idx+1,rep_succ_goal);
            rep_idx++;
          }
          printf("Same as state %d\n",rep_idx);
          goto done;
        }
        
        idx++;
      }
    }
    done: ;
  }
}

//=================================================================================================

int main(int argc, char** argv)
{
    try {
    try {
      setUsageHelp("USAGE: %s [options] <input-file>\n\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        // printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif

    // THE SPEC:
    int sigsize = 0; 
    Clauses initial;
    Clauses goal;
    Clauses universal;
    Clauses step;
    
    // translation variables will not be given names, so that we don't report on them (``project away'' semantics is the right one)
    // (this way, we will also not crash if the input comes from AIGER (where everything will be projected away)
    Names varNames;
       
    parseOptions(argc, argv, true);

    if (strcmp(opt_format,"aiger") == 0)
      aiger_LoadSpec((argc == 1) ? 0 : argv[1], (int)0, (int)opt_pg, (int)opt_verbose, opt_kth_property, (int)true, (int)opt_reach_as_live,
                   sigsize,initial,goal,universal,step);
    else if (strcmp(opt_format,"trp") == 0)
      trp_LoadSpec((argc == 1) ? 0 : argv[1],sigsize,initial,goal,universal,step,varNames);
    else {
      printf("Unknown format: %s!\n",(const char *)opt_format);
      exit (1);
    }
    
    if (opt_verbose)
      printf("Loaded spec -- sigsize: %d, #initial: %d, #goal: %d, #universal: %d, #step: %d\n",sigsize,initial.size(),goal.size(),universal.size(),step.size());

    analyzeSpec(sigsize,initial,goal,universal,step,varNames);

    } catch (OutOfMemoryException&){ //bad_alloc
        printf("===============================================================================\n");
        printf("OutOfMemory!\n");
        exit(0);
    };
    } catch (std::bad_alloc&){
       printf("===============================================================================\n");
       printf("bad_alloc!\n");
       exit(0);
    }
}
