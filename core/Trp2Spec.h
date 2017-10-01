/********************************************************************************************
Copyright (c) 2012, Martin Suda
Max-Planck-Institut für Informatik, Saarbrücken, Germany
 
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

#ifndef Trp_2_Spec_h
#define Trp_2_Spec_h

#include "mtl/Vec.h"
#include "core/SolverTypes.h"

#include <string>
#include <vector>

typedef Minisat::vec< Minisat::vec<Minisat::Lit> > Clauses;

typedef std::vector<std::string> Names;

void trp_LoadSpec( /* input:*/ 
                   const char* input_name, // can be 0 for parsing stdin                   
                   /*output:*/ 
                   int &signature_size, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step,
                   Names& varNames); // translation variables will not be given names, so that we don't report on them (``project away'' semantics is the right one)

#endif
