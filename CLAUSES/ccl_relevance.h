/*-----------------------------------------------------------------------

File  : ccl_relevance.h

Author: Stephan Schulz (schulz@eprover.org)

Contents

  Code implementing some limited relevance analysis for function
  symbols and clauses/formulas.

  Copyright 2009 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Sun May 31 11:20:27 CEST 2009
    New

-----------------------------------------------------------------------*/

#ifndef CCL_RELEVANCE

#define CCL_RELEVANCE

#include <clb_plist.h>
#include <ccl_findex.h>
#include <ccl_proofstate.h>
//#include <tensorflow/c/c_api.h>
//#include <omp.h>

/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/

/* Data structure for computing the relevance of function symbols with
 * respect to a set of conjectures/goals */

typedef struct relevance_cell
{
   Sig_p     sig;

   PList_p   clauses_core;
   PList_p   formulas_core;

   PList_p   clauses_rest;
   PList_p   formulas_rest;

   FIndex_p  clauses_index;
   FIndex_p  formulas_index;

   long      max_level;
   PDArray_p fcode_relevance;
   PStack_p  new_codes;
   PStack_p  relevance_levels;
}RelevanceCell, *Relevance_p;



/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

#define RelevanceCellAlloc()    (RelevanceCell*)SizeMalloc(sizeof(RelevanceCell))
#define RelevanceCellFree(junk) SizeFree(junk, sizeof(RelevanceCell))


Relevance_p RelevanceAlloc(void);
void        RelevanceFree(Relevance_p junk);

void ClausePListPrint(FILE* out, PList_p list);
void FormulaPListPrint(FILE* out, PList_p list);

long        RelevanceDataInit(ProofState_p state, Relevance_p data);
Relevance_p RelevanceDataCompute(ProofState_p state);
long ProofStatePreprocess(ProofState_p state, long level);

/*  Alternating Path Relevance functions and struct
 *  These are functions for a directed graph for the purpose of 
 *  computing alternating path relevance.
 *  The literals and clauses are NOT copies, so are not free'd in 
 *  the graph cleanup methods.
 *  The entry point is APRProofStateProcess.  
 *  John Hester
*/

typedef struct aprcontrolcell
{
	long max_used_node_id;
	long max_var;
	bool equality;
	IntMap_p map;
	PStack_p buckets;
	PStack_p graph_nodes;
	PStack_p type1_nodes;
	PStack_p type2_nodes;
	PStack_p type1_equality_nodes;
	PStack_p type1_nonequality_nodes;
	ClauseSet_p equality_axioms;
	FixedDArray_p substitution_axiom_characteristic;
	Sig_p sig;
	TB_p terms;
}APRControlCell, *APRControl_p;

typedef struct aprcell
{
	long id;
	short int type;
	bool visited;
	bool equality_node;
	Eqn_p literal;
	Clause_p clause;
	PStack_p edges;
}APRCell, *APR_p;

#define APRCellAlloc() (APRCell*)SizeMalloc(sizeof(APRCell))
#define APRCellFree(junk) SizeFree(junk, sizeof(APRCell))
#define APRControlCellAlloc() (APRControlCell*)SizeMalloc(sizeof(APRControlCell))
#define APRControlCellFree(junk) SizeFree(junk, sizeof(APRControlCell))
APR_p APRAlloc(short int type, Eqn_p literal, Clause_p clause, bool equality);
void APRFree(APR_p trash);
APRControl_p APRControlAlloc(Sig_p sig, TB_p terms);
void APRControlFree(APRControl_p trash);
bool APRComplementarilyUnifiable(Eqn_p a, Eqn_p b);
PStack_p APRBuildGraphConjectures(APRControl_p control, ClauseSet_p clauses, PList_p conjectures, int distance);
int APRGraphAddClauses(APRControl_p control, ClauseSet_p clauses, bool equality);
int APRGraphAddClausesList(APRControl_p control, PList_p clauses);
bool APRGraphAddNodes(APRControl_p control, Clause_p clause, bool equality);
long APRGraphUpdateEdges(APRControl_p control);
long APRGraphUpdateEdgesDeleteOld(APRControl_p control);
long APRGraphUpdateEdgesFromListStack(APRControl_p control,
												  PTree_p *already_visited,
												  PStack_p start_nodes,
												  PStack_p relevant,
												  int distance);
long APRGraphCreateDOT(APRControl_p control);
long APRGraphCreateDOTClausesLabeled(APRControl_p control);
long APRGraphCreateDOTClauses(APRControl_p control);
Clause_p APRGetBucketClause(PStack_p bucket);
int APRBreadthFirstSearch(APRControl_p control, PStack_p nodes, PTree_p *clauses, int relevance);
PStack_p APRRelevance(APRControl_p control, ClauseSet_p set, int relevance);
PStack_p APRCollectNodesFromList(APRControl_p control, PList_p list);

PStack_p APRRelevanceList(APRControl_p control, PList_p list, int relevance);
PStack_p APRRelevanceNeighborhood(Sig_p sig, ClauseSet_p set, PList_p list, int relevance, bool equality, bool print_graph);

void APRProofStateProcess(ProofState_p proofstate, int relevance, bool equality, bool print_apr_graph);
void APRLiveProofStateProcess(ProofState_p proofstate, int relevance);
ClauseSet_p EqualityAxioms(TB_p bank, bool substitution);

int APRNodeStackAddSubstAxioms(APRControl_p control, PStack_p nodes);
int APRNodeAddSubstAxioms(APRControl_p control, APR_p node);
int EqnAddSubstAxioms(APRControl_p control, Eqn_p eqn);
int TermAddSubstAxioms(APRControl_p control, Term_p term);
Clause_p ClauseCreateSubstitutionAxiom(APRControl_p control, Sig_p sig, FunCode f_code);


#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/





