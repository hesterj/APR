/*-----------------------------------------------------------------------

File  : ccl_relevance.c

Author: Stephan Schulz (schulz@eprover.org)

Contents

  Approximate relevance determination and filtering.

  Copyright 2009 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

Changes

<1> Wed Jun  3 00:07:17 CEST 2009
    New

-----------------------------------------------------------------------*/

#include "ccl_relevance.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/


/*-----------------------------------------------------------------------
//
// Function: find_level_fcodes()
//
//   Find all (non-special) function symbols in the relevance cores
//   and assign their relevance level. Push them onto the new_codes
//   stack (once).
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void find_level_fcodes(Relevance_p reldata, long level)
{
   PList_p handle;
   PStack_p collector = PStackAlloc();
   Clause_p clause;
   WFormula_p form;
   FunCode   f;

   for(handle = reldata->clauses_core->succ;
       handle != reldata->clauses_core;
       handle = handle->succ)
   {
      clause = handle->key.p_val;
      ClauseReturnFCodes(clause, collector);
      while(!PStackEmpty(collector))
      {
         f = PStackPopInt(collector);
         if(!SigIsSpecial(reldata->sig, f))
         {
            if(!PDArrayElementInt(reldata->fcode_relevance, f))
            {
               PDArrayAssignInt(reldata->fcode_relevance, f, level);
               PStackPushInt(reldata->new_codes, f);
            }
         }
      }
   }

   for(handle = reldata->formulas_core->succ;
       handle != reldata->formulas_core;
       handle = handle->succ)
   {
      form = handle->key.p_val;
      WFormulaReturnFCodes(form, collector);
      while(!PStackEmpty(collector))
      {
         f = PStackPopInt(collector);
         if(!SigIsSpecial(reldata->sig, f))
         {
            if(!PDArrayElementInt(reldata->fcode_relevance, f))
            {
               PDArrayAssignInt(reldata->fcode_relevance, f, level);
               PStackPushInt(reldata->new_codes, f);
            }
         }
      }
   }
   PStackFree(collector);
}


/*-----------------------------------------------------------------------
//
// Function: extract_new_core()
//
//   Find the formulas and clauses in the the "rest" part and put them
//   into the core.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void extract_new_core(Relevance_p reldata)
{
   FunCode f;
   PTree_p root;
   PList_p entry;

   while(!PStackEmpty(reldata->new_codes))
   {
      f = PStackPopInt(reldata->new_codes);

      while((root = PDArrayElementP(reldata->clauses_index->index, f)))
      {
         entry = root->key;
         FIndexRemovePLClause(reldata->clauses_index, entry);
         PListExtract(entry);
         PListInsert(reldata->clauses_core, entry);
      }
      while((root = PDArrayElementP(reldata->formulas_index->index, f)))
      {
         entry = root->key;
         FIndexRemovePLFormula(reldata->formulas_index, entry);
         PListExtract(entry);
         PListInsert(reldata->formulas_core, entry);
      }
   }
}



/*-----------------------------------------------------------------------
//
// Function: move_clauses()
//
//   Given a plist of clauses, move them into the clauseset.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

static void move_clauses(PList_p from, ClauseSet_p to)
{
   PList_p handle;
   Clause_p clause;

   for(handle = from->succ;
       handle != from;
       handle = handle->succ)
   {
      clause = handle->key.p_val;
      ClauseSetExtractEntry(clause);
      ClauseSetInsert(to, clause);
   }
}

/*-----------------------------------------------------------------------
//
// Function: move_formulas()
//
//   Given a plist of formulas, move them into the formulaset.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

static void move_formulas(PList_p from, FormulaSet_p to)
{
   PList_p handle;
   WFormula_p form;

   for(handle = from->succ;
       handle != from;
       handle = handle->succ)
   {
      form = handle->key.p_val;
      FormulaSetExtractEntry(form);
      FormulaSetInsert(to, form);
   }
}


/*-----------------------------------------------------------------------
//
// Function: proofstate_rel_prune()
//
//   Use the relevance data to prune axioms to those with a relevancy <=
//   level.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

static void proofstate_rel_prune(ProofState_p state,
                                  Relevance_p reldata,
                                  long level)
{
   ClauseSet_p  new_ax  = ClauseSetAlloc();
   FormulaSet_p new_fax = FormulaSetAlloc();
   PStackPointer i, base;
   PList_p       set;

   GCDeregisterFormulaSet(state->gc_terms, state->f_axioms);
   GCDeregisterClauseSet(state->gc_terms, state->axioms);

   for(i=0; i<level; i++)
   {
      base = 2*i;
      if(base >= PStackGetSP(reldata->relevance_levels))
      {
         /* Not enough levels to fullfil the request, add the
            remaining clauses.*/
         move_clauses(reldata->clauses_rest, new_ax);
         move_formulas(reldata->formulas_rest, new_fax);
         break;
      }
      set = PStackElementP(reldata->relevance_levels, base);
      move_clauses(set, new_ax);

      set = PStackElementP(reldata->relevance_levels, base+1);
      move_formulas(set, new_fax);
   }
   ClauseSetFree(state->axioms);
   FormulaSetFree(state->f_axioms);
   state->axioms   = new_ax;
   state->f_axioms = new_fax;

   GCRegisterFormulaSet(state->gc_terms, state->f_axioms);
   GCRegisterClauseSet(state->gc_terms, state->axioms);
}


/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/




/*-----------------------------------------------------------------------
//
// Function: RelevanceAlloc()
//
//   Allocate a relevancy data structure - mostly used to be able to
//   clearly state invariants. After initialization:
//   - Core contains the newly found relevant clauses and formulas
//   - Rest contains the remainder of clauses and formulas
//   - new_codes is the set of newly found relevant function symbols.
//   - f_code_relevance contains for all f_codes the relevance level
//     (if found relevant already) or 0.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

Relevance_p RelevanceAlloc(void)
{
   Relevance_p handle = RelevanceCellAlloc();

   handle->sig              = NULL;

   handle->clauses_core     = PListAlloc();
   handle->formulas_core    = PListAlloc();

   handle->clauses_rest     = PListAlloc();
   handle->formulas_rest    = PListAlloc();

   handle->clauses_index    = FIndexAlloc();
   handle->formulas_index   = FIndexAlloc();

   handle->fcode_relevance  = PDArrayAlloc(100, 0);
   handle->new_codes        = PStackAlloc();
   handle->relevance_levels =  PStackAlloc();
   return handle;
}


/*-----------------------------------------------------------------------
//
// Function: RelevanceFree()
//
//   Free a RelevanceCell data structure.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void RelevanceFree(Relevance_p junk)
{
   PList_p level;

   PListFree(junk->clauses_core);
   PListFree(junk->formulas_core);
   PListFree(junk->clauses_rest);
   PListFree(junk->formulas_rest);
   FIndexFree(junk->clauses_index);
   FIndexFree(junk->formulas_index);

   PDArrayFree(junk->fcode_relevance);
   PStackFree(junk->new_codes);

   while(!PStackEmpty(junk->relevance_levels))
   {
      level = PStackPopP(junk->relevance_levels);
      PListFree(level);
   }
   PStackFree(junk->relevance_levels);

   RelevanceCellFree(junk);
}




/*-----------------------------------------------------------------------
//
// Function: ClausePListPrint()
//
//   Print a plist of clauses.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ClausePListPrint(FILE* out, PList_p list)
{
   PList_p  handle;
   Clause_p clause;

   for(handle=list->succ;
       handle != list;
       handle = handle->succ)
   {
      clause = handle->key.p_val;
      ClausePrint(out, clause, true);
      fputc('\n', out);
   }
}

/*-----------------------------------------------------------------------
//
// Function: FormulaPListPrint()
//
//   Print a plist of WFormulas.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void FormulaPListPrint(FILE* out, PList_p list)
{
   PList_p    handle;
   WFormula_p form;

   for(handle=list->succ;
       handle != list;
       handle = handle->succ)
   {
      form = handle->key.p_val;
      WFormulaPrint(out, form, true);
      fputc('\n', out);
   }
}




/*-----------------------------------------------------------------------
//
// Function: RelevanceDataInit()
//
//   Initialize a relevancy data structure - Split conjectures and
//   non-conjectures, and index the non-conjectures.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long RelevanceDataInit(ProofState_p state, Relevance_p data)
{
   long res = 0;

   data->sig = state->signature;

   res += ClauseSetSplitConjectures(state->axioms,
                                    data->clauses_core,
                                    data->clauses_rest);
   res += FormulaSetSplitConjectures(state->f_axioms,
                                    data->formulas_core,
                                    data->formulas_rest);

   FIndexAddPLClauseSet(data->clauses_index, data->clauses_rest);
   FIndexAddPLFormulaSet(data->formulas_index, data->formulas_rest);

   return res;
}


/*-----------------------------------------------------------------------
//
// Function: RelevanceDataCompute()
//
//   Compute the relevance levels.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

Relevance_p RelevanceDataCompute(ProofState_p state)
{
   Relevance_p handle = RelevanceAlloc();
   long level = 1;

   (void)RelevanceDataInit(state, handle);

   while(!(PListEmpty(handle->clauses_core) &&
           PListEmpty(handle->formulas_core)))
   {
      /*
      printf("Level %ld core:\n", level);
      ClausePListPrint(stdout, handle->clauses_core);
      FormulaPListPrint(stdout, handle->formulas_core);
      printf("\n");
      */
      find_level_fcodes(handle, level);

      PStackPushP(handle->relevance_levels, handle->clauses_core);
      PStackPushP(handle->relevance_levels, handle->formulas_core);

      handle->clauses_core  = PListAlloc();
      handle->formulas_core = PListAlloc();

      extract_new_core(handle);
      level = level+1;
   }
   handle->max_level = level;

   return handle;
}



/*-----------------------------------------------------------------------
//
// Function: ProofStatePreprocess()
//
//   Perform proof state preprocssing, in particular compute relevancy
//   data and perform relevancy pruning.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long ProofStatePreprocess(ProofState_p state, long level)
{
   Relevance_p reldata;
   long old_axno, new_axno;

   if(!level)
   {
      return 0;
   }
   reldata = RelevanceDataCompute(state);

   old_axno = ProofStateAxNo(state);
   proofstate_rel_prune(state, reldata, level);
   new_axno = ProofStateAxNo(state);

   RelevanceFree(reldata);

  return old_axno-new_axno;
}

/*  Alternating path relevance stuff
 * 
*/

APR_p APRAlloc(short int type, Eqn_p literal, Clause_p clause)
{
	APR_p handle = APRCellAlloc();
	handle->type = type;
	handle->literal = literal;
	handle->clause = clause;
	handle->edges = PStackAlloc();
	return handle;
}

void APRFree(APR_p trash)
{
	PStackFree(trash->edges);
	APRCellFree(trash);
}

APRControl_p APRControlAlloc()
{
	APRControl_p handle = APRControlCellAlloc();
	handle->map = IntMapAlloc();
	handle->buckets = PStackAlloc();
	handle->graph_nodes = PStackAlloc();
	return handle;
}

void APRControlFree(APRControl_p trash)
{
	IntMapFree(trash->map);
	PStack_p trash_bucket = NULL;
	while (!PStackEmpty(trash->buckets))
	{
		trash_bucket = PStackPopP(trash->buckets);
		PStackFree(trash_bucket);
	}
	assert(PStackEmpty(trash->buckets));
	PStackFree(trash->buckets);
	APR_p trash_node = NULL;
	while (!PStackEmpty(trash->graph_nodes))
	{
		trash_node = PStackPopP(trash->graph_nodes);
		APRFree(trash_node);
	}
	assert(PStackEmpty(trash->graph_nodes));
	PStackFree(trash->graph_nodes);
	
}

APRControl_p APRBuildGraph(ClauseSet_p clauses)
{
	APRControl_p control = APRControlAlloc();
	IntMap_p map = control->map;
	PStack_p graph_nodes = control->graph_nodes;
	PStack_p buckets = control->buckets;
	
	/* Make the nodes, put them in appropriate buckets,
	* and add a map taking each clause ident in set to its bucket
	*/
	Clause_p handle = clauses->anchor->succ;
	while (handle != clauses->anchor)
	{
		assert(handle);
		assert(handle->ident);
		APRGraphAddNodes(control, handle);
		handle = handle->succ;
	}
	// Now we need to actually build the graph.
	// Add all possible edges from every node.
   long num_edges = APRGraphUpdateEdges(control);
	
	printf("# APR Graph with %ld nodes and %ld edges created.\n",PStackGetSP(graph_nodes),num_edges);
	return control;
}

long APRGraphUpdateEdges(APRControl_p control)
{
	PStack_p graph_nodes = control->graph_nodes;
	IntMap_p map = control->map;
	long num_edges = 0;
	for (PStackPointer graph_iterator = 0; graph_iterator<PStackGetSP(graph_nodes); graph_iterator++)
	{
		APR_p current_node = PStackElementP(graph_nodes, graph_iterator);
		Clause_p current_clause = current_node->clause;
		Eqn_p current_literal = current_node->literal;
		if (PStackGetSP(current_node->edges) > 0)
		{
			PStackFree(current_node->edges);
			current_node->edges = PStackAlloc();
		}
		PStack_p current_edges = current_node->edges;
		long current_ident = current_clause->ident;
		if (current_ident < 0)
		{
			current_ident = current_ident - LONG_MIN;
		}
		
		assert(current_node);
		assert(current_clause);
		assert(current_literal);
		assert(current_edges);
		assert(current_node->type);
		assert(current_ident > 0);
		
		if (current_node->type == 1)
		{
			// Create type 2 (intra-clause) edges
			PStack_p current_bucket = IntMapGetVal(map, current_ident);
			assert(current_bucket);
			
			for (PStackPointer bucket_iterator = 0; bucket_iterator < PStackGetSP(current_bucket); bucket_iterator++)
			{
				APR_p bucket_node = PStackElementP(current_bucket, bucket_iterator);
				assert(bucket_node);
				assert(bucket_node->type);
				if (bucket_node->type == 1) // Wrong type of node
				{
					continue;
				}
				else if (bucket_node->type == 2)
				{
					if (bucket_node->literal != current_literal)
					{
						assert(bucket_node->clause == current_clause);
						PStackPushP(current_edges, bucket_node);
						num_edges++;
					}
				}
			}
		}
		else if (current_node->type == 2)
		{
			// Create type 1 (inter-clause) edges
			// Iterate again over the nodes
			for (PStackPointer graph_iterator2 = 0; graph_iterator2 < PStackGetSP(graph_nodes); graph_iterator2++)
			{
				APR_p visited_node = PStackElementP(graph_nodes, graph_iterator2);
				assert(visited_node);
				if (visited_node->type == 2 || visited_node->clause == current_clause)
				{
					continue;
				}
				else if (visited_node->type == 1)
				{
					// Check to see if we can make a type 1 edge
					if (APRComplementarilyUnifiable(current_literal, visited_node->literal))
					{
						PStackPushP(current_edges, visited_node);
						num_edges++;
					}
				}
			}
		}
	}
	return num_edges;
}

bool APRComplementarilyUnifiable(Eqn_p a, Eqn_p b)
{
	assert (a && b);
	if (a==b) return false;  // Easy case...
	
	if (EqnIsPositive(a) && EqnIsPositive(b)) return false;
	if (EqnIsNegative(a) && EqnIsNegative(b)) return false;
	
	Eqn_p a_disj = EqnCopyDisjoint(a);
	bool res = EqnUnifyP(a_disj, b);
	EqnFree(a_disj);
	return res;
}

/*  Return number of clauses added to the APR graph
 * 
*/
int APRGraphAddClauses(APRControl_p control, ClauseSet_p clauses)
{
	IntMap_p map = control->map;
	int num_added = 0;
	Clause_p handle = clauses->anchor->succ;
	while (handle != clauses->anchor)
	{
		long handle_ident = handle->ident;
		if (handle_ident < 0)
		{
			handle_ident = handle_ident - LONG_MIN;
		}
		if (IntMapGetVal(map, handle_ident) == NULL)
		{
			APRGraphAddNodes(control, handle);
			num_added++;
			// Add the clause to the graph
		}
		handle = handle->succ;
	}
	long num_edges = 0;
	num_edges = APRGraphUpdateEdges(control);
	return num_added;
}

/*  Return number of clauses added to the APR graph
 * 
*/
int APRGraphAddClausesList(APRControl_p control, PList_p clauses)
{
	IntMap_p map = control->map;
	int num_added = 0;
	PList_p anchor = clauses;
	PList_p handle = clauses->succ;
	while (handle != anchor)
	{
		Clause_p handle_clause = handle->key.p_val;
		long handle_ident = handle_clause->ident;
		if (handle_ident < 0)
		{
			handle_ident = handle_ident - LONG_MIN;
		}
		if (IntMapGetVal(map, handle_ident) == NULL)
		{
			APRGraphAddNodes(control, handle_clause);
			num_added++;
			// Add the clause to the graph
		}
		handle = handle->succ;
	}
	long num_edges = 0;
	num_edges = APRGraphUpdateEdges(control);
	return num_added;
}

/*
 * Return true if clause is already in the graph, false, otherwise.
 * If it is not in the graph, add it.
 * 
 * WARNING: This method does Not add the edges!  Only creates the nodes.
*/
bool APRGraphAddNodes(APRControl_p control, Clause_p clause)
{
	assert(control);
	assert(clause);
	// Nodes
	PStack_p buckets = control->buckets; 
	IntMap_p map = control->map;
	PStack_p graph_nodes = control->graph_nodes;
	PStack_p clause_bucket = PStackAlloc();
	PStackPushP(buckets, clause_bucket);
	long handle_ident = clause->ident;
	if(handle_ident < 0)
	{
		handle_ident = handle_ident - LONG_MIN;
	}
	//printf("/* APR graph */ ");ClausePrint(GlobalOut, handle, true);printf("\n");
	//printf("# handle_ident %ld\n", handle_ident);
	IntMapAssign(map, handle_ident, clause_bucket);
	PStack_p clause_literals = EqnListToStack(clause->literals);
	for (PStackPointer p = 0; p < PStackGetSP(clause_literals); p++)
	{
		Eqn_p literal = PStackElementP(clause_literals, p);
		APR_p type1 = APRAlloc(1, literal, clause);
		APR_p type2 = APRAlloc(2, literal, clause);
		PStackPushP(clause_bucket, type1);
		PStackPushP(graph_nodes, type1);
		PStackPushP(clause_bucket, type2);
		PStackPushP(graph_nodes, type2);
	}
	PStackFree(clause_literals);
	return false;
}

/* Collect the clauses that are within relevance distance of set.
 * Uses the APR graph specified by the APRControl_p
 * Set must be added to the APR graph specified by control
 * by the method APRGraphAddClauses
*/

PStack_p APRRelevance(APRControl_p control, ClauseSet_p set, int relevance)
{
	assert(relevance);
	assert(control);
	assert(set);
	IntMap_p map = control->map;
	int search_distance = (2*relevance) - 2;
	PStack_p handle_bucket = NULL;
	PStack_p starting_nodes = PStackAlloc();
	
	Clause_p handle = set->anchor->succ;
	while (handle != set->anchor)
	{
		long handle_ident = handle->ident;
		if (handle_ident < 0)
		{
			handle_ident = handle_ident - LONG_MIN;
		}
		handle_bucket = IntMapGetVal(map, handle_ident);
		assert(handle_bucket);
		for (PStackPointer p = 0; p < PStackGetSP(handle_bucket); p++)
		{
			APR_p handle_node = PStackElementP(handle_bucket, p);
			assert(handle_node);
			if (handle_node->type == 2)
			{
				PStackPushP(starting_nodes, handle_node);
			}
		}
		handle = handle->succ;
		// handle_bucket is the collection of nodes corresponding to handle in the apr graph
		// this method does NOT add nodes if set is not already included in the apr graph
	}
	PTree_p clause_tree = NULL;
	int num_found = APRBreadthFirstSearch(control, starting_nodes, &clause_tree, search_distance);
	printf("# %d relevant clauses found.\n", num_found);
	PStack_p res = PStackAlloc();
	PTreeToPStack(res, clause_tree);
	PStackFree(starting_nodes);
	PTreeFree(clause_tree);
	return res;
}

/*  Poorly written breadth first search that searches through all edges
 *  connected to elements of nodes.  Clauses corresponding to discovered
 *  nodes are added to the PTree of clauses.  When relevance reaches 0,
 *  the search terminates and returns the tree of clauses.
 * 
*/

int APRBreadthFirstSearch(APRControl_p control, PStack_p nodes, PTree_p *clauses, int relevance)
{	
	//PStack_p temp = PStackAlloc();
	PTree_p temp = NULL;
	int num_clauses_found = 0;
	for (PStackPointer p=0; p<PStackGetSP(nodes); p++)
	{
		APR_p node = PStackElementP(nodes, p);
		PStack_p edges = node->edges;
		Clause_p node_clause = node->clause;
		assert(node);
		assert(edges);
		assert(node_clause);
		bool clause_added = PTreeStore(clauses, node_clause);
		if (clause_added)
		{
			//printf("# Relevant clause found in BFS: ");
			//ClausePrint(GlobalOut, node_clause, true);
			//printf("\n");
			num_clauses_found++;
		}
		//printf("edges: %ld relevance: %d\n", PStackGetSP(edges), relevance);
		for (PStackPointer r=0; r<PStackGetSP(edges); r++)
		{
			APR_p new_node = PStackElementP(edges, r);
			assert(new_node);
			//PStackPushP(temp, new_node);
			PTreeStore(&temp, new_node);
		}
	}
	PStackReset(nodes);
	PStack_p temp_stack = PStackAlloc();
	PTreeToPStack(temp_stack, temp);
	//printf("temp: %ld nodes: %ld relevance: %d\n", PStackGetSP(temp_stack), PStackGetSP(nodes), relevance);
	for (PStackPointer q=0; q<PStackGetSP(temp_stack); q++)
	{
		APR_p temp_node = PStackElementP(temp_stack, q);
		assert(temp_node);
		PStackPushP(nodes, temp_node);
	}
	PStackFree(temp_stack);
	PTreeFree(temp);
	if (relevance != 0)
	{
		num_clauses_found += APRBreadthFirstSearch(control, nodes, clauses, relevance - 1);
	}
	return num_clauses_found;
}

/* From the APR graph specified by control, find the clauses within relevance distance
 * of a clause from the list.  Does not add the clauses of list to the graph-
 * to find any relevant clauses they must be added to the graph with
 * APRGraphAddClauses.
 *
*/

PStack_p APRRelevanceList(APRControl_p control, PList_p list, int relevance)
{
	assert(relevance);
	assert(control);
	assert(list);
	IntMap_p map = control->map;
	int search_distance = (2*relevance) - 2;
	PStack_p handle_bucket = NULL;
	PStack_p starting_nodes = PStackAlloc();
	
	PList_p anchor = list;
	PList_p list_handle = anchor->succ;
	int list_counter = 0;
	// Add the nodes corresponding to the clauses of list
	// to the collection of starting nodes
	while (list_handle != anchor)
	{
		list_counter++;
		Clause_p handle = list_handle->key.p_val;
		//printf("# List clause: ");ClausePrint(GlobalOut, handle, true);printf("\n");
		long handle_ident = handle->ident;
		if (handle_ident < 0)
		{
			handle_ident = handle_ident - LONG_MIN;
		}
		handle_bucket = IntMapGetVal(map, handle_ident);
		//printf("%p\n", handle_bucket);
		assert(handle_bucket);
		for (PStackPointer p = 0; p < PStackGetSP(handle_bucket); p++)
		{
			APR_p handle_node = PStackElementP(handle_bucket, p);
			assert(handle_node);
			if (handle_node->type == 2)
			{
				//printf("# Found type 2 node with %ld edges\n", PStackGetSP(handle_node->edges));
				PStackPushP(starting_nodes, handle_node);
			}
		}
		list_handle = list_handle->succ;
	}
	//printf("# %ld nodes corresponding to list of length %d found.\n", PStackGetSP(starting_nodes), list_counter);
	PTree_p clause_tree = NULL;
	int num_found = APRBreadthFirstSearch(control, starting_nodes, &clause_tree, search_distance);
	//printf("# %d relevant clauses found.\n", num_found);
	PStack_p res = PStackAlloc();
	PTreeToPStack(res, clause_tree);
	PStackFree(starting_nodes);
	PTreeFree(clause_tree);
	return res;
}

/*
 *  Return a stack of clauses from set that are within relevance
 *  distance of clauses from list.
 *  The clauses of list must be members of set,
 *  or added to the graph corresponding to control by changing 
 *  this method.
 * 
*/

PStack_p APRRelevanceNeighborhood(ClauseSet_p set, PList_p list, int relevance)
{
	APRControl_p control = APRBuildGraph(set);
	ClauseSet_p equality_axioms = EqualityAxioms(set->anchor->succ->literals->bank);
	APRGraphAddClauses(control, equality_axioms);
	PStack_p relevant = APRRelevanceList(control, list, relevance);
	PStack_p relevant_without_equality_axs = PStackAlloc();
	for (PStackPointer p=0 ; p<PStackGetSP(relevant); p++)
	{
		Clause_p relevant_clause = PStackElementP(relevant, p);
		//~ PStack_p relevant_nodes = IntMapGetVal(control->map, relevant_clause->ident - LONG_MIN);
		//~ if (relevant_clause->set == equality_axioms)
		//~ {
			//~ printf("E ");
		//~ }
		//~ else
		//~ {
			//~ printf("C ");
		//~ }
		//~ ClausePrint(GlobalOut, relevant_clause, true);printf("\n");
		//~ for (PStackPointer r = 0; r < PStackGetSP(relevant_nodes); r++)
		//~ {
			//~ APR_p node = PStackElementP(relevant_nodes, r);
			//~ printf("%d:%ld ", node->type, PStackGetSP(node->edges));
		//~ }
		//~ printf("\n");
		if (relevant_clause->set != equality_axioms)
		{
			PStackPushP(relevant_without_equality_axs, relevant_clause);
		}
	}
	ClauseSetFree(equality_axioms);
	PStackFree(relevant);
	APRControlFree(control);
	return relevant_without_equality_axs;
}

/*  Removes axioms from proofstate that are not relevant to
 *  conjectures.  Deletes the original clauseset of axioms
*/

void APRProofStateProcess(ProofState_p proofstate, int relevance)
{
	//printf("# Alternating path relevance distance: %d\n", relevance);
	PList_p conjectures = PListAlloc();
	PList_p non_conjectures = PListAlloc();
	ClauseSetSplitConjectures(proofstate->axioms, 
									  conjectures, 
									  non_conjectures);
	PListFree(non_conjectures);
	if (!PListEmpty(conjectures))
	{
		PStack_p relevant = APRRelevanceNeighborhood(proofstate->axioms,
																	conjectures,
																	relevance);
		printf("# Relevant axioms at relevance distance %d: %ld of %ld\n", relevance, 
																								 PStackGetSP(relevant), 
																								 proofstate->axioms->members);
		if (PStackGetSP(relevant) < proofstate->axioms->members)
		{
			proofstate->state_is_complete = false;
		}
		ClauseSet_p relevant_set = ClauseSetAlloc();
		for (PStackPointer p=0; p<PStackGetSP(relevant); p++)
		{
			Clause_p relevant_clause = PStackElementP(relevant, p);
			assert(relevant_clause);
			ClauseSetMoveClause(relevant_set, relevant_clause);
		}
		ClauseSetFree(proofstate->axioms);
		proofstate->axioms = relevant_set;
		assert(proofstate->axioms->members > 0);
		PStackFree(relevant);
	}
	PListFree(conjectures);
}

ClauseSet_p EqualityAxioms(TB_p bank)
{
	//Setup
	Type_p i_type = bank->sig->type_bank->i_type;
	Term_p x = VarBankGetFreshVar(bank->vars, i_type);
	Term_p y = VarBankGetFreshVar(bank->vars, i_type);
	Term_p z = VarBankGetFreshVar(bank->vars, i_type);
	ClauseSet_p equality_axioms = ClauseSetAlloc();
	
	// Reflexivity
	/*
	Eqn_p x_equals_x = EqnAlloc(x, x, bank, true);
	Clause_p clause1 = ClauseAlloc(x_equals_x);
	ClauseRecomputeLitCounts(clause1);
	ClauseSetInsert(equality_axioms, clause1);
	*/
	
	// Symmetry clause 1
	/*
	Eqn_p y_equals_x = EqnAlloc(y, x, bank, true);
	Eqn_p x_neq_y = EqnAlloc(x, y, bank, false);
	EqnListAppend(&y_equals_x, x_neq_y);
	Clause_p clause2 = ClauseAlloc(y_equals_x);
	ClauseRecomputeLitCounts(clause2);
	ClauseSetInsert(equality_axioms, clause2);
	*/
	
	
	// Symmetry clause 2
	/*
	Eqn_p x_equals_y = EqnAlloc(x, y, bank, true);
	Eqn_p y_neq_x = EqnAlloc(y, x, bank, false);
	EqnListAppend(&x_equals_y, y_neq_x);
	Clause_p clause3 = ClauseAlloc(x_equals_y);
	ClauseRecomputeLitCounts(clause2);
	ClauseSetInsert(equality_axioms, clause3);
	*/
	
	// Transitivity
	Eqn_p x_equals_z = EqnAlloc(x, z, bank, true);
	Eqn_p x_neq_y2 = EqnAlloc(x, y, bank, false);
	Eqn_p y_neq_z = EqnAlloc(y, z, bank, false);
	EqnListAppend(&x_equals_z, x_neq_y2);
	EqnListAppend(&x_equals_z, y_neq_z);
	Clause_p clause4 = ClauseAlloc(x_equals_z);
	ClauseRecomputeLitCounts(clause4);
	ClauseSetInsert(equality_axioms, clause4);
	
	return equality_axioms;
}

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


