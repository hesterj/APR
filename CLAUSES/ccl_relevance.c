/*----------------------------------------------------------------------:

::::  : ccl_relevance.c

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
#include <che_clausesetfeatures.h>


/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/

#define KBLU  "\x1B[34m"
#define RESET "\033[0m"
#define RED   "\x1B[31m"

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
            { PDArrayAssignInt(reldata->fcode_relevance, f, level);
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

APR_p APRAlloc(short int type, Eqn_p literal, Clause_p clause, bool equality)
{
	APR_p handle = APRCellAlloc();
	handle->visited = false;
	handle->type = type;
	handle->literal = literal;
	handle->clause = clause;
	handle->edges = PStackAlloc();
	handle->equality_node = equality;
	handle->id = 0;
	return handle;
}

void APRFree(APR_p trash)
{
	PStackFree(trash->edges);
	APRCellFree(trash);
}

APRControl_p APRControlAlloc(Sig_p sig, TB_p terms)
{
	APRControl_p handle = APRControlCellAlloc();
	handle->map = IntMapAlloc();
	handle->original_clause_map = IntMapAlloc();
	handle->fresh_clauses = ClauseSetAlloc();
	handle->buckets = PStackAlloc();
	handle->graph_nodes = PStackAlloc();
	handle->type1_nodes = PStackAlloc();
	handle->type2_nodes = PStackAlloc();
	handle->type1_equality_nodes = PStackAlloc();
	handle->type1_nonequality_nodes = PStackAlloc();
	handle->equality_axioms = NULL;
	handle->substitution_axiom_characteristic = FixedDArrayAlloc(sig->size);
	FixedDArrayInitialize(handle->substitution_axiom_characteristic, 0);
	handle->sig = sig;
	handle->terms = terms;
	handle->equality = false;
	handle->build_graph = false;
	handle->max_used_node_id = 0;
	handle->max_var = 0;
	return handle;
}

void APRControlFree(APRControl_p trash)
{
	IntMapFree(trash->map);
	IntMapFree(trash->original_clause_map);
	ClauseSetFree(trash->fresh_clauses);
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
	PStackFree(trash->type1_nodes);
	PStackFree(trash->type2_nodes);
	PStackFree(trash->type1_equality_nodes);
	PStackFree(trash->type1_nonequality_nodes);
	// Free the equality axioms as they are no longer needed, and their stack
	if (trash->equality_axioms)
	{
		ClauseSetFree(trash->equality_axioms);
	}
	FixedDArrayFree(trash->substitution_axiom_characteristic);
	APRControlCellFree(trash);
}

/* Build the APR graph, with edges only being added if they are within
 * the appropriate relevance distance of the "set of support"
 * list of conjecture clauses.
 * 
 * Will return stack of clauses within relevance distance of conjectures
*/

PStack_p APRBuildGraphConjectures(APRControl_p control, ClauseSet_p clauses, PList_p conjectures, int distance)
{
	//APRControl_p control = APRControlAlloc();
	
	/* Make the nonequality nodes, put them in appropriate buckets,
	* and add a map taking each clause ident in set to its bucket
	*/
	Clause_p handle = clauses->anchor->succ;
	while (handle != clauses->anchor)
	{
		assert(handle);
		assert(handle->ident);
		APRGraphAddNodes(control, handle, false);
		handle = handle->succ;
	}
	
	// Now we need to actually build the graph.
	// Add all possible edges from the conjecture nodes.
	PStack_p relevant_stack = PStackAlloc();
	PTree_p start_tree = NULL;
	PTree_p already_visited = NULL;
	PStack_p start_nodes = APRCollectNodesFromList(control, conjectures);
	
	// Make sure the conjecture clauses are marked as relevant
	for (PStackPointer p=0; p<PStackGetSP(start_nodes); p++)
	{
		APR_p start_node = PStackElementP(start_nodes, p);
		Clause_p clause_handle = start_node->clause;
		if (!ClauseQueryProp(clause_handle, CPIsAPRRelevant))
		{
			ClauseSetProp(clause_handle, CPIsAPRRelevant);
			PStackPushP(relevant_stack, clause_handle);
		}
	}
	
	fprintf(GlobalOut, "# Creating %ld %d-neighborhoods in graph of %ld clauses and %ld literals.\n", PStackGetSP(start_nodes),
																																			distance,
																																			clauses->members,
																																			PStackGetSP(control->type1_nodes));
   APRGraphUpdateEdgesFromListStack(control, &already_visited,
													 start_nodes, 
													 relevant_stack, 
													 distance);
   fprintf(GlobalOut, "# Relevancy graph completed.  %ld relevant total.\n", PStackGetSP(relevant_stack));
	PStackFree(start_nodes);
	PTreeFree(start_tree);
	PTreeFree(already_visited);
	return relevant_stack;
}

/*  This method is meant to be used on an apr graph that has the nodes
 *  initialized, with the initial start_nodes PTree_p containing
 *  conjecture nodes in this graph.  It builds edges outwards from the 
 *  starting nodes, and adds the corresponding clauses to the ptree.
 * 
*/

long APRGraphUpdateEdgesFromListStack(APRControl_p control,
											PTree_p *already_visited,
											PStack_p start_nodes_stack, 
											PStack_p relevant, 
											int distance)
{
	if (distance < 0)
	{
		return 0;
	}
	IntMap_p map = control->map;
	PStack_p new_start_nodes = PStackAlloc();
	long num_edges = 0;
	// Create the appropriate substitution axioms corresponding to newly
	// discovered symbols and add the corresponding nodes to the APR graph
	if (control->equality_axioms)
	{
		int subst_axs_added = APRNodeStackAddSubstAxioms(control, start_nodes_stack);
		fprintf(GlobalOut, "# Created %d new equality axioms\n", subst_axs_added);
	}
	// Create new edges at this level
	fprintf(GlobalOut, "# Updating APR edges d:%d sn:%ld\n", distance, PStackGetSP(start_nodes_stack));
	for (PStackPointer graph_iterator = 0; graph_iterator<PStackGetSP(start_nodes_stack); graph_iterator++)
	{
		//fprintf(GlobalOut, "\r# %ld remaining at depth", PStackGetSP(start_nodes_stack)-graph_iterator);
		//fflush(GlobalOut);
		APR_p current_node = PStackElementP(start_nodes_stack, graph_iterator);
		PStack_p current_edges = current_node->edges;
		if (PStackGetSP(current_node->edges) > 0)
		{
			continue;
		}
		
		Clause_p current_clause = current_node->clause;
		Eqn_p current_literal = current_node->literal;
		long current_ident = ClauseGetIdent(current_clause);
		
		assert(current_node);
		assert(current_clause);
		assert(ClauseQueryProp(current_clause, CPIsAPRRelevant));
		assert(current_literal);
		assert(current_edges);
		assert(current_node->type);
		assert(current_ident > 0);
		assert(current_node->visited);

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
				assert(bucket_node->clause == current_clause);
				if ((bucket_node->type == 1))
				{
					continue;
				}
				// node has type 2
				assert(bucket_node->type == 2);
				if (bucket_node->literal != current_literal)
				{
					if (bucket_node->visited)
					{
						PStackPushP(current_edges, bucket_node);
						num_edges++;
					}
					else
					{
						bucket_node->visited = true;
						PStackPushP(current_edges, bucket_node);
						PStackPushP(new_start_nodes, bucket_node);
						num_edges++;
					}
				}
			}
		}
		else if (current_node->type == 2)
		{
			// Choose the appropriate stack to iterate over.
			// This is to prevent linking equality axioms as relevant to eachother.
			//int numthreads = omp_get_num_threads();
			//printf("# %d threads\n", numthreads);
			PStack_p type1stack = NULL;
			if (current_node->equality_node)
			{
				type1stack = control->type1_nonequality_nodes;
				if (distance == 0)
				{
					continue; // Do not search from equality axioms at the last step.
				}
			}
			else
			{
				type1stack = control->type1_nodes;
			}
			// Try to create edges to type 1 nodes
			// Candidate for parallelization!  This is where the hard work happens
			//~ omp_lock_t writelock;
			//~ omp_init_lock(&writelock);
			//~ omp_set_num_threads(4);
			//~ #pragma omp parallel for
			for (PStackPointer t1_iter = 0; 
				  t1_iter < PStackGetSP(type1stack);
				  t1_iter++)
			{
				//printf("# Creating interclause edges\n");
				APRCreateInterClauseEdges(control,
													current_literal,
													type1stack, 
													new_start_nodes,
													current_edges,
													relevant, 
													t1_iter, 
													distance);
			}
			//omp_destroy_lock(&writelock);
		}
	}
	fprintf(GlobalOut, "\n");
	printf("# Finished iterating\n");
	printf("# %ld edges created\n", num_edges);
	num_edges += APRGraphUpdateEdgesFromListStack(control,
														  already_visited,
														  new_start_nodes, 
														  relevant, 
														  distance - 1);
	PStackFree(new_start_nodes);
	return num_edges;
}
/*  Collect the type 2 nodes of the APR graph in to a PStack_p return
 *  it.  This method is meant to be used at the start of an APR
 *  graph search, with the PList_p corresponding to conjectures.
 *  Type 2 nodes have interclause edges, type 1 nodes would only have
 *  edges to the nodes we are interested in.
 * 
*/

PStack_p APRCollectNodesFromList(APRControl_p control, PList_p list)
{
	PList_p list_handle = list->succ;
	IntMap_p map = control->map;
	PStack_p graph_nodes = PStackAlloc();
	while (list_handle != list)
	{
		Clause_p clause_handle = list_handle->key.p_val;
		long current_ident = ClauseGetIdent(clause_handle);
		printf("# Searching for bucket of ");ClausePrint(GlobalOut, clause_handle, true);
		PStack_p handle_bucket = IntMapGetVal(map, current_ident);
		if (handle_bucket == NULL)  // If there is no bucket for this clause, create its nodes and add the bucket
		{
			printf(" failed");
			APRGraphAddClausesList(control, list);
			handle_bucket = IntMapGetVal(map, current_ident);
		}
		printf("\n");
		assert(handle_bucket);
		assert(PStackGetSP(handle_bucket));
		for (PStackPointer p = 0; p < PStackGetSP(handle_bucket); p++)
		{
			APR_p clause_node = PStackElementP(handle_bucket, p);
			if (clause_node->type == 2)
			{
				PStackPushP(graph_nodes, clause_node);
				ClauseSetProp(clause_handle, CPIsAPRRelevant);
				clause_node->visited = true;
			}
		}
		list_handle = list_handle->succ;
	}
	return graph_nodes;
}

/*  Updates all possible edges of the graph corresponding to control.
 *  Deletes all old edges. 
 *  Returns the new number of edges.
 * 
 *  Slow on big graphs!!!
*/

long APRGraphUpdateEdgesDeleteOld(APRControl_p control)
{
	printf("# Updating all APR edges\n");
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
		long current_ident = ClauseGetIdent(current_clause);
		
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
			for (PStackPointer graph_iterator2 = 0; graph_iterator2 < PStackGetSP(control->type1_nodes); graph_iterator2++)
			{
				APR_p visited_node = PStackElementP(control->type1_nodes, graph_iterator2);
				assert(visited_node);
				if (visited_node->clause == current_clause)
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

/*  Updates all possible edges of the graph corresponding to control.
 *  
 *  Returns the new number of edges.
 * 
 *  Slow on big graphs!!!
*/

long APRGraphUpdateEdges(APRControl_p control)
{
	PStack_p graph_nodes = control->graph_nodes;
	IntMap_p map = control->map;
	long num_edges = 0;
	//printf("# %ld nodes\n", PStackGetSP(graph_nodes));
	for (PStackPointer graph_iterator = 0; graph_iterator<PStackGetSP(graph_nodes); graph_iterator++)
	{
		//~ if (graph_iterator % 100 == 0)
		//~ {
			//~ printf(".");
			//~ fflush(stdout);
		//~ }
		APR_p current_node = PStackElementP(graph_nodes, graph_iterator);
		Clause_p current_clause = current_node->clause;
		Eqn_p current_literal = current_node->literal;
		if (PStackGetSP(current_node->edges) > 0)
		{
			PStackFree(current_node->edges);
			current_node->edges = PStackAlloc();
		}
		PStack_p current_edges = current_node->edges;
		long current_ident = ClauseGetIdent(current_clause);
		
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
			for (PStackPointer graph_iterator2 = 0; graph_iterator2 < PStackGetSP(control->type1_nodes); graph_iterator2++)
			{
				APR_p visited_node = PStackElementP(control->type1_nodes, graph_iterator2);
				assert(visited_node);
				if (visited_node->clause == current_clause)
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

/*  Return true if the equations a and b are complementarily
 *  unifiable.
*/ 

bool APRComplementarilyUnifiable(Eqn_p a, Eqn_p b)
{
	assert (a && b);
	if (a==b) return false;  // Easy case...  
	if (EqnIsPositive(a) && EqnIsPositive(b)) return false;
	if (EqnIsNegative(a) && EqnIsNegative(b)) return false;
	Eqn_p a_disj = EqnCopyDisjoint(a);
	//printf("a_disj: ");EqnTSTPPrint(GlobalOut, a_disj, true);printf("\n");
	//printf("b: ");EqnTSTPPrint(GlobalOut, b, true);printf("\n");

	bool res = EqnUnifyP(a_disj, b);
	EqnFree(a_disj);
	
	//printf("%d\n", res);
	return res;
}

/*  Return number of clauses added to the APR graph.
 *  This method adds the nodes corresponding to clauses from
 *  the set to the apr APR graph of control.
 * 
 *  Does not update edges!  That should be done when actually
 *  searching for the relevant clauses from some start nodes
 *  rather than udpating all edges at once.
 * 
*/
int APRGraphAddClauses(APRControl_p control, ClauseSet_p clauses, bool equality)
{
	IntMap_p map = control->map;
	int num_added = 0;
	Clause_p handle = clauses->anchor->succ;
	while (handle != clauses->anchor)
	{
		long handle_ident = ClauseGetIdent(handle);
		if (IntMapGetVal(map, handle_ident) == NULL)
		{
			APRGraphAddNodes(control, handle, equality);
			num_added++;
			// Add the clause to the graph
		}
		handle = handle->succ;
	}
	return num_added;
}

/*  Return number of clauses added to the APR graph
 *  This method adds the nodes from the clauses of 
 *  list to to the APR graph, then updates all the edges.
 * 
 *  Assumes the clauses of list are NOT equality axioms!
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
		long handle_ident = ClauseGetIdent(handle_clause);
		if (IntMapGetVal(map, handle_ident) == NULL) // Add the clause to the graph
		{
			APRGraphAddNodes(control, handle_clause, false);
			num_added++;
			// Add the clause to the graph
		}
		handle = handle->succ;
	}
	//APRGraphUpdateEdges(control);
	return num_added;
}

/*
 * Return true if clause is already in the graph, false, otherwise.
 * If it is not in the graph, add it.
 * 
 * WARNING: This method does Not add the edges!  Only creates the nodes.
*/
bool APRGraphAddNodes(APRControl_p control, Clause_p clause, bool equality)
{
	assert(control);
	assert(clause);
	// Nodes
	PStack_p buckets = control->buckets; 
	IntMap_p map = control->map;
	//IntMap_p original_clause_map = control->original_clause_map;
	PStack_p graph_nodes = control->graph_nodes;
	PStack_p clause_bucket = PStackAlloc();
	PStackPushP(buckets, clause_bucket);
	long handle_ident = ClauseGetIdent(clause);
	IntMapAssign(map, handle_ident, clause_bucket);
	//IntMapAssign(original_clause_map, handle_ident, clause);
	PStack_p clause_literals = EqnListToStack(clause->literals); // Original
	//Clause_p fresh_clause = ClauseCopyFresh(clause, control); //
	//ClauseSetInsert(control->fresh_clauses, fresh_clause); //
	//PStack_p clause_literals = EqnListToStack(fresh_clause->literals); //
	for (PStackPointer p = 0; p < PStackGetSP(clause_literals); p++)
	{
		Eqn_p literal = PStackElementP(clause_literals, p);
		APR_p type1 = APRAlloc(1, literal, clause, equality);
		APR_p type2 = APRAlloc(2, literal, clause, equality);
		type1->id = control->max_used_node_id + 1;
		type2->id = control->max_used_node_id + 2;
		control->max_used_node_id += 2;
		PStackPushP(clause_bucket, type1);
		PStackPushP(graph_nodes, type1);
		PStackPushP(clause_bucket, type2);
		PStackPushP(graph_nodes, type2);
		PStackPushP(control->type1_nodes, type1);
		PStackPushP(control->type2_nodes, type2);
		if (equality)
		{
			PStackPushP(control->type1_equality_nodes, type1);
		}
		else
		{
			PStackPushP(control->type1_nonequality_nodes, type1);
		}
	}
	assert(2*ClauseLiteralNumber(clause) == PStackGetSP(clause_bucket)); 
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
		long handle_ident = ClauseGetIdent(handle);
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
	printf("# APR BFS\n");
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
			num_clauses_found++;
		}
		for (PStackPointer r=0; r<PStackGetSP(edges); r++)
		{
			APR_p new_node = PStackElementP(edges, r);
			assert(new_node);
			PTreeStore(&temp, new_node);
		}
	}
	PStackReset(nodes);
	PStack_p temp_stack = PStackAlloc();
	PTreeToPStack(temp_stack, temp);
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
	long number_of_processors = sysconf(_SC_NPROCESSORS_ONLN);
	//~ pthread_t callThd[number_of_processors];
	//~ pthread_attr_t attr; 
	//~ pthread_attr_init(&attr);
   //~ pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
   //~ pthread_attr_destroy(&attr);
	int search_distance = (2*relevance) - 2;
	PStack_p handle_bucket = NULL;
	PStack_p starting_nodes = PStackAlloc();
	printf("# Number of processors available: %ld\n", number_of_processors);
	PList_p anchor = list;
	PList_p list_handle = anchor->succ;
	int list_counter = 0;
	// Add the nodes corresponding to the clauses of list
	// to the collection of starting nodes
	while (list_handle != anchor)
	{
		list_counter++;
		Clause_p handle = list_handle->key.p_val;
		long handle_ident = ClauseGetIdent(handle);
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
		list_handle = list_handle->succ;
	}
	printf("# %ld starting nodes corresponding to list of length %d found.\n",
			 PStackGetSP(starting_nodes), list_counter);
	PTree_p clause_tree = NULL;
	APRBreadthFirstSearch(control, starting_nodes, &clause_tree, search_distance);
	PStack_p res = PStackAlloc();
	PTreeToPStack(res, clause_tree);
	PStackFree(starting_nodes);
	PTreeFree(clause_tree);
	return res;
}

/*
 *  Return a stack of clauses from set that are within relevance
 *  distance of clauses from list
 * 
 * Side effects:  Adds equality axioms to the APR graph if equality is detected.
 *  
*/

PStack_p APRRelevanceNeighborhood(Sig_p sig, ClauseSet_p set, PList_p list, int relevance, bool equality, bool print_graph)
{
	APRControl_p control = APRControlAlloc(sig, set->anchor->succ->literals->bank);
	ClauseSet_p equality_axioms = NULL;
	control->equality = equality;
	if (equality && ClauseSetIsEquational(set))
	{
		//equality_axioms = ClauseSetAlloc();
		equality_axioms = EqualityAxioms(set->anchor->succ->literals->bank, true);  // true enables creation of equality substitution axioms
		control->equality_axioms = equality_axioms;
		ClauseSetSetProp(equality_axioms, CPDeleteClause);
		fprintf(GlobalOut, "# Building initial APR graph with %ld extra equality axiom(s)\n", equality_axioms->members);
		APRGraphAddClauses(control, equality_axioms, true);
	}
	else
	{
		fprintf(GlobalOut, "# Axioms nonequational or equality axioms disabled\n");
	}
	
	// Set the number of steps to take in building the graph
	int search_distance = (2*relevance) - 2;
	
	if (print_graph)
	{
		control->build_graph = true;
	}
	
	PStack_p relevant = APRBuildGraphConjectures(control, 
																set, 
																list, 
																search_distance);
	PStack_p relevant_without_equality_axs = PStackAlloc();
	
	if (print_graph)
	{
		APRGraphCreateDOTClauses(control);
	}
	for (PStackPointer p=0 ; p<PStackGetSP(relevant); p++)
	{
		Clause_p relevant_clause = PStackElementP(relevant, p);
		if (!ClauseQueryProp(relevant_clause, CPDeleteClause))
		{
			PStackPushP(relevant_without_equality_axs, relevant_clause);
		}
		else 
		{
			//if (ClauseIsConjecture(relevant_clause)) printf("# Delete clause is conjecture error\n");
			assert(ClauseQueryProp(relevant_clause, CPDeleteClause));
			ClauseDelProp(relevant_clause, CPDeleteClause);
		}
	}
	PStackFree(relevant);
	APRControlFree(control);
	return relevant_without_equality_axs;
}

/*  Removes axioms from proofstate that are not relevant to
 *  conjectures. 
*/

void APRProofStateProcess(ProofState_p proofstate, int relevance, bool equality, bool print_apr_graph)
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
		PStack_p relevant = APRRelevanceNeighborhood(proofstate->signature,
																	proofstate->axioms,
																	conjectures,
																	relevance, equality, print_apr_graph);
		fprintf(GlobalOut, "# Relevant axioms at relevance distance %d: %ld of %ld\n", relevance, 
																								 PStackGetSP(relevant), 
																								 proofstate->axioms->members);
		if (PStackGetSP(relevant) < proofstate->axioms->members)
		{
			proofstate->state_is_complete = false;
		}
		Clause_p axiom_handle = NULL;
		Clause_p tmp = NULL;
		for (axiom_handle = proofstate->axioms->anchor->succ;
			  axiom_handle != proofstate->axioms->anchor;
			  axiom_handle = tmp)
		{
			tmp = axiom_handle->succ;
			if (!ClauseQueryProp(axiom_handle, CPIsAPRRelevant))
			{
				ClauseSetMoveClause(proofstate->archive, axiom_handle);
			}
		}
		assert(proofstate->axioms->members > 0);
		PStackFree(relevant);
	}
	PListFree(conjectures);
}

/*  This method is meant to be called on a LIVE proof state.
 *  Causes incompleteness if unprocessed clauses are deleted.
 *  Keeps unprocessed clauses within relevance distance of
 *  the conjectures.  Discards other clauses.
 * 
 *  Does not create equality axioms for live proof state processing.
*/

void APRLiveProofStateProcess(ProofState_p proofstate, int relevance)
{
	assert(relevance);
	PList_p conjectures = PListAlloc();
	PList_p non_conjectures = PListAlloc();
	ClauseSetSplitConjectures(proofstate->axioms, 
									  conjectures, 
									  non_conjectures);
	PListFree(non_conjectures);
	if (!PListEmpty(conjectures))
	{
		PStack_p relevant = APRRelevanceNeighborhood(proofstate->signature,
																	proofstate->unprocessed,
																	conjectures,
																	relevance, false, false);
		printf("# Relevant unprocessed at relevance distance %d: %ld of %ld\n", relevance, 
																								 PStackGetSP(relevant), 
																								 proofstate->unprocessed->members);
		if (PStackGetSP(relevant) < proofstate->unprocessed->members)
		{
			proofstate->state_is_complete = false;
		}
		printf("# %ld relevant unprocessed clauses found\n", PStackGetSP(relevant));
		int removed = 0;
		ClauseSet_p new_unprocessed = ClauseSetAlloc();
		for (PStackPointer p=0; p<PStackGetSP(relevant); p++)
		{
			ClauseSetMoveClause(new_unprocessed, PStackElementP(relevant,p));
		}
		ClauseSetRemoveEvaluations(proofstate->unprocessed);
		ClauseSetFree(proofstate->unprocessed);
		proofstate->unprocessed = new_unprocessed;
		printf("Remaining members of unprocessed: %ld\n", proofstate->unprocessed->members);
		if (removed > 0)
		{
			proofstate->state_is_complete = false;
		}
	}
	PListFree(conjectures);
}
 
/*  Return a clause set of equality axioms appropriate for alternating
 *  path relevance.  If substitution is true, create substitution axioms
 *  for all non-internal symbols.
 * 
*/

ClauseSet_p EqualityAxioms(TB_p bank, bool substitution)
{
	//Setup
	printf("# Creating equality axioms\n");
	Sig_p sig = bank->sig;
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
	
	// Function/Predicate equality substitution axioms
	// There must be one for every f-code of a pred or non const func.
	
	FunCode f_count = sig->f_count; // Max used f_code
	
	if (substitution)
	{
		for (FunCode f_code = sig->internal_symbols + 1; f_code <= f_count; f_code++)
		{
			int arity = SigFindArity(sig, f_code);
			if (arity == 0) continue;
			PStack_p x_variables = PStackAlloc();
			PStack_p y_variables = PStackAlloc();
			Term_p x_0 = VarBankGetFreshVar(bank->vars, i_type);
			PStackPushP(x_variables, x_0);
			Term_p y_0 = VarBankGetFreshVar(bank->vars, i_type);
			//Term_p y_0 = VarBankGetAltVar(bank->vars, x_0);
			PStackPushP(y_variables, y_0);
			Eqn_p subst_axiom = EqnAlloc(x_0, y_0, bank, false);
			for (int i=1; i<arity; i++)
			{
				Term_p x_i = VarBankGetFreshVar(bank->vars, i_type);
				PStackPushP(x_variables, x_i);
				Term_p y_i = VarBankGetFreshVar(bank->vars, i_type);
				//Term_p y_i = VarBankGetAltVar(bank->vars, x_i);
				PStackPushP(y_variables, y_i);
				Eqn_p xi_neq_yi = EqnAlloc(x_i, y_i, bank, false);
				EqnListAppend(&subst_axiom, xi_neq_yi);
			}
			
			Term_p left_handle = TermDefaultCellAlloc();
			left_handle->arity = arity;
			left_handle->args = TermArgArrayAlloc(arity);
			left_handle->f_code = f_code;
			
			for (int i=0; i<arity; i++)
			{
				left_handle->args[i] = PStackElementP(x_variables, i);
			}
			left_handle->v_count = arity;
			left_handle = TBTermTopInsert(bank, left_handle);
			TypeInferSort(bank->sig, left_handle, NULL);
			Term_p right_handle = NULL;
			if (SigIsFunction(sig, f_code))
			{
				right_handle = TermDefaultCellAlloc();
				right_handle->arity = arity;
				right_handle->f_code = f_code;
				right_handle->args = TermArgArrayAlloc(arity);
				for (int i=0; i<arity; i++)
				{
					right_handle->args[i] = PStackElementP(y_variables, i);
				}
				right_handle->v_count = arity;
				right_handle = TBTermTopInsert(bank, right_handle);
				TypeInferSort(bank->sig, right_handle, NULL);
				Eqn_p final = EqnAlloc(left_handle, right_handle, bank, true);
				EqnListAppend(&subst_axiom, final);
			}
			else if (SigIsPredicate(sig, f_code))
			{
				right_handle = bank->true_term;
				assert(left_handle);
				assert(right_handle);
				Eqn_p seq = EqnAlloc(left_handle, right_handle, bank, false);
				EqnListAppend(&subst_axiom, seq);
				
				left_handle = TermDefaultCellAlloc();
				left_handle->arity = arity;
				left_handle->args = TermArgArrayAlloc(arity);
				left_handle->f_code = f_code;
				//left_handle->type = SigGetType(bank->sig, f_code);
				for (int i=0; i<arity; i++)
				{
					left_handle->args[i] = PStackElementP(y_variables, i);
				}
				left_handle->v_count = arity;
				left_handle = TBTermTopInsert(bank, left_handle);
				TypeInferSort(bank->sig, left_handle, NULL);
				Eqn_p final = EqnAlloc(left_handle, right_handle, bank, true);
				EqnListAppend(&subst_axiom, final);
			}
			
			Clause_p subst_axiom_clause = ClauseAlloc(subst_axiom);
			ClauseRecomputeLitCounts(subst_axiom_clause);
			ClauseSetInsert(equality_axioms, subst_axiom_clause);
			//printf("Substitution axiom:\n");
			//ClausePrint(GlobalOut, subst_axiom_clause, true);
			//printf("\n");
			PStackFree(x_variables);
			PStackFree(y_variables);
		}
	}
	
	printf("# Created %ld equality axioms.\n", equality_axioms->members);	
	return equality_axioms;
}

int APRNodeStackAddSubstAxioms(APRControl_p control, PStack_p nodes)
{
	int num_added = 0;
	for (PStackPointer p=0; p < PStackGetSP(nodes); p++)
	{
		num_added += APRNodeAddSubstAxioms(control, PStackElementP(nodes, p));
	}
	return num_added;
}

int APRNodeAddSubstAxioms(APRControl_p control, APR_p node)
{
	return EqnAddSubstAxioms(control, node->literal);
}
int EqnAddSubstAxioms(APRControl_p control, Eqn_p eqn)
{
	int num_added = 0;
	num_added += TermAddSubstAxioms(control, eqn->lterm);
	num_added += TermAddSubstAxioms(control, eqn->rterm);
	return num_added;
}
int TermAddSubstAxioms(APRControl_p control, Term_p term)
{
	int num_added = 0;
	Sig_p sig = control->sig;
	FixedDArray_p substitution_axiom_characteristic = control->substitution_axiom_characteristic;
	FunCode f_code = term->f_code;
	// If we have reached a variable or internal symbol, return 0
	if (f_code <= sig->internal_symbols) return 0;
	if (SigFindArity(sig, f_code) == 0) return 0;  
	if (SigIsPredicate(sig, f_code) || SigIsFunction(sig, f_code))
	{
		// Check to see if we have already made the corresponding substitution axiom
		if (substitution_axiom_characteristic->array[f_code] == 0)
		{
			substitution_axiom_characteristic->array[f_code] = f_code;
			num_added++;
			Clause_p substitution_axiom = ClauseCreateSubstitutionAxiom(control, sig, f_code);
			//ClauseSetProp(substitution_axiom, CPDeleteClause);
			//ClauseSetInsert(control->equality_axioms, substitution_axiom);
			assert(substitution_axiom);
			assert(substitution_axiom->set);
			APRGraphAddNodes(control, substitution_axiom, true);
		}
	}
	for (int i=0; i<term->arity; i++)
	{
		num_added += TermAddSubstAxioms(control, term->args[i]);
	}
	return num_added;
}

Clause_p ClauseCreateSubstitutionAxiom(APRControl_p control, Sig_p sig, FunCode f_code)
{
	TB_p bank = control->terms;
	Type_p i_type = sig->type_bank->i_type;
	int arity = SigFindArity(sig, f_code);
	if (arity == 0) return NULL;
	PStack_p x_variables = PStackAlloc();
	PStack_p y_variables = PStackAlloc();
	Term_p x_0 = VarBankGetFreshVar(bank->vars, i_type);
	PStackPushP(x_variables, x_0);
	Term_p y_0 = VarBankGetFreshVar(bank->vars, i_type);
	//Term_p y_0 = VarBankGetAltVar(bank->vars, x_0);
	PStackPushP(y_variables, y_0);
	Eqn_p subst_axiom = EqnAlloc(x_0, y_0, bank, false);
	for (int i=1; i<arity; i++)
	{
		Term_p x_i = VarBankGetFreshVar(bank->vars, i_type);
		PStackPushP(x_variables, x_i);
		Term_p y_i = VarBankGetFreshVar(bank->vars, i_type);
		//Term_p y_i = VarBankGetAltVar(bank->vars, x_i);
		PStackPushP(y_variables, y_i);
		Eqn_p xi_neq_yi = EqnAlloc(x_i, y_i, bank, false);
		EqnListAppend(&subst_axiom, xi_neq_yi);
	}
	
	Term_p left_handle = TermDefaultCellAlloc();
	left_handle->arity = arity;
	left_handle->args = TermArgArrayAlloc(arity);
	left_handle->f_code = f_code;
	
	for (int i=0; i<arity; i++)
	{
		left_handle->args[i] = PStackElementP(x_variables, i);
	}
	left_handle->v_count = arity;
	left_handle = TBTermTopInsert(bank, left_handle);
	TypeInferSort(bank->sig, left_handle, NULL);
	Term_p right_handle = NULL;
	if (SigIsFunction(sig, f_code))
	{
		right_handle = TermDefaultCellAlloc();
		right_handle->arity = arity;
		right_handle->f_code = f_code;
		right_handle->args = TermArgArrayAlloc(arity);
		for (int i=0; i<arity; i++)
		{
			right_handle->args[i] = PStackElementP(y_variables, i);
		}
		right_handle->v_count = arity;
		right_handle = TBTermTopInsert(bank, right_handle);
		TypeInferSort(bank->sig, right_handle, NULL);
		Eqn_p final = EqnAlloc(left_handle, right_handle, bank, true);
		EqnListAppend(&subst_axiom, final);
	}
	else if (SigIsPredicate(sig, f_code))
	{
		right_handle = bank->true_term;
		assert(left_handle);
		assert(right_handle);
		Eqn_p seq = EqnAlloc(left_handle, right_handle, bank, false);
		EqnListAppend(&subst_axiom, seq);
		
		left_handle = TermDefaultCellAlloc();
		left_handle->arity = arity;
		left_handle->args = TermArgArrayAlloc(arity);
		left_handle->f_code = f_code;
		//left_handle->type = SigGetType(bank->sig, f_code);
		for (int i=0; i<arity; i++)
		{
			left_handle->args[i] = PStackElementP(y_variables, i);
		}
		left_handle->v_count = arity;
		left_handle = TBTermTopInsert(bank, left_handle);
		TypeInferSort(bank->sig, left_handle, NULL);
		Eqn_p final = EqnAlloc(left_handle, right_handle, bank, true);
		EqnListAppend(&subst_axiom, final);
	}
	
	Clause_p subst_axiom_clause = ClauseAlloc(subst_axiom);
	ClauseRecomputeLitCounts(subst_axiom_clause);
	ClauseSetProp(subst_axiom_clause, CPDeleteClause);
	ClauseSetInsert(control->equality_axioms, subst_axiom_clause);
	//printf("Substitution axiom:\n");
	//ClausePrint(GlobalOut, subst_axiom_clause, true);
	//printf("\n");
	PStackFree(x_variables);
	PStackFree(y_variables);
	return subst_axiom_clause;
}

/*  Print the APR graph in DOT format to a file */

long APRGraphCreateDOT(APRControl_p control)
{
	FILE *dotgraph = fopen("/home/hesterj/Projects/APRTESTING/DOT/graph.dot", "w");
	if (dotgraph == NULL)
	{
		printf("# File failure\n");
		return 0;
	}
	else
	{
		printf("# Printing DOT APR graph to ~/Projects/APRTESTING/DOT/graph.dot\n");
	}
	
	fprintf(dotgraph, "digraph aprgraph {\n");
	fprintf(dotgraph, "   graph [splines = true overlap=scale]\n");
	
	for (PStackPointer p=0; p<PStackGetSP(control->graph_nodes); p++)
	{
		APR_p handle = PStackElementP(control->graph_nodes, p);
		Clause_p handle_clause = handle->clause;
		long handle_id = handle->id;
		if (ClauseIsConjecture(handle_clause))
		{
			fprintf(dotgraph,"   %ld [color=Blue]\n", handle_id);
		}
		else if (ClauseQueryProp(handle_clause, CPDeleteClause))
		{
			fprintf(dotgraph,"   %ld [color=Red, shape=box]\n", handle_id);
		}
		for (PStackPointer q=0; q<PStackGetSP(handle->edges); q++)
		{
			APR_p edge = PStackElementP(handle->edges, q);
			long edge_id = edge->id;
			if (edge->type == 1)
			{
				fprintf(dotgraph,"   %ld -> %ld [color=Blue]\n", handle_id, edge_id);
			}
			else
			{
				fprintf(dotgraph,"   %ld -> %ld [color=Green]\n", handle_id, edge_id);
			}
		}
		
	}
	fprintf(dotgraph,"}\n");
	fclose(dotgraph);
	
	return 1;
}

/*  Print an approximation of the graph in DOT format to a file 
 *  Instead of having literals as nodes, clauses are nodes.
 * */

long APRGraphCreateDOTClausesLabeled(APRControl_p control)
{
	FILE *dotgraph = fopen("/home/hesterj/Projects/APRTESTING/DOT/graph.dot", "w");
	printf("# Number of buckets: %ld\n", PStackGetSP(control->buckets));
	if (dotgraph == NULL)
	{
		printf("# File failure\n");
		return 0;
	}
	else
	{
		printf("# Printing DOT APR graph to ~/Projects/APRTESTING/DOT/graph.dot\n");
	}
	
	fprintf(dotgraph, "digraph aprgraph {\n");
	fprintf(dotgraph, "   graph [splines = true overlap=scale]\n");
	
	for (PStackPointer p=0; p<PStackGetSP(control->buckets); p++)
	{
		PStack_p bucket = PStackElementP(control->buckets, p);
		assert(PStackGetSP(bucket) > 0);
		assert(bucket);
		Clause_p handle_clause = APRGetBucketClause(bucket);
		long handle_id = ClauseGetIdent(handle_clause);
		if (ClauseIsConjecture(handle_clause))
		{
			fprintf(dotgraph,"   %ld [color=Green, label=\"", handle_id);
			ClausePrint(dotgraph, handle_clause, true);
			fprintf(dotgraph, "\"]\n");
		}
		else if (ClauseQueryProp(handle_clause, CPDeleteClause))
		{
			fprintf(dotgraph,"   %ld [color=Red, shape=box, label=\"", handle_id);
			ClausePrint(dotgraph, handle_clause, true);
			fprintf(dotgraph, "]\"\n");
		}
		else if (ClauseQueryProp(handle_clause, CPIsProofClause))
		{
			fprintf(dotgraph,"   %ld [color=Yellow, shape=box, label=\"", handle_id);
			ClausePrint(dotgraph, handle_clause, true);
			fprintf(dotgraph, "\"]\n");
		}
		else
		{
			fprintf(dotgraph,"   %ld [label=\"", handle_id);
			ClausePrint(dotgraph, handle_clause, true);
			fprintf(dotgraph, "\"]\n");
		}
		for (PStackPointer q=0; q<PStackGetSP(bucket); q++)
		{
			APR_p node = PStackElementP(bucket, q);
			PStack_p edges = node->edges;
			for (PStackPointer r=0; r<PStackGetSP(edges); r++)
			{
				APR_p edge = PStackElementP(edges, r);
				Clause_p linked_clause = edge->clause;
				if (linked_clause == handle_clause) continue;
				long edge_id = ClauseGetIdent(linked_clause);
				//long edge_id = edge->id;
				if (edge->type == 1)
				{
					fprintf(dotgraph,"   %ld -> %ld [color=Blue, label=\"", handle_id, edge_id);
					EqnTSTPPrint(dotgraph, edge->literal, true);
					fprintf(dotgraph, "\"]\n");
				}
				else
				{
					fprintf(dotgraph,"   %ld -> %ld [color=Green]\n", handle_id, edge_id);
					EqnTSTPPrint(dotgraph, edge->literal, true);
					fprintf(dotgraph, "]\n");
				}
			}
		}
		
	}
	fprintf(dotgraph,"}\n");
	fclose(dotgraph);
	
	return 1;
}

/*  As APRGraphCreateDOTClauses, but does not label the nodes.
 * */

long APRGraphCreateDOTClauses(APRControl_p control)
{
	FILE *dotgraph = fopen("/home/hesterj/Projects/APRTESTING/DOT/graph.dot", "w");
	printf("# Number of buckets: %ld\n", PStackGetSP(control->buckets));
	if (dotgraph == NULL)
	{
		printf("# File failure\n");
		return 0;
	}
	else
	{
		printf("# Printing DOT APR graph to ~/Projects/APRTESTING/DOT/graph.dot\n");
	}
	
	fprintf(dotgraph, "digraph aprgraph {\n");
	fprintf(dotgraph, "   graph [splines = true overlap=scale]\n");
	
	for (PStackPointer p=0; p<PStackGetSP(control->buckets); p++)
	{
		PStack_p bucket = PStackElementP(control->buckets, p);
		assert(PStackGetSP(bucket) > 0);
		assert(bucket);
		Clause_p handle_clause = APRGetBucketClause(bucket);
		long handle_id = ClauseGetIdent(handle_clause);
		if (ClauseIsConjecture(handle_clause))
		{
			fprintf(dotgraph,"   %ld [color=Green]\n", handle_id);
		}
		else if (ClauseQueryProp(handle_clause, CPDeleteClause))
		{
			fprintf(dotgraph,"   %ld [color=Red, shape=box]\n", handle_id);
		}
		else if (ClauseQueryProp(handle_clause, CPIsProofClause))
		{
			fprintf(dotgraph,"   %ld [color=Yellow]\n", handle_id);
		}
		else
		{
			fprintf(dotgraph,"   %ld\n", handle_id);
		}
		for (PStackPointer q=0; q<PStackGetSP(bucket); q++)
		{
			APR_p node = PStackElementP(bucket, q);
			PStack_p edges = node->edges;
			for (PStackPointer r=0; r<PStackGetSP(edges); r++)
			{
				APR_p edge = PStackElementP(edges, r);
				Clause_p linked_clause = edge->clause;
				if (linked_clause == handle_clause) continue;
				long edge_id = ClauseGetIdent(linked_clause);
				//long edge_id = edge->id;
				if (edge->type == 1)
				{
					fprintf(dotgraph,"   %ld -> %ld [color=Blue]\n", handle_id, edge_id);
				}
				else
				{
					fprintf(dotgraph,"   %ld -> %ld [color=Green]\n", handle_id, edge_id);
				}
			}
		}
		
	}
	fprintf(dotgraph,"}\n");
	fclose(dotgraph);
	
	return 1;
}

Clause_p APRGetBucketClause(PStack_p bucket)
{
	assert(PStackGetSP(bucket) > 0);
	APR_p first_node = PStackElementP(bucket, 0);
	assert(first_node);
	Clause_p handle = first_node->clause;
	return handle;
}

int APRCreateInterClauseEdges(APRControl_p control,
										Eqn_p current_literal,
										PStack_p type1stack, 
										PStack_p new_start_nodes,
										PStack_p current_edges,
										PStack_p relevant, 
										PStackPointer t1_iter, 
										int distance)
{
	APR_p visited_node = PStackElementP(type1stack, t1_iter);
	Clause_p visited_node_clause = visited_node->clause;
	int edge_found = 0;
	// Do not search to already visited nodes
	if (visited_node->visited) return 0;
	// Do not attempt to unify with equality axioms at the final step
	if (distance == 0 && visited_node->equality_node) return 0;
	Eqn_p visited_literal = visited_node->literal;
	if (APRComplementarilyUnifiable(current_literal, visited_literal))
	{
		//printf("# Successful unification\n");
		visited_node->visited = true;
		if (control->build_graph)
		{
			PStackPushP(current_edges, visited_node);
		}
		PStackPushP(new_start_nodes, visited_node);
		if (!ClauseQueryProp(visited_node_clause, CPIsAPRRelevant))
		{
			ClauseSetProp(visited_node_clause, CPIsAPRRelevant);
			PStackPushP(relevant, visited_node_clause);
			edge_found = 1;
		}
	}
	return edge_found;
}

/*-----------------------------------------------------------------------
//
// Function: ClauseCopyFresh()
//
//   Create a variable-fresh copy of clause.  Every variable that is 
//   in the clause is replaced with a fresh one.  variable_subst is the address of the 
//   substitution replacing the old variables with new ones.  Must be free'd afterwards!
//
//	John Hester
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

Clause_p ClauseCopyFresh(Clause_p clause, APRControl_p control)
{
   PTree_p variable_tree;
   PStack_p variables;
   PStackPointer p;
   Subst_p subst;
   Term_p old_var, fresh_var;
   Clause_p handle;
   VarBank_p variable_bank;
   
   assert(clause);
   
   variable_bank = clause->literals->bank->vars;
   variables = PStackAlloc();
   variable_tree = NULL;
   subst = SubstAlloc();
   
   ClauseCollectVariables(clause, &variable_tree);
   PTreeToPStack(variables, variable_tree);
   PTreeFree(variable_tree);
   
   for (p = 0; p < PStackGetSP(variables); p++)
   {
	   old_var = PStackElementP(variables, p);
	   control->max_var -= 2;
	   //printf("# %ld\n", control->max_var);
	   fresh_var = VarBankVarAssertAlloc(variable_bank, control->max_var, old_var->type);
	   //assert(fresh_var != old_var);
	   //assert(fresh_var->f_code != old_var->f_code);
	   if (fresh_var->f_code == old_var->f_code)
	   {
			continue;
		}
	   SubstAddBinding(subst, old_var, fresh_var);
   }
   
   handle = ClauseCopy(clause, clause->literals->bank);
   
   SubstDelete(subst);
   PStackFree(variables);

   return handle;
}

/* Test method for creating many subproblems based on relevancy for
 * continuing proof search after a failed attempt.
*/

void APRProofStateProcessTest(ProofState_p proofstate, int relevance, bool equality, bool print_apr_graph)
{
	printf("# Creating APR graph of proofstate\n");
	PList_p conjectures = PListAlloc();
	PList_p non_conjectures = PListAlloc();
	ClauseSetSplitConjectures(proofstate->axioms, 
									  conjectures, 
									  non_conjectures);
	PListFree(non_conjectures);
	APRControl_p control = APRControlAlloc(proofstate->signature, proofstate->terms);
	control->build_graph = true;
	long total_number = ProofStateCardinality(proofstate);
	printf("# U:%ld PR:%ld PE:%ld NU:%ld NNU:%ld Total:%ld\n", proofstate->unprocessed->members,
												proofstate->processed_pos_rules->members,
												proofstate->processed_pos_eqns->members,
												proofstate->processed_neg_units->members,
												proofstate->processed_non_units->members,
												total_number);
	APRGraphAddClausesList(control, conjectures);
	APRGraphAddClauses(control, proofstate->unprocessed ,false);
	APRGraphAddClauses(control, proofstate->processed_pos_rules ,false);
	APRGraphAddClauses(control, proofstate->processed_pos_eqns ,false);
	APRGraphAddClauses(control, proofstate->processed_neg_units ,false);
	APRGraphAddClauses(control, proofstate->processed_non_units ,false);
	printf("# Updating edges of APR graph.  There are %ld nodes.\n", PStackGetSP(control->graph_nodes));
	//APRGraphUpdateEdges(control);
	PStack_p start_nodes = APRCollectNodesFromList(control, conjectures);
	PStack_p relevant_stack = PStackAlloc();
   APRGraphUpdateEdgesFromListStack(control, NULL,
													 start_nodes, 
													 relevant_stack, 
													 10);
	printf("# Printing APR graph. %ld of %ld relevant.\n", PStackGetSP(relevant_stack), total_number);
	APRGraphCreateDOTClausesLabeled(control);
	PStackFree(relevant_stack);
	PStackFree(start_nodes);
	APRControlFree(control);
	PListFree(conjectures);
	printf("# APR finished\n");
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


