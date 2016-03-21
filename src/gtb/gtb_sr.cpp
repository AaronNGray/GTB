/*******************************************************************************
*
* GTB release 2.0 by Adrian Johnstone (A.Johnstone@rhul.ac.uk) 28 September 2000
*
* gtb_sr.c - shift-reduce parser functions
*
* This file may be freely distributed. Please mail improvements to the author.
*
*******************************************************************************/
#include <string.h>
#include "graph.h"
#include "memalloc.h"
#include "textio.h"
#include "gtb.h"
#include "gtb_lex.h"
#include "gtb_gram.h"
#include "gtb_nfa.h"
#include "gtb_dfa.h"
#include "gtb_gdg.h"
#include "gtb_sr.h"
#include "gtb_scr.h"

//#define PARSER_TRACE(string, p1, p2) text_printf(string, p1, p2)
#define PARSER_TRACE(string, p1, p2)

//#define PARSER_TRACE3(string, p1, p2, p3) text_printf(string, p1, p2 ,p3)
#define PARSER_TRACE3(string, p1, p2, p3)

/* #define RESOLVER_TRACE */
//#define LEXER_TRACE
//#define LR_PARSER_TRACE
//#define LR_PARSER_INSTRUMENTATION

void sr_print_action(dfa* this_dfa, int state, int this_symbol, int this_parse_action)
{
  text_printf("State %i, input symbol %i '%s', action %i", state, this_symbol, gram_find_symbol_by_number(this_dfa->nfa->grammar, this_symbol)->id, this_parse_action);
  if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, this_parse_action))
    text_printf(" (S%i)\n", this_parse_action);
  else if (GRAM_IS_SLOT(this_dfa->nfa->grammar, this_parse_action))
  {
    reduction *this_reduction = &this_dfa->reduction_table[this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

    text_printf(" (R[%i] R%i |%i|->%i%s)\n", this_parse_action - this_dfa->nfa->grammar->first_level_0_slot,
                                             this_dfa->reductions_index[this_parse_action - this_dfa->nfa->grammar->first_level_0_slot],
                                             this_reduction->length, this_reduction->symbol_number, this_reduction->is_accepting ? " Accepting" : "");
  }
}

derivation *sr_lr_parse(dfa* this_dfa, char *string)
{
#if defined(LR_PARSER_INSTRUMENTATION)
  int stack_max = 0;
  unsigned shift_count = 0;
  unsigned reduce_count = 0;
#endif
  int *stack = (int *) mem_malloc(2000);
  int *sp = stack;
  int this_symbol;
  derivation *this_derivation = (derivation *) mem_calloc(1, sizeof(derivation));

  text_printf("\n");
  text_message(TEXT_INFO, "LR parse: \'%s\'\n", string);

  lex_init(string, this_dfa->nfa->grammar);
  LEX(this_symbol);

  *++sp = this_dfa->nfa->grammar->first_dfa_state;

  while (1)
  {
    int this_parse_action = dfa_retrieve_first_action(this_dfa, *sp, this_symbol);

    if (this_parse_action == 0)
    {
      text_message(TEXT_INFO, "LR_parse: reject\n");
      mem_free(stack);
      this_derivation->accept = 0;
      return (this_derivation);
    }

  if (script_gtb_verbose())
  {
    int *sp_temp;

    text_printf("\nStack: [%i] ", *(stack + 1));
    for (sp_temp = stack + 2; sp_temp <= sp; sp_temp += 2)
      text_printf("(%i '%s') [%i] ", *sp_temp, gram_find_symbol_by_number(this_dfa->nfa->grammar, *sp_temp)->id, *(sp_temp + 1));

    text_printf("\n");
    sr_print_action(this_dfa, *sp, this_symbol, this_parse_action);
  }

    if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, this_parse_action))       /* Shift */
    {
      *++sp = this_symbol;
      *++sp = this_parse_action;
#if defined(LR_PARSER_INSTRUMENTATION)
      text_printf("**LR stack,shift,+1, %u\n", sp - stack);
      shift_count++;
      if (sp - stack > stack_max)
        stack_max = sp - stack;
#endif
      LEX(this_symbol);
    }                                      /* Reduce */
    else if (GRAM_IS_SLOT(this_dfa->nfa->grammar, this_parse_action))
    {
      reduction *this_reduction = &(this_dfa->reduction_table[this_parse_action - this_dfa->nfa->grammar->first_level_0_slot]);

      if (this_reduction->is_accepting)
      {
        if (this_symbol != GRAM_EOS_SYMBOL_NUMBER)
        {
          text_message(TEXT_INFO, "LR_parse: reject (accepting reduction encountered before end of string)\n");
          mem_free(stack);
          this_derivation->accept = 0;
          return (this_derivation);
        }
        else
        {
          text_message(TEXT_INFO,"LR parse: accept\n");
#if defined(LR_PARSER_INSTRUMENTATION)
          text_printf("**LR accept with %u shifts, and %u reduces: max stack depth %u\n", shift_count, reduce_count, stack_max);
#endif
          this_derivation->accept = 1;
          mem_free(stack);
          return (this_derivation);
				}
      }

      sp -= this_reduction->length * 2;
      int go_to_action = dfa_retrieve_first_action(this_dfa, *sp, this_reduction->symbol_number);
#if defined(LR_PARSER_TRACE)
      text_printf("Goto state %u, goto action %i\n", *sp, go_to_action);
#endif
      *++sp = this_reduction->symbol_number;
      *++sp = go_to_action;
#if defined(LR_PARSER_INSTRUMENTATION)
      text_printf("**LR stack,reduce,=-%i + 1, %u\n",this_reduction->length, sp - stack);
      reduce_count++;
      if (sp - stack > stack_max)
        stack_max = sp - stack;
#endif
    }
    else
      text_message(TEXT_FATAL, "LR parser found a non-standard action in the table\n");
  }
}

/* RNGLR stuff starts here */
static histogram_node *path_length_histogram = NULL;
static histogram_node *reduction_length_histogram = NULL;
static histogram_node *reduction_histogram = NULL;
static int max_queue_depth;

void sr_ssg_statistics(FILE * output_file, void *ssg_trace)
{
  ssg_node *this_node;
  ssg_edge *this_edge;
  FILE *old_text_stream = text_stream();
  unsigned node_count = 0;
  unsigned edge_count = 0;
  unsigned max_level = 0;
  histogram_node *node_visit_histogram = NULL;
  histogram_node *edge_visit_histogram = NULL;

  hist_init(&node_visit_histogram);
  hist_init(&edge_visit_histogram);

  text_redirect(output_file);

  for (this_node = (ssg_node *) graph_next_node(ssg_trace); this_node != NULL; this_node = (ssg_node *) graph_next_node(this_node))
  {
    node_count++;

    if (max_level < this_node->level)
      max_level = this_node->level;

    for (this_edge = (ssg_edge *) graph_next_in_edge(this_node); this_edge != NULL; this_edge = (ssg_edge *) graph_next_in_edge(this_edge))
    {
      edge_count++;

      hist_update(edge_visit_histogram, this_edge->visits);
    }
  }

  text_printf("\nSSG has final level %u with %u node%s and %u edge%s; maximum queue length %i\n",
              max_level,
              node_count - 1, node_count - 1 == 1 ? "" : "s",
              edge_count - 1, edge_count - 1 == 1 ? "" : "s",
              max_queue_depth);

  text_printf("\nEdge visit count histogram\n");
  hist_print(edge_visit_histogram);
  text_printf("Total of %u edge visits\n", hist_weighted_sum_buckets(edge_visit_histogram));

  if (script_gtb_verbose())
  {
    text_printf("\nPath length histogram\n");
    hist_print(path_length_histogram);
    text_printf("Total of %u path entries\n", hist_sum_buckets(path_length_histogram));
    text_printf("Weighted total of %u path entries\n", hist_weighted_sum_buckets(path_length_histogram));

    text_printf("\nReduction length histogram\n");
    hist_print(reduction_length_histogram);
    text_printf("Total of %u reduction length entries\n", hist_sum_buckets(reduction_length_histogram));
    text_printf("Weighted total of %u reduction length entries\n", hist_weighted_sum_buckets(reduction_length_histogram));

    text_printf("\nReduction histogram\n");
    hist_print(reduction_histogram);
    text_printf("Total of %u reduction entries\n", hist_sum_buckets(reduction_histogram));
    text_printf("Weighted total of %u reduction entries\n", hist_weighted_sum_buckets(reduction_histogram));

    hist_free(&node_visit_histogram);
    hist_free(&edge_visit_histogram);
    hist_free(&path_length_histogram);
    hist_free(&reduction_length_histogram);
    hist_free(&reduction_histogram);
  }

  text_redirect(old_text_stream);
}

static derivation *sr_current_render_derivation;

void vcg_print_ssg_graph(const void *graph)
{
  text_printf("orientation:left_to_right dirty_edge_labels:yes ", graph); /* parameter 'graph' is hack to suppress warning message */
}

void vcg_print_ssg_node(const void *node)
{
  ssg_node *this_node = (ssg_node *) node;

  int level = 2+ this_node->level * 2;


  if (GRAM_IS_DFA_STATE(sr_current_render_derivation->dfa->nfa->grammar, (this_node->value)))
  {
    level--;
    text_printf("borderwidth:2 shape:ellipse label:\"%u:%u\"", this_node->value, graph_atom_number(this_node));
  }
  else
    text_printf("borderwidth:2 label:\"%s:%u\"", gram_find_symbol_by_number(sr_current_render_derivation->dfa->nfa->grammar, this_node->value)->id, graph_atom_number(this_node));

  text_printf("level:%u horizontal_order:%u ", level, this_node->value);
}

void vcg_print_ssg_edge(const void *edge)
{
  ssg_edge *this_edge = (ssg_edge *) edge;

  if (this_edge->symbol != 0)
  {
    text_printf("label:\"");
    gram_print_symbol_id(gram_find_symbol_by_number(sr_current_render_derivation->dfa->nfa->grammar, this_edge->symbol));
    text_printf("\"");
  }
}

void sr_write_derivation(FILE * output_file, derivation * this_derivation)
{
  if (this_derivation == NULL)
    return;

  FILE *old_text_stream = text_stream();

  text_redirect(output_file);

  text_printf("Derivation: %s\n", this_derivation->accept ? "true" : "false");

  text_redirect(old_text_stream);
}

void sr_render_derivation(FILE * output_file, derivation * this_derivation)
{
  if (this_derivation == NULL)
    return;

  FILE *old_text_stream = text_stream();

  text_redirect(output_file);
  sr_current_render_derivation = this_derivation;
  graph_vcg(this_derivation->ssg, vcg_print_ssg_graph, vcg_print_ssg_node, vcg_print_ssg_edge);
  text_redirect(old_text_stream);
}

#define REDUCTION_QUEUE_INSERT(edge, count, original_count, symbol, start_node)    \
  { \
    PARSER_TRACE3("Enqueue |%u| %i:%s\n", count, symbol, gram_find_symbol_by_number(this_dfa->nfa->grammar, symbol)->id); \
    reduction_queue_in->active_edge = edge; \
    reduction_queue_in->node_count = count; \
    reduction_queue_in->original_node_count = original_count; \
    reduction_queue_in->reduction_symbol = symbol; \
    reduction_queue_in->source_node = start_node; \
    \
    hist_update(path_length_histogram, count); \
    hist_update(reduction_histogram, original_count); \
    \
    if (++reduction_queue_in == reduction_queue_top)\
      reduction_queue_in = reduction_queue; \
    \
    if (reduction_queue_in == reduction_queue_out)\
      text_message(TEXT_FATAL, "ssg reduction queue overflow: increase value of reduction_queue_length parameter in call to tomita_1_parse or rnglr_parse\n"); \
    \
    if (reduction_queue_in >= reduction_queue_out)\
    { \
      if (max_queue_depth < reduction_queue_in - reduction_queue_out)\
        max_queue_depth = reduction_queue_in - reduction_queue_out; \
    } \
    else \
    { \
      if (max_queue_depth < reduction_queue_length -(reduction_queue_in - reduction_queue_out))\
        max_queue_depth = reduction_queue_length -(reduction_queue_in - reduction_queue_out); \
    } \
  }

#define DFA_STATE_BASE_ZERO(state) (state - this_dfa->nfa->grammar->first_dfa_state)

derivation *sr_tomita_1_parse(dfa * this_dfa, char *string, int nullable_accept_states_present, int reduction_queue_length)
{
  typedef struct reduction_queue_node_struct
  {
    ssg_edge *active_edge;
    unsigned node_count;
    unsigned original_node_count;
    unsigned reduction_symbol;
    ssg_node *source_node;
  } reduction_queue_node;

  reduction_queue_node *reduction_queue;
  reduction_queue_node *reduction_queue_top;
  reduction_queue_node *reduction_queue_in;
  reduction_queue_node *reduction_queue_out;

  ssg_node **active;            /* Set of states to be reduced */
  ssg_node **frontier;          /* Set of states at head of trace */
  ssg_node **shift_to;          /* Set of states to be shifted to */
  int this_element;             /* Element counter for sets */
  int input_symbol;             /* Input symbol from lexer */
  int frontier_nonempty;        /* Nonempty frontier flag to control termination */
  unsigned state_count = this_dfa->state_count;
  unsigned frontier_number = 0; /* frontier counter */
  derivation *this_derivation;  /* derivation structure to hold output of parse */


  /* Stage 1: initialisation */
  /* Initialisation step 1: sign on */
  text_printf("\n");
  text_message(TEXT_INFO, "Tomita 1 parse (queue length %i) %s: \'%s\'\n", reduction_queue_length, nullable_accept_states_present ? "with nullable accepts" : "", string);

  /* Initialisation step 2: create and initialise reduction queue */
  if (reduction_queue_length == 0)
    reduction_queue_length = 4096;

  reduction_queue = (reduction_queue_node*) mem_calloc(reduction_queue_length, sizeof(reduction_queue_node)); /* queue of pending reductions */
  reduction_queue_top = reduction_queue + reduction_queue_length; /* flip point */
  reduction_queue_in = reduction_queue; /* input pointer for (circular) queue */
  reduction_queue_out = reduction_queue;  /* output pointer for (circular) queue */


  /* Initialisation step 3: allocate active, frontier and shift_to sets (actually vectors of pointers to nodes */
  active = (ssg_node * *) mem_calloc(state_count, sizeof(ssg_node *));
  frontier = (ssg_node * *) mem_calloc(state_count, sizeof(ssg_node *));
  shift_to = (ssg_node * *) mem_calloc(state_count, sizeof(ssg_node *));

  /* Initialisation step 4: create derivation structure, create trace graph and root header node */
  this_derivation = (derivation *) mem_calloc(1, sizeof(derivation));
  this_derivation->dfa = this_dfa;
  this_derivation->ssg = graph_insert_graph("ssg trace");
  graph_set_root(this_derivation->ssg, graph_insert_node(sizeof(ssg_node), this_derivation->ssg));

  /* Initialisation step 5: create initial node in trace graph, and load into initial frontier vector */
  frontier[0] = (ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
  frontier[0]->value = this_dfa->nfa->grammar->first_dfa_state;
  frontier[0]->level = frontier_number;

  /* We need an output edge for the start node since we queue edges! */
  graph_insert_edge(sizeof(ssg_edge), graph_root(this_derivation->ssg), frontier[0]);

  /* Initialisation step 6: initialise lexer and load input symbol */
  lex_init(string, this_dfa->nfa->grammar);
  LEX(input_symbol);

  /* Initialisation step 7: initialise path length histogram */
  hist_init(&path_length_histogram);
  hist_init(&reduction_length_histogram);
  hist_init(&reduction_histogram);
  max_queue_depth = -1000;

  int accept_detected;
  int accept_detected_symbol;

  /* Main loop */
  do
  {
    accept_detected = false;

    PARSER_TRACE("\nStarting frontier %u\n", frontier_number, 0);

    /* Stage 2: reductions */
    /* Reduction step 1: iterate over frontier set, removing error entries; looking for reductions and loading them into the queue */
    for (this_element = state_count - 1; this_element >= 0; this_element--)
      if (frontier[this_element] != NULL)
      {
        int *this_parse_action = dfa_retrieve_all_actions(this_dfa, this_element+this_dfa->nfa->grammar->first_dfa_state, input_symbol);

        if (* this_parse_action == 0)
        {
          frontier[this_element] = NULL;  /* remove element from frontier */
          PARSER_TRACE("No actions for state %i\n", this_element + this_dfa->nfa->grammar->first_dfa_state, 0);
        }
        else
        {
          while (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action))  /* skip over any shifts which come first in the table */
            this_parse_action++;

          while (GRAM_IS_SLOT(this_dfa->nfa->grammar, *this_parse_action))
          {
            if (script_gtb_verbose())
              sr_print_action(this_dfa, this_element + this_dfa->nfa->grammar->first_dfa_state, input_symbol, *this_parse_action);

            reduction *this_reduction = &this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];
            unsigned this_reduction_number = this_dfa->reductions_index[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

            if (this_reduction->is_accepting)
            {
              if (script_gtb_verbose())
              {
                PARSER_TRACE("Accepting reduction %u: not queued\n", this_reduction_number, 0);
              }
              this_parse_action++;
            }
            else
            {
              unsigned node_count = this_reduction->length * 2;
              unsigned symbol = this_reduction->symbol_number;

              ssg_node *source_node = frontier[this_element];
              ssg_edge *active_edge;


              for (active_edge = (ssg_edge*) graph_next_out_edge(source_node); active_edge != NULL; active_edge = (ssg_edge*) graph_next_out_edge(active_edge))
              {
                hist_update(reduction_length_histogram, node_count);
                REDUCTION_QUEUE_INSERT(active_edge, node_count, node_count, symbol, source_node);
              }
              this_parse_action++;
            }
          }
        }
      }

    /* Reduction step 2: iterate over queue until it is empty, tracking backwards through all ssg trace paths */
    while (reduction_queue_in != reduction_queue_out)
    {
      int goto_state_is_new;
      unsigned goto_state;
      ssg_node *goto_node;
      int *goto_parse_action;
      unsigned this_node_count = reduction_queue_out->node_count;
      unsigned this_original_node_count = reduction_queue_out->original_node_count;
      unsigned symbol = reduction_queue_out->reduction_symbol;
      ssg_edge *active_edge = reduction_queue_out->active_edge;
      ssg_node *destination_node = (ssg_node *) graph_source(active_edge);  /* In case we count zero edges ! */
      ssg_node *source_node = reduction_queue_out->source_node;
      ssg_edge *new_reduction_edge;
      ssg_node *reduction_symbol_node;

      PARSER_TRACE3("Dequeue |%i| %i:%s. Search:", this_node_count, symbol, gram_find_symbol_by_number(this_dfa->nfa->grammar, symbol)->id);
//      PARSER_TRACE("reduction_queue_in: %p, reduction_queue_out: %p\n", reduction_queue_in, reduction_queue_out);
//      PARSER_TRACE("reduction_queue_length: %i\n", reduction_queue_in - reduction_queue_out, 0);

      /* Increment queue output pointer, testing for wrap-around */
      if (++reduction_queue_out == reduction_queue_top)
        reduction_queue_out = reduction_queue;

      /* Trace backwards through ssg trace graph, queueing branch points */
      while (this_node_count > 0)
      {
        ssg_edge *this_edge;

        this_node_count--;

        destination_node = (ssg_node *) graph_destination(active_edge);
        active_edge->visits++;
        active_edge = (ssg_edge*) graph_next_out_edge(destination_node);
        PARSER_TRACE(" [%i]", destination_node->value, 0);

        /* queue bifurcation edges */
        if (active_edge != NULL)
          for (this_edge = (ssg_edge*) graph_next_out_edge(active_edge); this_edge != NULL; this_edge = (ssg_edge*) graph_next_out_edge(this_edge))
            REDUCTION_QUEUE_INSERT(this_edge, this_node_count, this_original_node_count, symbol, source_node);
      }

      /* Find go-to state and add to frontier if necessary */
      goto_state = *(dfa_retrieve_all_actions(this_dfa, destination_node->value, symbol));
      PARSER_TRACE("\nGoto state %i: ", goto_state, 0);
      goto_node = frontier[goto_state - this_dfa->nfa->grammar->first_dfa_state];
      if (goto_node == NULL)
      {
        PARSER_TRACE("new\n", 0, 0);
        goto_node = (ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
        goto_node->value = goto_state;
        goto_node->level = frontier_number;
        frontier[goto_state - this_dfa->nfa->grammar->first_dfa_state] = goto_node;

        /* Set flag to enable adding zero length (epsilon) reductions to queue */
        goto_state_is_new = 1;
      }
      else
      { /* check to see if there is already a path of length 2 between goto_node and source_node. an assumption here: let's guess that the goto_node has fewer edges leaving it
           than the source_node has entering it. This assumption is based on the idea that the source_node has been in the graph for longer. Therefore, we search from the
           goto_node */

        PARSER_TRACE("old\n", 0, 0);
        void *goto_node_out_edge;

        for (goto_node_out_edge = graph_next_out_edge(goto_node); goto_node_out_edge != NULL; goto_node_out_edge = graph_next_out_edge(goto_node_out_edge))
        {
          ssg_node *symbol_node = (ssg_node *) graph_destination(goto_node_out_edge);
          void *symbol_node_out_edge;

          for (symbol_node_out_edge = graph_next_out_edge(symbol_node); symbol_node_out_edge != NULL; symbol_node_out_edge = graph_next_out_edge(symbol_node_out_edge))
            if (graph_destination(symbol_node_out_edge) == destination_node)
              goto path_found;
        }

        /* Set flag to disable adding zero length (epsilon) reductions to queue */
        goto_state_is_new = 0;
      }

      /* Add reduction symbol node and then connect to goto and destination nodes */
#if 1
/* Old code: puts in symbol nodes */
      reduction_symbol_node = (ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
      reduction_symbol_node->value = symbol;
      if (destination_node->level == goto_node->level)
        reduction_symbol_node->level = destination_node->level;
      else
        reduction_symbol_node->level = goto_node->level - 1;

      graph_insert_edge(sizeof(ssg_edge), destination_node, reduction_symbol_node);
      new_reduction_edge = (ssg_edge*) graph_insert_edge(sizeof(ssg_edge), reduction_symbol_node, goto_node);
#else
      new_reduction_edge = (ssg_edge*) graph_insert_edge(sizeof(ssg_edge), destination_node, goto_node);
#endif

      /* Check to see if there is a further reduction on this edge. If so, queue it */
      goto_parse_action = dfa_retrieve_all_actions(this_dfa, goto_state, input_symbol);

      while (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *goto_parse_action))  // Skip shifts
        goto_parse_action++;

      while (GRAM_IS_SLOT(this_dfa->nfa->grammar, *goto_parse_action))       //Iterate over reductions
      {
        reduction *this_goto_reduction = &(this_dfa->reduction_table[*goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot]);

        if (script_gtb_verbose())
          sr_print_action(this_dfa, goto_state, input_symbol, *goto_parse_action);

        if (this_goto_reduction->is_accepting)
        {
          if (script_gtb_verbose())
          {
            PARSER_TRACE("Skipping accepting reduction\n", 0, 0);
          }
          accept_detected = true;
          accept_detected_symbol = input_symbol;
          goto_parse_action++;
        }
        else
        {
          unsigned node_count = this_goto_reduction->length * 2;
          unsigned symbol = this_goto_reduction->symbol_number;

          /* Liz's tweak */

          if (!(nullable_accept_states_present &&
                goto_node->level == destination_node->level /* goto node was found from a reduction of length 0 */ &&
                node_count != 0)) /* the new reduction is an epsilon reduction too! */
            if (goto_state_is_new || node_count != 0)
            {
              hist_update(reduction_length_histogram, node_count);
              REDUCTION_QUEUE_INSERT(new_reduction_edge, node_count, node_count, symbol, source_node);
            }

          goto_parse_action++;  /* get next action from table */
        }
      }
  path_found:;

    }

    /* Stage 3: shifts */
    /* Shift step 1: clear active and shift-to sets */
    memset(active, 0, sizeof(ssg_node *) * state_count);  /* Clear active aray */
    memset(shift_to, 0, sizeof(ssg_node *) * state_count);  /* Clear shift_to aray */

    /* Shift step 2: iterate over the frontier, collecting shift-to and new active sets.
       When an element is added, create shift-to stub Active element_pointer is set to the shifted-to state Shift_to
       element_pointer is set to the end of the stub */
    for (this_element = 0; this_element < state_count; this_element++)
    {
      if (frontier[this_element] != NULL)
      {
        int *this_parse_action = dfa_retrieve_all_actions(this_dfa, frontier[this_element]->value, input_symbol);

        while (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action))
        {
          if (script_gtb_verbose())
            sr_print_action(this_dfa, this_element + this_dfa->nfa->grammar->first_dfa_state, input_symbol, *this_parse_action);

          ssg_node * * active_element_pointer = & active[*this_parse_action - this_dfa->nfa->grammar->first_dfa_state];
          ssg_node * * shift_to_element_pointer = & shift_to[*this_parse_action - this_dfa->nfa->grammar->first_dfa_state];

          if (* shift_to_element_pointer == NULL)
          {

            * active_element_pointer =(ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
            (* active_element_pointer)->value = *this_parse_action;
            (* active_element_pointer)->level = frontier_number + 1;

            * shift_to_element_pointer =(ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
            (* shift_to_element_pointer)->value = input_symbol;
            (* shift_to_element_pointer)->level = frontier_number;

            graph_insert_edge(sizeof(ssg_edge), * shift_to_element_pointer, * active_element_pointer);
          }
          this_parse_action++;
        }
      }
    }

    /* Shift step 3: iterate over the frontier, connecting shifted nodes to shift-to stubs and copying active list back into frontier */
    for (frontier_nonempty = 0, this_element = 0; this_element < state_count; this_element++)
    {
      if (frontier[this_element] != NULL)
      {
        int *this_parse_action = dfa_retrieve_all_actions(this_dfa, frontier[this_element]->value, input_symbol);

        if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action))
        {
          frontier_nonempty = 1;
          graph_insert_edge(sizeof(ssg_edge), frontier[this_element], shift_to[*this_parse_action - this_dfa->nfa->grammar->first_dfa_state]);
        }
      }
      frontier[this_element] = active[this_element];
    }

    /* Shift step 4: call lexer and increment frontier */
    LEX(input_symbol);
    frontier_number++;
  }
  while (frontier_nonempty);

  if (accept_detected)
  {
    if (accept_detected_symbol == GRAM_EOS_SYMBOL_NUMBER)
      text_message(TEXT_INFO, "Tomita 1 parse: accept\n");
    else
      text_message(TEXT_INFO, "Tomita 1 parse: reject (accepting reduction encountered before end of string)\n");
  }
  else
    text_message(TEXT_INFO, "Tomita 1 parse: reject\n");

  /* Stage 5: dump statistics */
  sr_ssg_statistics(stdout, this_derivation->ssg);

  /* Stage 6: cleanup */
  mem_free(frontier);
  mem_free(active);
  mem_free(shift_to);

  graph_delete_node(graph_root(this_derivation->ssg));
  graph_set_root(this_derivation->ssg, NULL);
  return this_derivation;
}

#if 0
derivation *zz_rnglr_parse(dfa * this_dfa, char *string, int nullable_accept_states_present, int reduction_queue_length)
{
  typedef struct reduction_queue_node_struct
  {
    ssg_edge *active_edge;
    unsigned node_count;
    unsigned original_node_count;
    unsigned reduction_symbol;
    ssg_node *source_node;
  } reduction_queue_node;

  reduction_queue_node *reduction_queue;
  reduction_queue_node *reduction_queue_top;
  reduction_queue_node *reduction_queue_in;
  reduction_queue_node *reduction_queue_out;

  ssg_node **active;            /* Set of states to be reduced */
  ssg_node **frontier;          /* Set of states at head of trace */
  int this_element;             /* Element counter for sets */
  int input_symbol;             /* Input symbol from lexer */
  int frontier_nonempty;        /* Nonempty frontier flag to control termination */
  unsigned state_count = this_dfa->state_count;
  unsigned frontier_number = 1; /* frontier counter */
  derivation *this_derivation;  /* derivation structure to hold output of parse */
  int accept_state_found = 0;


  /* Stage 1: initialisation */
  /* Initialisation step 1: sign on */
  if (reduction_queue_length == 0)
    reduction_queue_length = 4096;

  reduction_queue = (reduction_queue_node*) mem_calloc(reduction_queue_length, sizeof(reduction_queue_node)); /* queue of pending reductions */
  reduction_queue_top = reduction_queue + reduction_queue_length; /* flip point */
  reduction_queue_in = reduction_queue; /* input pointer for (circular) queue */
  reduction_queue_out = reduction_queue;  /* output pointer for (circular) queue */

  text_printf("\nRNGLR parse (queue length %i) %s: \'%s\': accepting reductions {", reduction_queue_length, nullable_accept_states_present ? "with nullable accepts" : "", string);
  set_print_set(nullable_accept_states_present ? &this_dfa->grammar->right_nullable_reductions : &this_dfa->grammar->reductions, NULL, 0);
  text_printf("}\n");

  /* Initialisation step 2: allocate active, frontier and shift_to sets (actually vectors of pointers to nodes */
  active = (ssg_node * *) mem_calloc(state_count, sizeof(ssg_node *));
  frontier = (ssg_node * *) mem_calloc(state_count, sizeof(ssg_node *));

  /* Initialisation step 3: create derivation structure, create trace graph and root header node */
  this_derivation = (derivation *) mem_calloc(1, sizeof(derivation));
  this_derivation->dfa = this_dfa;
  this_derivation->ssg = graph_insert_graph("ssg trace");
  graph_set_root(this_derivation->ssg, graph_insert_node(sizeof(ssg_node), this_derivation->ssg));

  /* Initialisation step 4: create initial node in trace graph, and load into initial frontier vector */
  frontier[0] = (ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
  frontier[0]->value = this_dfa->nfa->grammar->first_dfa_state;
  frontier[0]->level = frontier_number;

  /* We need an output edge for the start node since we queue edges! */
  graph_insert_edge(sizeof(ssg_edge), graph_root(this_derivation->ssg), frontier[0]);

  /* Initialisation step 5: initialise lexer and load input symbol */
  lex_init(string, this_dfa->nfa->grammar);
  LEX(input_symbol);

  /* Initialisation step 6: initialise path length histogram */
  hist_init(&path_length_histogram);
  hist_init(&reduction_length_histogram);
  hist_init(&reduction_histogram);
  max_queue_depth = -1000;

  /* Main loop */
  do
  {
    /* Stage 2: reductions */
    /* Reduction step 1: iterate over frontier set, removing error entries; looking for reductions and loading them into the queue */
    for (this_element = state_count - 1; this_element > 0; this_element--)
      if (frontier[this_element] != NULL)
      {
        int *this_parse_action = dfa_retrieve_all_actions(this_dfa, this_element+this_dfa->nfa->grammar->first_dfa_state, input_symbol);

        if (* this_parse_action == 0)
        {
          frontier[this_element] = NULL;  /* remove element from frontier */
          PARSER_TRACE("No actions for state %i\n", this_element + this_dfa->nfa->grammar->first_dfa_state, 0);
        }
        else
        {
          while (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action))  /* skip over any shifts which come first in the table */
          {
            this_parse_action++;
            PARSER_TRACE("Skipping shift actions for element %u\n", this_element, 0);
          }

          while (GRAM_IS_SLOT(this_dfa->nfa->grammar, *this_parse_action))
          {
            if (script_gtb_verbose())
              sr_print_action(this_dfa, this_element + this_dfa->nfa->grammar->first_dfa_state, input_symbol, *this_parse_action);

            reduction *this_reduction = &this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];
            unsigned this_reduction_number = this_dfa->reductions_index[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

            if (this_reduction->is_accepting)
            {
              PARSER_TRACE("Accepting reduction %u found\n", graph_atom_number(this_parse_table->reduction_table_elements[*this_parse_action].slot), 0);
              this_parse_action++;
            }
            else
            {
              unsigned node_count = this_reduction->length;
              unsigned symbol = this_reduction->symbol_number;

              ssg_node *source_node = frontier[this_element];
              ssg_edge *active_edge;

              for (active_edge = (ssg_edge*) graph_next_out_edge(source_node); active_edge != NULL; active_edge = (ssg_edge*) graph_next_out_edge(active_edge))
              {
                hist_update(reduction_length_histogram, node_count);
                REDUCTION_QUEUE_INSERT(active_edge, node_count, node_count, symbol, source_node);
              }
              this_parse_action++;
            }
          }
        }
      }

    /* Reduction step 2: iterate over queue until it is empty, tracking backwards through all ssg trace paths */
    while (reduction_queue_in != reduction_queue_out)
    {
      int goto_state_is_new;
      unsigned goto_state;
      ssg_node *goto_node;
      int *goto_parse_action;
      unsigned this_node_count = reduction_queue_out->node_count;
      unsigned this_original_node_count = reduction_queue_out->original_node_count;
      unsigned symbol = reduction_queue_out->reduction_symbol;
      ssg_edge *active_edge = reduction_queue_out->active_edge;
      ssg_node *destination_node = (ssg_node *) graph_source(active_edge);  /* In case we count zero edges ! */
      ssg_node *source_node = reduction_queue_out->source_node;
      ssg_edge *new_reduction_edge;

      PARSER_TRACE3("Dequeue |%i| %i:%s. Search:", this_node_count, symbol, gram_find_symbol_by_number(this_dfa->nfa->grammar, symbol)->id);

      /* Increment queue output pointer, testing for wrap-around */
      if (++reduction_queue_out == reduction_queue_top)
        reduction_queue_out = reduction_queue;

      /* Trace backwards through ssg trace graph, queueing branch points */
      while (this_node_count > 0)
      {
        ssg_edge *this_edge;

        this_node_count--;

        destination_node = (ssg_node *) graph_destination(active_edge);
        if (graph_source(active_edge) != source_node)  /* Don't count initial edges to match Rob's statistics */
        {
          active_edge->visits++;
          destination_node->visits++;
        }
        active_edge = (ssg_edge*) graph_next_out_edge(destination_node);
        PARSER_TRACE(" [%i]", destination_node->value, 0);

        /* queue bifurcation edges */
        if (active_edge != NULL)
          for (this_edge = (ssg_edge*) graph_next_out_edge(active_edge); this_edge != NULL; this_edge = (ssg_edge*) graph_next_out_edge(this_edge))
            REDUCTION_QUEUE_INSERT(this_edge, this_node_count, this_original_node_count, symbol, source_node);
      }

      PARSER_TRACE("Processing reduce with destination node %u\n", destination_node->value, 0);

      /* Find go-to state and add to frontier if necessary */
      goto_state = *(dfa_retrieve_all_actions(this_dfa, destination_node->value, symbol));
      PARSER_TRACE("\nGoto state %i: ", goto_state, 0);
      goto_node = frontier[goto_state - this_dfa->nfa->grammar->first_dfa_state];
      if (goto_node == NULL)
      {
        PARSER_TRACE("new\n", 0, 0);
        goto_node = (ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
        goto_node->value = goto_state;
        goto_node->level = frontier_number;
        frontier[goto_state - this_dfa->nfa->grammar->first_dfa_state] = goto_node;

        /* Set flag to enable adding zero length (epsilon) reductions to queue */
        goto_state_is_new = 1;
      }
      else
      {  /* check to see if there is already a path of length 2 between goto_node and source_node. an assumption here: let's guess that the goto_node has fewer edges leaving it
           than the source_node has entering it. This assumption is based on the idea that the source_node has been in the graph for longer. Therefore, we search from the
           goto_node */

        PARSER_TRACE("old\n", 0, 0);

        void *goto_node_out_edge;

/??? Error here: restore old function
        for (goto_node_out_edge = graph_next_out_edge(goto_node); goto_node_out_edge != NULL; goto_node_out_edge = graph_next_out_edge(goto_node_out_edge))
        {
          ssg_node *symbol_node = (ssg_node *) graph_destination(goto_node_out_edge);
          void *symbol_node_out_edge;

          for (symbol_node_out_edge = graph_next_out_edge(symbol_node); symbol_node_out_edge != NULL; symbol_node_out_edge = graph_next_out_edge(symbol_node_out_edge))
            if (graph_destination(symbol_node_out_edge) == destination_node)
              goto path_found;
        }

        /* Set flag to disable adding zero length (epsilon) reductions to queue */
        goto_state_is_new = 0;
      }

      /* Add reduction symbol node and then connect to goto and destination nodes */
      new_reduction_edge = (ssg_edge*) graph_insert_edge(sizeof(ssg_edge), destination_node, goto_node);
      new_reduction_edge->symbol = symbol;

      /* Check to see if there is a further reduction on this edge. If so, queue it */
      goto_parse_action = RETRIEVE_PARSE_TABLE_ELEMENT(this_parse_table, goto_state, input_symbol);

      while (*goto_parse_action < 0)
        goto_parse_action++;

      while (*goto_parse_action > 0)
        if (set_includes_element(&this_parse_table->accepting_reductions, graph_atom_number(this_parse_table->reduction_table_elements[*goto_parse_action].slot)))
        {
          PARSER_TRACE("Accepting reduction %u found\n", graph_atom_number(this_parse_table->reduction_table_elements[*goto_parse_action].slot), 0);
          goto_parse_action++;
        }
        else
        {
          reduction_table_element *this_reduction_table_element = &(this_parse_table->reduction_table_elements[*goto_parse_action]);
          unsigned node_count = this_reduction_table_element->length;
          unsigned symbol = this_reduction_table_element->symbol->symbol_number;

          /* Liz's tweak */
          PARSER_TRACE("Queuing reduction %u\n", graph_atom_number(this_parse_table->reduction_table_elements[*goto_parse_action].slot), 0);
          if (!(nullable_accept_states_present &&
                goto_node->level == destination_node->level /* goto node was found from a reduction of length 0 */ &&
                node_count != 0)) /* the new reduction is an epsilon reduction too! */
            if (goto_state_is_new || node_count != 0)
            {
              hist_update(reduction_length_histogram, node_count);
              REDUCTION_QUEUE_INSERT(new_reduction_edge, node_count, node_count, symbol, goto_node); /* ! */
            }

          goto_parse_action++;  /* get next action from table */
        }
  path_found:;

    }

    /* Stage 3: shifts */

    /* Shift step 1: clear active and shift-to sets */
    memset(active, 0, sizeof(ssg_node *) * state_count);  /* Clear active aray */

    /* Shift step 2: iterate over the frontier connecting to next frontier held in active */
    for (frontier_nonempty = 0, this_element = 1; this_element < state_count; this_element++)
    {
      if (frontier[this_element] != NULL)
      {
        int *this_parse_action = RETRIEVE_PARSE_TABLE_ELEMENT(this_parse_table, frontier[this_element]->value, input_symbol);

        while (*this_parse_action < 0)
        {
          ssg_node * * active_element_pointer = & active[- *this_parse_action];

          if (* active_element_pointer == NULL)
          {
            PARSER_TRACE("Adding shift_to node for S%i from state %i\n", -*this_parse_action, this_element);

            frontier_nonempty = 1;

            * active_element_pointer =(ssg_node *) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
            (* active_element_pointer)->value = - *this_parse_action;
            (* active_element_pointer)->kind = ssg_state_node;
            (* active_element_pointer)->level = frontier_number + 2;
          }

          ((ssg_edge*) graph_insert_edge(sizeof(ssg_edge), frontier[this_element], * active_element_pointer))->symbol = input_symbol;

          this_parse_action++;
        }
      }
    }

    if (frontier_nonempty)
    {
      /* Shift step 3: iterate over the frontier copying active list back into frontier */
      for (this_element = 1; this_element < state_count; this_element++)
        frontier[this_element] = active[this_element];

      /* Shift step 4: call lexer and increment frontier */
      PARSER_TRACE("Finished frontier number %u\n", frontier_number, 0);
      ssg_LEX(input_symbol);
      frontier_number += 2;
    }
  }
  while (frontier_nonempty);

  /* Stage 5: check for acceptance */
  PARSER_TRACE("Checking for acceptance on final symbol %u\n", input_symbol, 0);

  if (input_symbol != GRAM_EOS_SYMBOL_NUMBER)
  {
    PARSER_TRACE("Not at EOS\n", 0, 0);
  }
  else
  {
    for (this_element = 1; this_element < state_count; this_element++)
    {
      int *this_parse_action;

      this_parse_action = RETRIEVE_PARSE_TABLE_ELEMENT(this_parse_table, this_element, input_symbol);

      while (*this_parse_action > 0)
      {
        if (set_includes_element(&this_parse_table->accepting_reductions, graph_atom_number(this_parse_table->reduction_table_elements[*this_parse_action].slot)))
        {
          accept_state_found = 1;
          PARSER_TRACE("Acceptance check passes on reduction %u found in state %u\n", graph_atom_number(this_parse_table->reduction_table_elements[*this_parse_action].slot), this_element);
        }
        this_parse_action++;
      }
    }
  }

  if (accept_state_found) text_printf("Accept\n"); else text_printf("Reject\n");

  /* Stage 6: dump statistics */
  sr_ssg_statistics(stdout, this_derivation->ssg);

  /* Stage 7: cleanup */
  mem_free(frontier);
  mem_free(active);

  return this_derivation;
}
#endif
