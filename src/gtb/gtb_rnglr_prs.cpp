/*******************************************************************************
*
* GTB release 2.0 by Adrian Johnstone (A.Johnstone@rhul.ac.uk) 28 September 2000
*
* gtb_rnglr_prs.cpp - an RNGLR parser, as per the TOPLAS paper
*
* This file may be freely distributed. Please mail improvements to the author.
*
*******************************************************************************/
#include <string.h>
#include "graph.h"
#include "memalloc.h"
#include "hist.h"
#include "textio.h"
#include "gtb.h"
#include "gtb_lex.h"
#include "gtb_gram.h"
#include "gtb_nfa.h"
#include "gtb_dfa.h"
#include "gtb_gdg.h"
#include "gtb_sr.h"
#include "gtb_scr.h"
#include "gtb_rnglr_rec.h"

/* 8 July 2006: created by splitting off this code from gtb_sr.cpp */
/* 8 July 2006: added edge histogram code to check behaviour of Chi set traversal algorithm */
//#define RNGLR_EPSILON_TRACE
//#define RNGLR_RECOGNISER_TRACE
//#define CHI_HIST

#if defined(CHI_HIST)
static histogram_node *chi_edge_histogram = NULL;
static histogram_node *chi_node_histogram = NULL;
static histogram_node *chi_prime_edge_histogram = NULL;
static histogram_node *chi_prime_node_histogram = NULL;
#endif

static derivation *vcg_sppf_render_derivation = NULL;
static void  vcg_print_sppf_node(const void *node)
{
  sppf_node *this_node = (sppf_node*) node;

  if (GRAM_IS_NONTERMINAL(vcg_sppf_render_derivation->dfa->nfa->grammar, this_node->x) || this_node->x == GRAM_EPSILON_SYMBOL_NUMBER)
  {
    text_printf("label:\"");
    gram_print_symbol_id(gram_find_symbol_by_number(vcg_sppf_render_derivation->dfa->nfa->grammar, this_node->x));
    text_printf(" %i:%i\"",this_node->j, this_node->i);
  }
  else
    text_printf("shrink:2 shape:circle label:\"\"");
}

static void  vcg_epsilon_sppf_print_index(const void *graph)
{
  for (int i = 0; i < vcg_sppf_render_derivation->dfa->nfa->grammar->first_dfa_state; i++)
  {
    if (vcg_sppf_render_derivation->epsilon_sppf_index[i] != NULL)
    {
      text_printf("node:{title:\"i%i\" bordercolor:red", i);
      text_printf("label:\"");

      if (i == 0)
        text_printf("#");
      else if (GRAM_IS_SLOT(vcg_sppf_render_derivation->dfa->nfa->grammar, i))
        gram_print_slot_by_number(vcg_sppf_render_derivation->dfa->nfa->grammar, i, 1);
      else
        gram_print_symbol_id(vcg_sppf_render_derivation->dfa->nfa->grammar->symbol_index[i]);

      text_printf("\"}\n");
      text_printf("edge:{sourcename:\"i%i\" targetname:\"%i\" color:red}\n", i, graph_atom_number(vcg_sppf_render_derivation->epsilon_sppf_index[i]));
    }
  }
}

struct epsilon_sppf_table_data {
unsigned *id;
struct sppf_node_struct *sppf_node;
};

sppf_node * epsilon_sppf_add_slot_suffix(derivation *this_derivation, unsigned *this_slot, void *epsilon_sppf_table, sppf_node *base_node, int suppress_ultimate_penultimate)
{
  unsigned *suffix = gram_slot_suffix_by_number(this_derivation->dfa->nfa->grammar, *this_slot);

#if defined RNGLR_EPSILON_TRACE
  text_printf("Slot suffix for slot %u", *this_slot);
  gram_print_slot_suffix(this_derivation->dfa->nfa->grammar, suffix);
  text_printf("\n");
#endif

  gram_edge *out_edge = (gram_edge*) graph_next_out_edge(graph_node_index(this_derivation->dfa->nfa->grammar->rules)[*this_slot]);
  gram_edge *out_out_edge = NULL;
  if (out_edge != NULL)
    out_out_edge = (gram_edge*) graph_next_out_edge(graph_destination(out_edge));

  if (suppress_ultimate_penultimate && (out_edge == NULL || out_out_edge == NULL))
  {
#if defined RNGLR_EPSILON_TRACE
    text_printf("Slot is penultimate or ultimate in production: skipping\n");
#endif
    return NULL;
  }

  /* Put the slot suffix into the symbol table, and create the epsilon-SPPF node and its immediate children */
  epsilon_sppf_table_data *this_symbol;

  if (base_node != NULL)
  {
    this_symbol = (epsilon_sppf_table_data*) symbol_insert_key(epsilon_sppf_table, &suffix, sizeof(unsigned*), sizeof(epsilon_sppf_table_data));
    this_symbol->sppf_node = NULL;
  }
  else
  {
    this_symbol = (epsilon_sppf_table_data*) symbol_find(epsilon_sppf_table, &suffix, sizeof(unsigned*), sizeof(epsilon_sppf_table_data), NULL, SYMBOL_ANY);
    this_symbol->sppf_node = NULL;
  }

  if (this_symbol->sppf_node == NULL)
  {
#if defined RNGLR_EPSILON_TRACE
    text_printf("New suffix: creating epsilon-SPPF node\n");
#endif

    if (base_node != NULL)
      this_symbol->sppf_node = base_node;
    else
      this_symbol->sppf_node = (sppf_node*) graph_insert_node(sizeof(sppf_node), this_derivation->epsilon_sppf);

    if (*suffix == 0)
        graph_insert_edge(0,
                          this_derivation->epsilon_sppf_index[0],
                          this_symbol->sppf_node);
    else
      for (int count = 1; count <= *suffix; count++)
        graph_insert_edge(0, this_derivation->epsilon_sppf_index[suffix[count]], this_symbol->sppf_node);
  }
  else
    mem_free(suffix);

  this_derivation->epsilon_sppf_index[*this_slot] = this_symbol->sppf_node;

  return this_symbol->sppf_node;
}

static void create_epsilon_sppf(derivation* this_derivation)
{
  this_derivation->epsilon_sppf = graph_insert_graph("Epsilon SPPF");
  this_derivation->epsilon_sppf_index = (sppf_node**) mem_calloc(this_derivation->dfa->nfa->grammar->first_dfa_state, sizeof(sppf_node*));

  void *epsilon_sppf_table = epsilon_sppf_table = symbol_new_table("Epsilon SPPF entries", 101, 31,
                                                                  symbol_compare_pointer_to_counted_unsigned,
                                                                  symbol_hash_pointer_to_counted_unsigned,
                                                                  symbol_print_pointer_to_counted_unsigned);

  this_derivation->epsilon_sppf_index[0] = (sppf_node*) graph_insert_node(sizeof(sppf_node), this_derivation->epsilon_sppf);
  this_derivation->epsilon_sppf_index[0]->x = GRAM_EPSILON_SYMBOL_NUMBER;

  unsigned *nullable_reduction_numbers = set_array(&this_derivation->dfa->nfa->grammar->right_nullable_reductions);

  /* First create epsilon-sppf nodes for nonterminals by looking for leader reductions (i.e. accepting level 1 slots */
  for (unsigned *this_nullable_reduction_number = nullable_reduction_numbers;
       *this_nullable_reduction_number != SET_END;
       this_nullable_reduction_number++)
  {
    if (*this_nullable_reduction_number < this_derivation->dfa->nfa->grammar->first_level_2_slot)   /* make a node for the RHS */
    {
      int this_nonterminal_number = ((gram_node*) graph_source(graph_next_in_edge((gram_node*) graph_node_index(this_derivation->dfa->nfa->grammar->rules)[*this_nullable_reduction_number])))->symbol_table_entry->symbol_number;

      if (this_derivation->epsilon_sppf_index[this_nonterminal_number] == NULL)
      {
        this_derivation->epsilon_sppf_index[this_nonterminal_number] = (sppf_node*) graph_insert_node(sizeof(sppf_node), this_derivation->epsilon_sppf);
        this_derivation->epsilon_sppf_index[this_nonterminal_number]->x = this_nonterminal_number;
      }
    }
  }

  /* Now create symbol table entries for the leader reductions (i.e. accepting level 1 slots */
  for (unsigned *this_nullable_reduction_number = nullable_reduction_numbers;
       *this_nullable_reduction_number != SET_END;
       this_nullable_reduction_number++)
  {
    if (*this_nullable_reduction_number < this_derivation->dfa->nfa->grammar->first_level_2_slot)
    {
      gram_node *lhs_node = (gram_node*) graph_source(graph_next_in_edge(graph_node_index(this_derivation->dfa->nfa->grammar->rules)[*this_nullable_reduction_number]));


      /* Now test to see if we have exactly one nullable production */
      int nullable_productions = 0;

      for (gram_edge* this_edge = (gram_edge*) graph_next_out_edge(lhs_node); this_edge != NULL; this_edge = (gram_edge*) graph_next_out_edge(this_edge))
        if (set_includes_element(&this_derivation->dfa->nfa->grammar->right_nullable_reductions, graph_atom_number(graph_destination(this_edge))))
          nullable_productions++;

      if (script_gtb_verbose())
        text_printf("Nonterminal %s has %i nullable productions\n", lhs_node->symbol_table_entry->id, nullable_productions);

      // I'm a leader, so find my LHS and then add a suffix for each RHS
      if (nullable_productions == 1)
        epsilon_sppf_add_slot_suffix(this_derivation, this_nullable_reduction_number, epsilon_sppf_table, this_derivation->epsilon_sppf_index[lhs_node->symbol_table_entry->symbol_number], 0);
      else
      {
        graph_insert_edge(0,
                          epsilon_sppf_add_slot_suffix(this_derivation, this_nullable_reduction_number, epsilon_sppf_table, NULL, 0),
                          this_derivation->epsilon_sppf_index[lhs_node->symbol_table_entry->symbol_number]);
      }
    }
  }

  /* Now do the required right parts */
  for (unsigned *this_nullable_reduction_number = nullable_reduction_numbers;
       *this_nullable_reduction_number != SET_END;
       this_nullable_reduction_number++)
    if (*this_nullable_reduction_number >= this_derivation->dfa->nfa->grammar->first_level_2_slot)
      epsilon_sppf_add_slot_suffix(this_derivation, this_nullable_reduction_number, epsilon_sppf_table, NULL, 1);

  mem_free(nullable_reduction_numbers);
}

/* poor man's generator: use a stack to explore part of the SGG, returning an element of Chi on each iteration */
ssg_edge **reduction_search_stack, **reduction_search_stack_pointer, **reduction_search_stack_limit;

/* Global variable that holds the next member of Chi */
static ssg_node* reduction_search_target_node;

/* Initialise the search stack */
static void reduction_search_generate_init(dfa* this_dfa)
{
  reduction_search_stack = (ssg_edge**) mem_calloc(this_dfa->nfa->grammar->maximum_rule_length, sizeof (ssg_edge*) );
}

/* Return search stack space to heap */
static void reduction_search_generate_cleanup(void)
{
  mem_free(reduction_search_stack);
}

/* Find the first search target, stacking side branches as we go */
static void reduction_search_generate_start(ssg_node* this_node, int length)
{
  reduction_search_target_node = this_node;
  reduction_search_stack_pointer = reduction_search_stack;
  reduction_search_stack_limit = reduction_search_stack + length;

#if defined(RNGLR_RECOGNISER_TRACE)
  text_printf("Search generate start: node (%i,L%i) length %i\n", this_node->value, this_node->level, length);
#endif

#if defined(CHI_HIST)
  hist_update(chi_node_histogram, graph_atom_number(reduction_search_target_node));
#endif

  while (reduction_search_stack_pointer < reduction_search_stack_limit)
  {
    ssg_edge * this_edge = (ssg_edge*) graph_next_out_edge(reduction_search_target_node);
#if defined(CHI_HIST)
    hist_update(chi_edge_histogram, graph_atom_number(this_edge));
#endif

    *reduction_search_stack_pointer = this_edge;

#if defined(RNGLR_RECOGNISER_TRACE)
    text_printf("Search generate start: stacked in-edge to state (%u,L%i)\n",
                ((ssg_node*) graph_destination(*reduction_search_stack_pointer))->value,
                ((ssg_node*) graph_destination(*reduction_search_stack_pointer))->level);
#endif
    reduction_search_stack_pointer++;

    reduction_search_target_node = (ssg_node*) graph_destination(this_edge);
#if defined(CHI_HIST)
    hist_update(chi_node_histogram, graph_atom_number(reduction_search_target_node));
#endif
  }
#if defined(RNGLR_RECOGNISER_TRACE)
  text_printf("Search generate start: target is (%i,L%i)\n", reduction_search_target_node->value, reduction_search_target_node->level);
#endif
}

static void reduction_search_generate_next_target(void)
{
#if defined(RNGLR_RECOGNISER_TRACE)
      text_printf("Search generate next: stack base %p, stack pointer %p, offset %i\n",
                  reduction_search_stack, reduction_search_stack_pointer, reduction_search_stack_pointer - reduction_search_stack
                 );
#endif
  if (reduction_search_stack_pointer == reduction_search_stack)
    reduction_search_target_node = NULL;
  else
  {
    /* unstack until we find an edge with a sibling */
    ssg_edge *sibling_edge;

    while (reduction_search_stack_pointer > reduction_search_stack && (sibling_edge = (ssg_edge*) graph_next_out_edge(*--reduction_search_stack_pointer)) == NULL)
    {
      #if defined(RNGLR_RECOGNISER_TRACE)
      text_printf("Search generate next: unstacked in-edge %u to state (%u,L%i)\n",
                  graph_atom_number(*reduction_search_stack_pointer),
                  ((ssg_node*) graph_destination(*reduction_search_stack_pointer))->value,
                  ((ssg_node*) graph_destination(*reduction_search_stack_pointer))->level);
      #endif
    }

#if defined(RNGLR_RECOGNISER_TRACE)
    text_printf("Search generate next: after unstacking: stack base %p, stack pointer %p, offset %i, sibling edge %u to state (%u,L%i)\n",
                reduction_search_stack, reduction_search_stack_pointer, reduction_search_stack_pointer - reduction_search_stack,
                graph_atom_number(sibling_edge),
                reduction_search_target_node->value,
                reduction_search_target_node->level
               );
#endif
    if (sibling_edge == NULL)
      reduction_search_target_node = NULL;
    else
    {
      //Push new edge onto stack
      *reduction_search_stack_pointer = sibling_edge;
      reduction_search_stack_pointer++;

      reduction_search_target_node = (ssg_node*) graph_destination(sibling_edge);

#if defined(RNGLR_RECOGNISER_TRACE)
      text_printf("Search generate next: stacking sibling edge %u to state (%u,L%i)\n",
                  graph_atom_number(sibling_edge),
                  reduction_search_target_node->value,
                  reduction_search_target_node->level);
#endif

      #if defined(CHI_HIST)
      hist_update(chi_edge_histogram, graph_atom_number(sibling_edge));
      #endif


      #if defined(CHI_HIST)
      hist_update(chi_node_histogram, graph_atom_number(reduction_search_target_node));
      #endif

      /* Now continue down new branch */
      while (reduction_search_stack_pointer < reduction_search_stack_limit)
      {
        ssg_edge * this_edge = (ssg_edge*) graph_next_out_edge(reduction_search_target_node);

        #if defined(CHI_HIST)
        hist_update(chi_edge_histogram, graph_atom_number(this_edge));
        #endif

        *reduction_search_stack_pointer = this_edge;

        #if defined(RNGLR_RECOGNISER_TRACE)
        text_printf("Search generate start: stacked in-edge to state (%u,L%i)\n",
                    ((ssg_node*) graph_destination(*reduction_search_stack_pointer))->value,
                    ((ssg_node*) graph_destination(*reduction_search_stack_pointer))->level);
        #endif
        reduction_search_stack_pointer++;

        reduction_search_target_node = (ssg_node*) graph_destination(this_edge);
        #if defined(CHI_HIST)
        hist_update(chi_node_histogram, graph_atom_number(reduction_search_target_node));
        #endif
      }
    }
  }

  #if defined(RNGLR_RECOGNISER_TRACE)
  if (reduction_search_target_node == NULL)
    text_printf("Search generate next: target is NULL\n");
  else
    text_printf("Search generate next: target is %i\n", reduction_search_target_node->value);
#endif
}

static void reduction_search_rec(ssg_node *node, int depth)
{
#if defined(CHI_HIST)
  hist_update(chi_prime_node_histogram, graph_atom_number(node));
#endif

  if (depth <= 0)
    return;

  for (ssg_edge *this_edge = (ssg_edge*) graph_next_out_edge(node); this_edge != NULL; this_edge = (ssg_edge*) graph_next_out_edge(this_edge))
  {
#if defined(CHI_HIST)
    hist_update(chi_prime_edge_histogram, graph_atom_number(this_edge));
#endif
    reduction_search_rec((ssg_node*) graph_destination(this_edge), depth - 1);
  }
}

derivation *sr_rnglr_parse(dfa * this_dfa, char *string, int reduction_stack_size)
{
  struct reduction_stack_element{
    ssg_node *node;                     /* u in paper */
    reduction* reduction_table_entry;   /* indirectly, X and m in paper */
  } *reduction_stack, *reduction_stack_pointer;

  struct shift_stack_element {
    ssg_node *current_frontier_node;    /* v in paper */
    int next_frontier_node_number;      /* label[w] in paper */
  } *shift_stack, *shift_stack_prime, *shift_stack_pointer, *shift_stack_prime_pointer, *shift_stack_exchanger;

  derivation *this_derivation;          /* derivation structure to hold output of parse */
  ssg_node **current_frontier;          /* U_k the current frontier */
  ssg_node **next_frontier;             /* U_k+1 the next frontier created via shoft actions */
  ssg_node **frontier_exchanger;        /* dummy frontier pointer used when swapping over frontiers */

  /* Initialisation step 1: sign on */
  text_printf("\n");
  text_message(TEXT_INFO, "RNGLR parse: \'%s\'\n", string);

  /* Initialisation step 2: create derivation structure and SSG structure */
  this_derivation = (derivation *) mem_calloc(1, sizeof(derivation));
  this_derivation->dfa = this_dfa;
  this_derivation->ssg = graph_insert_graph("ssg trace");
  create_epsilon_sppf(this_derivation);
  FILE *epsilon_sppf_vcg_file = fopen("esppf.vcg", "w");
  text_redirect(epsilon_sppf_vcg_file);
  vcg_sppf_render_derivation = this_derivation;
  graph_vcg(this_derivation->epsilon_sppf, vcg_epsilon_sppf_print_index, vcg_print_sppf_node, NULL);
  text_redirect(stdout);

  /* Initialisation step 3: create the frontiers */
  current_frontier = (ssg_node**) mem_calloc(sizeof(ssg_node*), this_dfa->state_count);
  next_frontier = (ssg_node**) mem_calloc(sizeof(ssg_node*), this_dfa->state_count);
  int first_dfa_state = this_dfa->nfa->grammar->first_dfa_state;

  /* Initialisation step 4: create and initialise reduction (R) and shift (Q) sets as stacks */
  reduction_stack = (reduction_stack_element*) mem_calloc(reduction_stack_size == 0 ? 4096 : reduction_stack_size, sizeof (reduction_stack_element));
  shift_stack = (shift_stack_element*) mem_calloc(this_dfa->state_count, sizeof(shift_stack_element));
  shift_stack_prime = (shift_stack_element*) mem_calloc(this_dfa->state_count, sizeof(shift_stack_element));
  reduction_search_generate_init(this_dfa);

  /* Initialisation step 5: initialise lexer and load input symbol array */
  int d = strlen(string);
  int *a = (int*) mem_malloc((d+2) * sizeof(unsigned));  /* we don't use a[0], and we need an a[d+1] for $, hence length is d+2 */

  lex_init(string, this_dfa->nfa->grammar);

  for (int i = 1; i <= d; i++)
    LEX(a[i]);

  /* Main algorithm, as per pages 20-21 of the TOPLAS paper */
  if (d == 0)  /* On empty string, see is acc is a member of T(0,$) by checking all reductions and setting this_derivation->accept */
  {
#if defined(RNGLR_RECOGNISER_TRACE)
    text_printf("Empty string\n");
#endif
    int *these_parse_actions = dfa_retrieve_all_actions(this_dfa, this_dfa->nfa->grammar->first_dfa_state, GRAM_EOS_SYMBOL_NUMBER);  /* Get T(0, $) */
    int *this_parse_action = these_parse_actions;

    if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action)) /* If this first action is a shift, then skip it */
      this_parse_action++;

    for (;*this_parse_action != 0; this_parse_action++)                /* Walk the rest of the actions in T(0, $) looking for accepts */
      if (this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot].is_accepting)
        this_derivation->accept = 1;
  }
  else /* Non-empty string */
  {
    ssg_node *v0 = (ssg_node*) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);  /* Create a node v_0... */
    v0->value = this_dfa->nfa->grammar->first_dfa_state;         /* labelled with the start state of the DFA */
    v0->level = 0;
    current_frontier[0] = v0;                                    /* U_0 = { v_0 } */
    reduction_stack_pointer = reduction_stack;                   /* R = { } */
    shift_stack_pointer = shift_stack;                           /* S = { } */
    a[d+1] = GRAM_EOS_SYMBOL_NUMBER;
    /* NB out current frontier and next frontier arrays represent U_k and U_k+1 at any point: we can't initislise the U_i's to empty because they don't exist */

    int *these_parse_actions = dfa_retrieve_all_actions(this_dfa, this_dfa->nfa->grammar->first_dfa_state, a[1]);  /* Get T(0, a_1) */
    int *this_parse_action = these_parse_actions;                /* If there is a shift, it will be first */

    if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action)) /* If this first action is a shift, then push (label(v0), k) into Q set */
    {
      shift_stack_pointer->current_frontier_node = v0;
      shift_stack_pointer->next_frontier_node_number = *this_parse_action;
#if defined(RNGLR_RECOGNISER_TRACE)
      text_printf("Add to Q: ");
      sr_print_action(this_dfa, shift_stack_pointer->current_frontier_node->value, a[1], *this_parse_action);
#endif
      shift_stack_pointer++;                                     /* bump Q pointer */

      this_parse_action++;                                       /* advance action pointer past the shift action */
    }

    for (; *this_parse_action != 0; this_parse_action++)         /* forall reductions in T(0, a_1) */
    {
      if (!this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot].is_accepting)
      {
        reduction_stack_pointer->node = v0;
        reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

  #if defined(RNGLR_RECOGNISER_TRACE)
        text_printf("Load v_0 actions: Add to R: ");
        sr_print_action(this_dfa, reduction_stack_pointer->node->value, a[1], *this_parse_action);
  #endif

        reduction_stack_pointer++;                                 /* Bump R pointer */
      }
    }

    mem_free(these_parse_actions);                               /* Reclaim memory for T(0, a_1) */

    /* Main loop: for i = 0 to do while U_i != { } */
    int thereis_a_shifted_node = true;                           /* true if we created a node during SHIFTER: use to test U_i != { } */
    for (int i = 0; i <= d && thereis_a_shifted_node; i++)
        {
#if defined(RNGLR_RECOGNISER_TRACE)
    text_printf("\nStarting frontier %i: a[i] is %i\n", i, a[i]);
#endif
      /* Clear next_frontier */
      /* Switch frontiers and clear next_frontier: we do this at the beginning so that at the end of the runm current_frontier contains U_d */
      frontier_exchanger = current_frontier;
      current_frontier = next_frontier;
      next_frontier = frontier_exchanger;
      memset(next_frontier, 0, sizeof(ssg_node*) * this_dfa->state_count);

      /* REDUCER */
      while (reduction_stack_pointer != reduction_stack)
      {
        reduction_stack_pointer--;

        ssg_node *original_reduction_node = reduction_stack_pointer->node;
        reduction *original_reduction_table_entry = reduction_stack_pointer->reduction_table_entry;

#if defined(RNGLR_RECOGNISER_TRACE)
        text_printf("Reducer: State (%i,L%i), input symbol %i, action R[%i]\n",
                    original_reduction_node->value, original_reduction_node->level,
                    a[i+1],
                    original_reduction_table_entry - this_dfa->reduction_table);
#endif

#if defined(CHI_HIST)
        /* Initialise the Chi histograms */
        hist_init(&chi_edge_histogram);
        hist_init(&chi_node_histogram);
        hist_init(&chi_prime_edge_histogram);
        hist_init(&chi_prime_node_histogram);

        /* and now build the chi_prime histograms with a recursive walk */
        reduction_search_rec(original_reduction_node, original_reduction_table_entry->length - 1);
#endif

        reduction_search_generate_start(original_reduction_node, original_reduction_table_entry->length - 1);

        /* reduction_search_target_node now contains the first member of Chi, the set of nodes which can be reached along a
           path of length m - 1, or 0 if m = 0. Each time we call reduction_search_next_target() we get a new member of Chi
           in reduction_search_target_node until all have been visited; subsequent calls yield NULL

           In the paper, the current member of Chi is called u, here we call it reduction_search_target
        */
        while (reduction_search_target_node != NULL)
        {
          /* get the shift (the 'goto') out of the table pl is a member of T(k,X) */
          int goto_action = dfa_retrieve_first_action(this_dfa, reduction_search_target_node->value, original_reduction_table_entry->symbol_number);
#if defined(RNGLR_RECOGNISER_TRACE)
          text_printf("Goto state %i: ", goto_action);
#endif

          /* In the paper the goto state is called w, here it is called current_frontier[goto_action - first_dfa_state]. An odd name, which arises from the fact
             that a shift action is simply the state number of the state to be shifted to */

          /* The reducer handles two cases: that in which the node to goto already exists, and that in which it doesn't
             In both cases we need to access the action in T(l, a_{i+1}) so we factor the table access out and perform it here for both cases */
          int *these_goto_parse_actions = dfa_retrieve_all_actions(this_dfa, goto_action, a[i+1]);  /* Get T(goto_state, a_i+1) */
          int *this_goto_parse_action = these_goto_parse_actions;

          if (current_frontier[goto_action - first_dfa_state] != NULL)  /* If there is a w in U_{i} with label l */
          {
#if defined(RNGLR_RECOGNISER_TRACE)
            text_printf("old\n");
#endif
            /* Check out edges of w to see if we have one going to u: as soon as we find one we jump to the end of the reducer and pull the next u from Chi */
            for (ssg_edge* this_edge = (ssg_edge*) graph_next_out_edge(current_frontier[goto_action - first_dfa_state]); this_edge != NULL; this_edge = (ssg_edge*) graph_next_out_edge(this_edge))
              if ((ssg_node*) graph_destination(this_edge) == reduction_search_target_node)
                goto edge_already_exists;

            /* We didn't find an appropriate edge, so now we must add one and stack the appropriate actions for subsequent processing */
            ((ssg_edge*) graph_insert_edge(sizeof(ssg_edge), reduction_search_target_node, current_frontier[goto_action - first_dfa_state]))->symbol = original_reduction_table_entry->symbol_number;   /* create an edge from w to u */

            /* Now we must start stacking the reductions from w */
            if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_goto_parse_action))  /* Skip any shift which will be first in sequence of parse actions */
              this_goto_parse_action++;

            if (original_reduction_table_entry->length != 0)         /* If reduction-edge was created by a non-zero length reduction */
            {
              for (; *this_goto_parse_action != 0; this_goto_parse_action++)         /* forall reductions in T(goto_state, a_1) */
              {
                if (!this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot].is_accepting)   /* skip accepting reductions */
                {
                  /* Add (u, B, t) to R */
                  if (this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot].length != 0)
                  {
#if defined(RNGLR_RECOGNISER_TRACE)
                    text_printf("On old goto state: Add to R: ");
                    sr_print_action(this_dfa, current_frontier[goto_action - first_dfa_state]->value, a[i+1], *this_goto_parse_action);
                    text_printf("\n");
#endif
                    reduction_stack_pointer->node = reduction_search_target_node;  /* u */
                    reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

                    reduction_stack_pointer++;                                 /* Bump R pointer */
                  }
                }
              }
            }
          }
          else
          {
#if defined(RNGLR_RECOGNISER_TRACE)
            text_printf("new\n");
#endif
            /* Create a node w on current_frontier (in U_i) labelled l and an edge (w, u) */
            current_frontier[goto_action - first_dfa_state] = (ssg_node*) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
            current_frontier[goto_action - first_dfa_state]->value = goto_action;
            current_frontier[goto_action - first_dfa_state]->level = i;

            ((ssg_edge*) graph_insert_edge(sizeof(ssg_edge), reduction_search_target_node, current_frontier[goto_action - first_dfa_state]))->symbol = original_reduction_table_entry->symbol_number;

            if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_goto_parse_action))  /* If there is a shift ph in T(goto_state, a+1) */
            {
              shift_stack_pointer->current_frontier_node = current_frontier[goto_action - first_dfa_state];
              shift_stack_pointer->next_frontier_node_number = *this_goto_parse_action;
#if defined(RNGLR_RECOGNISER_TRACE)
              text_printf("On new goto state: Add to Q: ");
              sr_print_action(this_dfa, shift_stack_pointer->current_frontier_node->value, a[i+1], shift_stack_pointer->next_frontier_node_number);
              text_printf("\n");
#endif

              shift_stack_pointer++;                                     /* bump Q pointer */

              this_goto_parse_action++;                                       /* advance action pointer past the shift action */
            }

            /* Now we stack the zero length non-accepting reductions from w using w as the start of the path */
            for (; *this_goto_parse_action != 0; this_goto_parse_action++)         /* forall reductions in T(goto_state, a_i+1) */
            {
              /* Pick out and stack the zero length, non-accepting reductions */
              if (this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot].length == 0 && !this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot].is_accepting)  /* Skip accepting reductions */
              {
                reduction_stack_pointer->node = current_frontier[goto_action - first_dfa_state];   /* w */
                reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

#if defined(RNGLR_RECOGNISER_TRACE)
                text_printf("On new goto state (zero length creating reduction): Add to R: ");
                sr_print_action(this_dfa, current_frontier[goto_action - first_dfa_state]->value, a[i+1], *this_goto_parse_action);
                text_printf("\n");
#endif
                reduction_stack_pointer++;                                 /* Bump R pointer */
              }
            }

            /* Now we do the non-zero length reductions IF w was created by a non-zero length reduction: we use u as the start point on the search path */
            if (original_reduction_table_entry->length != 0)
            {
              /* reset the action pointer to the first reduction in the block */
              this_goto_parse_action = these_goto_parse_actions;

              if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_goto_parse_action))  /* If there is a shift... */
                this_goto_parse_action++;                                              /* ...skip it */

              for (; *this_goto_parse_action != 0; this_goto_parse_action++)         /* forall reductions in T(goto_state, a_i+1) */
              {
                /* Pick out and stack the non-zero length, non-accepting reductions */
                if ((this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot].length != 0) && (!this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot].is_accepting))
                                {
#if defined(RNGLR_RECOGNISER_TRACE)
                  text_printf("On new goto state (nonzero length creating reduction): Add to R: ");
                  sr_print_action(this_dfa, current_frontier[goto_action - first_dfa_state]->value, a[i+1], *this_goto_parse_action);
                  text_printf("\n");
#endif
                  reduction_stack_pointer->node = reduction_search_target_node;       /* u */
                  reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_goto_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

                  reduction_stack_pointer++;                                 /* Bump R pointer */
                }
              }
            }

          }


          edge_already_exists:
            reduction_search_generate_next_target();                  /* Pull the next u from Chi */
        }

#if defined(CHI_HIST)
        text_printf("Chi edges\n");
        hist_print(chi_edge_histogram);
        text_printf("Chi edges ");
        hist_report_differences(chi_edge_histogram, chi_prime_edge_histogram);
        text_printf("Chi nodes\n");
        hist_print(chi_node_histogram);
        text_printf("Chi nodes ");
        hist_report_differences(chi_node_histogram, chi_prime_node_histogram);

        hist_free(&chi_edge_histogram);
        hist_free(&chi_node_histogram);
        hist_free(&chi_prime_edge_histogram);
        hist_free(&chi_prime_node_histogram);
#endif

      }

      /*SHIFTER */
      thereis_a_shifted_node = false;
      if (i != d)
      {
        shift_stack_prime_pointer = shift_stack_prime;           /* Q' = { ] */

        while (shift_stack_pointer != shift_stack)               /* While Q != { } */
        {
          /* The shifter handles two cases: that in which the node to shift to already exists, and that in which it doesn't
             In both cases we need to access the action in T(k, a_{i+2}) so we factor the table access out and perform it here for both cases */
          shift_stack_pointer--;
#if defined(RNGLR_RECOGNISER_TRACE)
      text_printf("Shifter processing current frontier %i, next frontier %i, symbol %i\n",
                  shift_stack_pointer->current_frontier_node->value,
                  shift_stack_pointer->next_frontier_node_number,
                  a[i+1]);
#endif

          int *these_parse_actions = dfa_retrieve_all_actions(this_dfa, shift_stack_pointer->next_frontier_node_number, a[i+2]);  /* Get T(k, a_i+2) */
          int *this_parse_action = these_parse_actions;

          if (next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state] != NULL)  /* If there is a w in U_{i+1} with label k */
          {
            ((ssg_edge*) graph_insert_edge(sizeof(ssg_edge), shift_stack_pointer->current_frontier_node, next_frontier[shift_stack_pointer->next_frontier_node_number  - first_dfa_state]))->symbol = a[i+1];

            if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action)) /* If this first action is a shift, then skip it */
              this_parse_action++;

            for (; *this_parse_action != 0; this_parse_action++)   /* forall reductions in T(k, a_i+2) */
            {
              if (this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot].length != 0)
              {
#if defined(RNGLR_RECOGNISER_TRACE)
                text_printf("Shifter old node: Add to R: ");
                sr_print_action(this_dfa, shift_stack_pointer->next_frontier_node_number, a[i+2], *this_parse_action);
#endif
                reduction_stack_pointer->node = shift_stack_pointer->current_frontier_node;   /* We store the target of the first edge on the search path */
                reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

                reduction_stack_pointer++;                                 /* Bump R pointer */
              }
            }
          }
          else
          {
            next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state] = (ssg_node*) graph_insert_node(sizeof(ssg_node), this_derivation->ssg);
            next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state]->value = shift_stack_pointer->next_frontier_node_number;
            next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state]->level = i + 1;
            thereis_a_shifted_node = true;

            ((ssg_edge*) graph_insert_edge(sizeof(ssg_edge), shift_stack_pointer->current_frontier_node, next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state]))->symbol = a[i+1];

            if (GRAM_IS_DFA_STATE(this_dfa->nfa->grammar, *this_parse_action)) /* If this first action is a shift, then add it into shift_stack_prime */
            {
              shift_stack_prime_pointer->current_frontier_node = next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state];
              shift_stack_prime_pointer->next_frontier_node_number = *this_parse_action;
#if defined(RNGLR_RECOGNISER_TRACE)
              text_printf("Add to Q': ");
              sr_print_action(this_dfa, shift_stack_prime_pointer->current_frontier_node->value, a[i+2], *this_parse_action);
#endif
              shift_stack_prime_pointer++;

              this_parse_action++;                                 /* and skip the shift action */
            }

            for (; *this_parse_action != 0; this_parse_action++)   /* forall reductions in T(k, a_i+2) */
            {
              if (this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot].length != 0)
              {
                reduction_stack_pointer->node = shift_stack_pointer->current_frontier_node;   /* We store the target of the first edge on the search path */
                reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];
#if defined(RNGLR_RECOGNISER_TRACE)
                text_printf("Shifter new node: Add to R: ");
                sr_print_action(this_dfa, reduction_stack_pointer->node->value, a[i+2], *this_parse_action);
#endif
              }
              else
              {
                reduction_stack_pointer->node = next_frontier[shift_stack_pointer->next_frontier_node_number - first_dfa_state];   /* We store the start node on the search path for zero length reductions */
                reduction_stack_pointer->reduction_table_entry = &this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot];

#if defined(RNGLR_RECOGNISER_TRACE)
                text_printf("Shifter new node: Add to R: ");
                sr_print_action(this_dfa, reduction_stack_pointer->node->value, a[i+2], *this_parse_action);
#endif
              }
              reduction_stack_pointer++;                                 /* Bump R pointer */
            }
          }
          mem_free(these_parse_actions);                           /* Reclaim memory for T(k, a_i+2) */
        }

        /* copy Q' to Q by exchanging pointers */
        shift_stack_exchanger = shift_stack;                       /* rotate stack bases through exchange */
        shift_stack = shift_stack_prime;
        shift_stack_prime = shift_stack_exchanger;

        shift_stack_pointer = shift_stack_prime_pointer;           /* set Q-stack-pointer to be Q'-stack-pointer... */
      }
    }
  }

  /* Test for acceptance: scan all states on frontier and their reductions */
  for (int i = 0; i < this_dfa->state_count; i++)
  {
    if (current_frontier[i] != NULL)               /* If state i is on frontier */
    {
      int *these_parse_actions = dfa_retrieve_all_actions(this_dfa, i + first_dfa_state, GRAM_EOS_SYMBOL_NUMBER);  /* Get T(i, $) */

      for (int *this_parse_action = these_parse_actions; *this_parse_action!= 0; this_parse_action++)
        if (GRAM_IS_SLOT(this_dfa->nfa->grammar, *this_parse_action))
          if (this_dfa->reduction_table[*this_parse_action - this_dfa->nfa->grammar->first_level_0_slot].is_accepting)
            this_derivation->accept = 1;

      mem_free(these_parse_actions);
    }
  }

  /* Cleanup: free memory */
  mem_free(current_frontier);
  mem_free(next_frontier);
  mem_free(reduction_stack);
  mem_free(shift_stack);
  mem_free(shift_stack_prime);
  reduction_search_generate_cleanup();
  mem_free(a);

  if (this_derivation->accept)
    text_message(TEXT_INFO, "RNGLR parse: accept\n");
  else
    text_message(TEXT_INFO, "RNGLR parse: reject\n");

  return this_derivation;
}

