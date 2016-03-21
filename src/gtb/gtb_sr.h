/*******************************************************************************
*
* GTB release 2.0 by Adrian Johnstone (A.Johnstone@rhul.ac.uk) 28 September 2000
*
* gtb_sr.h - shift-reduce parser functions
*
* This file may be freely distributed. Please mail improvements to the author.
*
*******************************************************************************/
#ifndef GTB_SR_H
#define GTB_SR_H

//#include "gtb_dfa.h"
typedef struct ssg_node_struct
{
  unsigned value;
  unsigned level;
} ssg_node;

typedef struct ssg_edge_struct
{
  unsigned visits;
  unsigned symbol;
} ssg_edge;

typedef struct sppf_node_struct{
  unsigned x;
  unsigned j;
  unsigned i;
} sppf_node;

typedef struct derivation_struct{
  struct dfa *dfa;
  void *ssg;
  void* sppf;
  void *epsilon_sppf;
  sppf_node** epsilon_sppf_index;
  int accept:1;
}  derivation;

derivation* sr_lr_parse(dfa* this_dfa, char *string);
derivation *sr_tomita_1_parse(dfa * this_dfa, char *string, int nullable_accept_states_present, int reduction_queue_length);
derivation *sr_rnglr_recognise(dfa * this_dfa, char *string, int reduction_stack_size);

void sr_print_action(dfa* this_dfa, int state, int this_symbol, int this_parse_action);
void sr_write_derivation(FILE *output_file, derivation *this_derivation);
void sr_render_derivation(FILE *output_file, derivation *this_derivation);
#endif

