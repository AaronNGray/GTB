/*******************************************************************************
*
* GTB release 2.0 by Adrian Johnstone (A.Johnstone@rhul.ac.uk) 15 October 2003
*
* gtb_gp.cpp - generalised parser functions (not GLR: see gtb_sr.cpp for those)
*
* This file may be freely distributed. Please mail improvements to the author.
*
*******************************************************************************/
#include <string.h>
#include <ctype.h>
#include "graph.h"
#include "memalloc.h"
#include "set.h"
#include "textio.h"
#include "gtb.h"
#include "gtb_scr.h"
#include "gtb_gram.h"
#include "gtb_gdg.h"
#include "gtb_gen.h"
#include "gtb_rd.h"
#include "gtb_nfa.h"
#include "gtb_dfa.h"
#include "gtb_sr.h"
#include "gtb_gp.h"

static char *lex_ip;
static grammar* lex_grammar;

// Do a longest match lex from string lex_ip
// #define LEXER_TRACE 1
static unsigned lex(void)
{
  gram_symbols_data *this_symbol,
  *longest_symbol;
  int longest_length = 0;

  while (!isgraph(*lex_ip) && *lex_ip != 0)
    lex_ip++;

  if (*lex_ip == 0)
  {
#if defined(LEXER_TRACE)
    text_printf("Lex: EOS\n");
#endif
    return GRAM_EOS_SYMBOL_NUMBER;
  }

  for (this_symbol = (gram_symbols_data *) symbol_next_symbol_in_scope(symbol_get_scope(lex_grammar->symbol_table));
       this_symbol != NULL;
       this_symbol = (gram_symbols_data *) symbol_next_symbol_in_scope(this_symbol))
    if (this_symbol->name_space == SCRIPT_NS_TERMINAL)
    {
      int this_length = strlen(this_symbol->id);

      if (strncmp(this_symbol->id, lex_ip, this_length) == 0 && this_length > longest_length)
      {
        longest_symbol = this_symbol;
        longest_length = this_length;
      }
    }

  if (longest_length > 0)
  {
#if defined(LEXER_TRACE)
    text_printf("Lex: %i \'%s\'\n", longest_symbol->symbol_number, longest_symbol->id);
#endif
    lex_ip += longest_length;
    return longest_symbol->symbol_number;
  }
  else
  {
    text_printf("Lex: no match starting at %s\n", lex_ip);
    lex_ip++;
    return GRAM_ILLEGAL_SYMBOL_NUMBER;
  }
}


derivation* gp_earley_parse(grammar *this_grammar, char *string)
{
  derivation *this_derivation = (derivation*) mem_calloc(1, sizeof(derivation));
  unsigned token_count;

  lex_grammar = this_grammar;

  for (lex_ip = string; lex() != GRAM_EOS_SYMBOL_NUMBER; token_count++)
    ;

//  text_printf("Input string contains %u tokens\n", token_count);

  unsigned** earley_sets = (unsigned**) mem_calloc(token_count, sizeof (unsigned*));
  unsigned maximum_item_number = graph_max_node_number(this_grammar->rules);
  set_ current_earley_set;

//  text_printf("Grammar contains %u items\n", maximum_item_number);

  unsigned *tokens = (unsigned*) mem_malloc(token_count * sizeof(unsigned));
  unsigned *input_token;

  for (input_token = tokens, lex_ip = string; token_count > 0; token_count--)
    *tokens++ = lex();


  this_derivation->accept = 1;
  return this_derivation;
}

cyk_table* gp_cyk_recognise(grammar *this_grammar, char *string)
{
  cyk_table *this_cyk_table = (cyk_table*) mem_calloc(1, sizeof(derivation));
  unsigned token_count;

  lex_grammar = this_grammar;

  for (lex_ip = string; lex() != GRAM_EOS_SYMBOL_NUMBER; token_count++)
    ;

//  text_printf("Input string contains %u tokens\n", token_count);

  return this_cyk_table;
}

