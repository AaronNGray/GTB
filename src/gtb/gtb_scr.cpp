/*****************************************************************************
*
* GTB version 2.0 by Adrian Johnstone (A.Johnstone@rhbnc.ac.uk) 28 August 2000
*
* gtb_scr.c - script processor
*
* This file may be freely distributed. Please mail improvements to the author.
*
*****************************************************************************/
#include <stdio.h>
#include <math.h>
#include <time.h>

#include "graph.h"
#include "memalloc.h"
#include "scan.h"
#include "symbol.h"
#include "textio.h"

#include "gtb.h"
#include "gtb_scr.h"
#include "gtb_gram.h"
#include "gtb_gdg.h"
#include "gtb_gen.h"
#include "gtb_rd.h"
#include "gtb_nfa.h"
#include "gtb_dfa.h"
#include "gtb_ah.h"
#include "gtb_sr.h"
#include "gtb_gp.h"
#include "gtb_rnglr_rec.h"
#include "gtb_rnglr_prs.h"
#include "gtb_gdg_analyse_fast.h"

/* #define emit_rpn_trace */
/* #define SCRIPT_EXECUTE_TRACE */

unsigned script_symbol_count;
unsigned script_first_nonterminal;
char *script_symbol_string;
char **script_symbol_ids;

static char *script_string_from_file(FILE *f)
{
  char *string, *string_pointer;

  unsigned text_size = 0;

  while (1)
  {
    int ch = fgetc(f);

    if (ch == EOF)
      break;

    text_size++;
  }

  string_pointer = string = (char*) mem_malloc(text_size + 1);

  rewind(f);

  while (1)
  {
    int ch = fgetc(f);

    if (ch == EOF)
      break;

    *string_pointer++ = (char) ch;
  }

  *string_pointer = 0;

  return string;
}


script_symbols_data *script_epsilon_symbol;

static void *script_symbols;
static void *script_global_scope;
static rdp_tree_node_data *script_rules_root;

static set_ script_homogenous_diadic = SET_NULL;
static set_ script_get_left_value = SET_NULL;
static set_ script_get_right_value = SET_NULL;
static set_ script_becomes_return_post = SET_NULL;
static set_ script_becomes_return_pre = SET_NULL;

int script_gtb_verbose(void)
{
  script_symbols_data *this_symbol = script_symbol_find("gtb_verbose");

  return this_symbol->value->v_BOOLEAN;
}


static script_value script_execute(rdp_tree_node_data * root, int side_effects);

char *script_strdup(char *str)  /* Make a copy of a string, like Unix strdup() */
{
  return strcpy((char *) mem_malloc(strlen(str) + 1), str);
}

script_symbols_data *script_symbol_find(char *id)
{
  return (script_symbols_data *) symbol_find(script_symbols, &id, sizeof(char *), sizeof(script_symbols_data), NULL, SYMBOL_ANY);
}

void script_open_scope(void)
{
  symbol_new_scope(script_symbols, NULL);
}

void script_name_scope(char *scope_name)
{
  symbol_set_scope_name(script_symbols, scope_name);
}

void script_close_scope(void)
{
  symbol_unlink_scope(symbol_get_scope(script_symbols));
  symbol_set_scope(script_symbols, script_global_scope);
}

static char *script_primitive_type_string(int type)
{
  switch (type)
  {
    case SCRIPT_P_C_ACTION: return "C action";
    case SCRIPT_P_EMPTY: return "empty";
    case SCRIPT_P_VOID: return "void";
    case SCRIPT_P_BOOLEAN: return "boolean";
    case SCRIPT_P_NATURAL: return "nat";
    case SCRIPT_P_INTEGER: return "int";
    case SCRIPT_P_REAL: return "real";
    case SCRIPT_P_CHAR: return "char";
    case SCRIPT_P_STRING: return "string";
    case SCRIPT_P_FILE: return "file";
    case SCRIPT_P_BUILT_IN_FUNCTION: return "built_in_function";
    case SCRIPT_P_BUILT_IN_ENUM: return "built_in_enum";
    case SCRIPT_P_NONTERMINAL: return "nonterminal";
    case SCRIPT_P_PRODUCTION: return "production";
    case SCRIPT_P_TERMINAL: return "terminal";
    case SCRIPT_P_TERMINAL_ELEMENT: return "terminal element";
    case SCRIPT_P_EPSILON: return "epsilon";
    case SCRIPT_P_GRAMMAR: return "grammar";
    case SCRIPT_P_GDG: return "gdg";
    case SCRIPT_P_NFA: return "nfa";
    case SCRIPT_P_DFA: return "dfa";
    case SCRIPT_P_AH_TABLE: return "ah table";
    case SCRIPT_P_DERIVATION: return "derivation";
    case SCRIPT_P_COMPOUND: return "compound";
    default: return "unknown";
  }
}

static void script_print_value_diagnostic(script_value this_value)
{
  switch (this_value.type)
  {
    case SCRIPT_P_BOOLEAN: text_printf("%s::%s", this_value.v_BOOLEAN ? "true" : "false", script_primitive_type_string(this_value.type)); break;
    case SCRIPT_P_NATURAL: text_printf("%u::%s", this_value.v_NATURAL, script_primitive_type_string(this_value.type)); break;
    case SCRIPT_P_INTEGER: text_printf("%i::%s", this_value.v_INTEGER, script_primitive_type_string(this_value.type)); break;
    case SCRIPT_P_REAL: text_printf("%f::%s", this_value.v_REAL, script_primitive_type_string(this_value.type)); break;
    case SCRIPT_P_CHAR: text_printf("`%c (%i)::%s", this_value.v_CHAR, this_value.v_CHAR, script_primitive_type_string(this_value.type)); break;
    case SCRIPT_P_STRING: text_printf("\"%s\"::%s", this_value.v_STRING, script_primitive_type_string(this_value.type)); break;
    default: text_printf("::%s", script_primitive_type_string(this_value.type));
  }
}

static void script_write_value(FILE *output_file, script_value this_value)
{
  switch (this_value.type)
  {
    case SCRIPT_P_BOOLEAN: fprintf(output_file, "%s", this_value.v_BOOLEAN ? "true" : "false"); break;
    case SCRIPT_P_NATURAL: fprintf(output_file,"%u", this_value.v_NATURAL); break;
    case SCRIPT_P_INTEGER: fprintf(output_file,"%i", this_value.v_INTEGER); break;
    case SCRIPT_P_REAL: fprintf(output_file,"%f", this_value.v_REAL); break;
    case SCRIPT_P_CHAR: fprintf(output_file,"`%c", this_value.v_CHAR); break;
    case SCRIPT_P_STRING: fprintf(output_file,"%s", this_value.v_STRING); break;
    case SCRIPT_P_GRAMMAR: gram_write(output_file, this_value.v_GRAMMAR);  break;
    case SCRIPT_P_GDG: gdg_write(output_file, this_value.v_GDG); break;
    case SCRIPT_P_NFA: nfa_write(output_file, this_value.v_NFA); break;
    case SCRIPT_P_DFA: dfa_write(output_file, this_value.v_DFA); break;
    case SCRIPT_P_AH_TABLE: ah_table_write(output_file, this_value.v_AH_TABLE); break;
    case SCRIPT_P_DERIVATION: sr_write_derivation(output_file, this_value.v_DERIVATION); break;
    case SCRIPT_P_GENERATED_PARSER: fprintf(output_file, "attempt to write suppressed type GENERATED_PARSER"); break;
    case SCRIPT_P_CYK_TABLE: fprintf(output_file, "attempt to write suppressed type CYK_TABLE"); break;
    case SCRIPT_P_CYCLE_BREAK_SETS: fprintf(output_file, "attempt to write suppressed type CYCLE_BREAK_SETS"); break;
    case SCRIPT_P_AH_TRIE: fprintf(output_file, "attempt to write suppressed type AH_TRIE"); break;
    case SCRIPT_P_RIA: fprintf(output_file, "attempt to write suppressed type RIA"); break;
    case SCRIPT_P_RCA: fprintf(output_file, "attempt to write suppressed type RCA"); break;
    default: fprintf(output_file, "%s", script_primitive_type_string(this_value.type));
  }
}

static void script_render_value(FILE *output_file, script_value this_value)
{
  switch (this_value.type)
  {
    case SCRIPT_P_GRAMMAR: gram_render(output_file, this_value.v_GRAMMAR);  break;
    case SCRIPT_P_GDG: gdg_render(output_file, this_value.v_GDG); break;
    case SCRIPT_P_NFA: nfa_render(output_file, this_value.v_NFA); break;
    case SCRIPT_P_DFA: dfa_render(output_file, this_value.v_DFA); break;
    case SCRIPT_P_DERIVATION: sr_render_derivation(output_file, this_value.v_DERIVATION); break;
    default: text_printf("Attempt to render non-renderable object\n");
  }
}
script_value script_read_symbol_value(rdp_tree_node_data *root, int side_effects)
{
  script_value return_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (root == NULL)
    text_printf("Attempt to read NULL symbol\n");
  else if (root->symbol_table_entry == NULL)
    text_printf("Read symbol '%s' has no symbol table entry\n", root->id);
  else if (root->symbol_table_entry->value == NULL)
    text_printf("Read symbol '%s' has empty value\n", root->id);
  else if (root->symbol_table_entry->value->type == SCRIPT_P_BUILT_IN_FUNCTION)
  {
#if defined(SCRIPT_EXECUTE_TRACE)
    text_printf("Script: calling built in function '%s'\n", root->id);
#endif
    return_value = root->symbol_table_entry->value->v_BUILT_IN_FUNCTION(root, side_effects);
  }
  else
  {
#if defined(SCRIPT_EXECUTE_TRACE)
  text_printf("Script: reading symbol '%s' value ", root->id);
  script_print_value_diagnostic(return_value);
  text_printf("\n");
#endif
    memcpy(&return_value, root->symbol_table_entry->value, sizeof(script_value));
  }

  return return_value;
}

static void script_write_symbol_value(rdp_tree_node_data *root, script_value this_value)
{

#if defined(SCRIPT_EXECUTE_TRACE)
  text_printf("Script: writing symbol '%s' with ", root->id);
  script_print_value_diagnostic(this_value);
  text_printf("\n");
#endif

  if (root == NULL)
    text_printf("Attempt to write to NULL symbol\n");
  else if (root->symbol_table_entry == NULL)
    text_printf("Write symbol '%s' has no symbol table entry\n", root->id);
  else if (root->symbol_table_entry->value == NULL)
  {
    root->symbol_table_entry->value = (script_value*) mem_calloc(1, sizeof(script_value));
    memcpy(root->symbol_table_entry->value, &this_value, sizeof(script_value));
  }
  else if (this_value.type != root->symbol_table_entry->value->type)
  {
    text_printf("Mismatched types: attempt to write ");
    script_print_value_diagnostic(this_value);
    text_printf(" to symbol '%s' which has value ", root->id);
    script_print_value_diagnostic(*(root->symbol_table_entry->value));
    text_printf("\n");
  }
  else
    memcpy(root->symbol_table_entry->value, &this_value, sizeof(script_value));
}

static int script_get_parameter(void **this_edge, script_value *parameter, script_primitive_type type, char *function_name, int side_effects)
{
    if (*this_edge == NULL)
    {
      if (function_name != NULL)
        text_message(TEXT_FATAL, "missing argument in call to function '%s'\n", function_name);
      parameter->type = SCRIPT_P_EMPTY;
      return 0;
    }

    *parameter = script_execute((rdp_tree_node_data*) graph_destination(*this_edge), side_effects);

    if (parameter->type != type)
    {
      if (function_name != NULL)
      {
        text_message(TEXT_FATAL, "type mismatch in call to function '%s': expected type '%s' but found type '%s'\n",
                     function_name,
                     script_primitive_type_string(type),
                     script_primitive_type_string(parameter->type));
      }
      parameter->type = SCRIPT_P_EMPTY;
      return 0;
    }

    *this_edge = graph_next_out_edge(*this_edge);
    return 1;
}

static int script_get_any_parameter(void **this_edge, script_value *parameter, int side_effects)
{
    if (*this_edge == NULL)
    {
      parameter->type = SCRIPT_P_EMPTY;
      return 0;
    }

    *parameter = script_execute((rdp_tree_node_data*) graph_destination(*this_edge), side_effects);

    *this_edge = graph_next_out_edge(*this_edge);
    return 1;
}

static script_value script_built_in_open(void *root, int side_effects)
{
  script_value this_value;
  void *this_edge = graph_next_out_edge(root);
  script_value return_value;
  int file_open_mode;
  char *filename;

  return_value.type = SCRIPT_P_VOID;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_STRING, "open", side_effects);
    filename = this_value.v_STRING;
    return_value.type = SCRIPT_P_FILE;

    if (this_edge == NULL)
      file_open_mode = SCRIPT_BUILT_IN_write_text;
    else
    {
      file_open_mode = SCRIPT_BUILT_IN_illegal;
      script_get_any_parameter(&this_edge, &this_value, side_effects);

      if (this_value.type == SCRIPT_P_BUILT_IN_ENUM)
        file_open_mode = this_value.v_INTEGER;
    }

    switch (file_open_mode)
    {
      case SCRIPT_BUILT_IN_write_text: return_value.v_FILE = fopen(filename, "w"); break;
      case SCRIPT_BUILT_IN_read_text: return_value.v_FILE = fopen(filename, "r"); break;
      case SCRIPT_BUILT_IN_write_raw: return_value.v_FILE = fopen(filename, "wb"); break;
      case SCRIPT_BUILT_IN_read_raw: return_value.v_FILE = fopen(filename, "rb"); break;
      case SCRIPT_BUILT_IN_window: text_message(TEXT_FATAL, "direct output to graphics window not yet implemented\n"); break;
      default: text_message(TEXT_FATAL, "type mismatch in paramater 2 of call to function 'open': expecting write_text or read_text or write_raw or read_raw or window\n"); break;
    }
  }

  if (return_value.v_FILE == NULL)
    text_message(TEXT_FATAL, "unable to open file '%s'\n", filename);

  return return_value;
}

static script_value script_built_in_tokeniser(void *root, int side_effects)
{
  script_value this_value, this_file;
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);

  return_value.type = SCRIPT_P_VOID;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_file, SCRIPT_P_FILE, "tokeniser", side_effects);

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "tokeniser", side_effects);

    gram_tokeniser(this_file.v_FILE, this_value.v_GRAMMAR);
  }

  return return_value;
}

static script_value script_built_in_close(void *root, int side_effects)
{
  script_value this_value;
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);

  return_value.type = SCRIPT_P_VOID;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_FILE, "close", side_effects);
    fclose(this_value.v_FILE);
  }

  return return_value;
}

static script_value script_built_in_flush(void *root, int side_effects)
{
  script_value this_value;
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);

  return_value.type = SCRIPT_P_VOID;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_FILE, "close", side_effects);
    fflush(this_value.v_FILE);
  }

  return return_value;
}

static script_value script_built_in_render(void *root, int side_effects)
{
  void * this_edge= graph_next_out_edge(root);
  script_value return_value;
  FILE *output_file = stdout;

  return_value.type = SCRIPT_P_VOID;

  if (side_effects)
  {
    if (script_get_parameter(&this_edge, &return_value, SCRIPT_P_FILE, NULL, side_effects))
      output_file = return_value.v_FILE;

    for (; this_edge != NULL; this_edge = graph_next_out_edge(this_edge))
      script_render_value(output_file, return_value = script_execute((rdp_tree_node_data*) graph_destination(this_edge), side_effects));
  }

  return return_value;
}

static script_value script_built_in_write(void *root, int side_effects)
{
  void * this_edge= graph_next_out_edge(root);
  script_value return_value;
  FILE *output_file = stdout;

  return_value.type = SCRIPT_P_VOID;

  if (side_effects)
  {
    if (script_get_parameter(&this_edge, &return_value, SCRIPT_P_FILE, NULL, side_effects))
      output_file = return_value.v_FILE;

    for (; this_edge != NULL; this_edge = graph_next_out_edge(this_edge))
      script_write_value(output_file, return_value = script_execute((rdp_tree_node_data*) graph_destination(this_edge), side_effects));
  }

  return return_value;
}

static script_value script_built_in_read(void *root, int side_effects)
{
  script_value return_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
    return_value.v_INTEGER = ((rdp_tree_node_data*) root)->token;

  return return_value;
}

static script_value script_built_in_grammar(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value start_rule, this_value;

  int tilde_enabled = 0;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &start_rule, SCRIPT_P_NONTERMINAL, "grammar", side_effects);

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "grammar", side_effects);

      if (this_value.v_INTEGER == SCRIPT_BUILT_IN_tilde_enabled)
        tilde_enabled = 1;
      else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_tilde_disabled)
        tilde_enabled = 0;
      else
        text_message(TEXT_FATAL, "'grammar' parameter 2 must be either 'tilde_enabled' or 'tilde_disabled'\n");
    }

    return_value.type = SCRIPT_P_GRAMMAR;
    return_value.v_GRAMMAR = gram_construct_gram(script_rules_root, (rdp_tree_node_data*) (start_rule.v_POINTER), tilde_enabled);
  }

  return return_value;
}

static script_value script_built_in_augment_grammar(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "augment_grammar", side_effects);

    return_value.type = SCRIPT_P_VOID;
    gram_tidy(this_value.v_GRAMMAR, 1, 1);
  }

  return return_value;
}

static script_value script_built_in_terminalise_grammar(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "tilde", side_effects);
    grammar *this_grammar = this_value.v_GRAMMAR;

    int terminalise = 0;

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "tilde", side_effects);
      if (this_value.v_INTEGER == SCRIPT_BUILT_IN_terminal_all)
        terminalise = 2;
      else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_terminal)
        terminalise = 1;
      else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_nonterminal)
        terminalise = 0;
      else
        text_message(TEXT_FATAL, "'tilde' parameter 2 must be either 'terminal' or 'terminal_all' or 'nonterminal'\n");
    }

    return_value.type = SCRIPT_P_VOID;
    gram_tilde(this_grammar, terminalise);
  }

  return return_value;
}

static script_value script_built_in_remove_multiple_direct_recursion(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "remove_multiple_direct_recursion", side_effects);

    return_value.type = SCRIPT_P_GRAMMAR;
    return_value.v_POINTER = gram_remove_multiple_direct_recursion(this_value.v_GRAMMAR);
  }

  return return_value;
}

static script_value script_built_in_ebnf2bnf(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "ebnf2bnf", side_effects);

    return_value.type = SCRIPT_P_GRAMMAR;
    return_value.v_POINTER = gram_ebnf2bnf(this_value.v_GRAMMAR);
  }

  return return_value;
}

static script_value script_built_in_cnf(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "cnf", side_effects);

    return_value.type = SCRIPT_P_GRAMMAR;
    return_value.v_POINTER = gram_cnf(this_value.v_GRAMMAR);
  }

  return return_value;
}

static script_value script_built_in_gnf(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "gnf", side_effects);

    return_value.type = SCRIPT_P_GRAMMAR;
    return_value.v_POINTER = gram_gnf(this_value.v_GRAMMAR);
  }

  return return_value;
}

static script_value script_built_in_gdg(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "gdg", side_effects);

    return_value.type = SCRIPT_P_GDG;
    return_value.v_POINTER = gdg_construct_gdg(this_value.v_GRAMMAR);
  }

  return return_value;
}

static script_value script_built_in_parser_generate(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "parser_generate", side_effects);

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "nfa", side_effects);

    switch (this_value.v_INTEGER)
    {
      case SCRIPT_BUILT_IN_ll:
        text_message(TEXT_FATAL, "ll parser generation suppressed in version 2.5\n");
        break;

      case SCRIPT_BUILT_IN_lalr:
        text_message(TEXT_FATAL, "lalr parser generation suppressed in version 2.5\n");
        break;

      case SCRIPT_BUILT_IN_lr:
        text_message(TEXT_FATAL, "lr parser generation suppressed in version 2.5\n");
        break;

      case SCRIPT_BUILT_IN_slr:
        text_message(TEXT_FATAL, "slr parser generation suppressed in version 2.5\n");
        break;

      case SCRIPT_BUILT_IN_rnglr:
        text_message(TEXT_FATAL, "rnglr parser generation suppressed in version 2.5\n");
        break;

      case SCRIPT_BUILT_IN_ri:
        text_message(TEXT_FATAL, "ri parser generation suppressed in version 2.5\n");
        break;

      default: text_message(TEXT_FATAL, "'parser_generate' parameter 2: expecting one of 'll', 'lalr', 'lr', 'slr', 'rnglr' or 'ri'\n");
    }

    return_value.type = SCRIPT_P_GENERATED_PARSER;
    return_value.v_POINTER = NULL;
  }

  return return_value;
}

static script_value script_built_in_gdg_compress(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value, optional_value;
  int recursion_level = 0;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GDG, "gdg_compress", side_effects);

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &optional_value, SCRIPT_P_INTEGER, "gdg_compress", side_effects);
      recursion_level = optional_value.v_INTEGER;
    }

    return_value.type = SCRIPT_P_GDG;
    return_value.v_POINTER = gdg_compress_gdg(this_value.v_GDG, recursion_level);
  }

  return return_value;
}

static script_value script_built_in_cycle_break_sets(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  unsigned long break_set_cardinality_limit = 0;
  gdg *this_gdg;
  int break_set_disposition = SCRIPT_BUILT_IN_prune_break_sets_by_table;
  bool restart_after_cardinality_limit_reached = false;
  bool delete_break_sets = false;
  unsigned long break_set_count = 1000000;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    while (this_edge != NULL)
    {
      script_get_any_parameter(&this_edge, &this_value, side_effects);

      if (this_value.type == SCRIPT_P_GDG)
      {
        this_gdg = this_value.v_GDG;
      }
      else if (this_value.type == SCRIPT_P_BUILT_IN_ENUM)
      {
        if (this_value.v_INTEGER == SCRIPT_BUILT_IN_retain_break_sets)
          break_set_disposition = SCRIPT_BUILT_IN_retain_break_sets;
        else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_prune_break_sets_by_element)
          break_set_disposition = SCRIPT_BUILT_IN_prune_break_sets_by_element;
        else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_prune_break_sets_by_set)
          break_set_disposition = SCRIPT_BUILT_IN_prune_break_sets_by_set;
        else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_prune_break_sets_by_table)
          break_set_disposition = SCRIPT_BUILT_IN_prune_break_sets_by_table;
        else if (this_value.v_INTEGER == SCRIPT_BUILT_IN_delete_break_sets)
          delete_break_sets = true;
      }
      else if (this_value.type == SCRIPT_P_INTEGER)
      {
        if (this_value.v_INTEGER < 0)
        {
          break_set_cardinality_limit = - this_value.v_INTEGER;
          restart_after_cardinality_limit_reached = true;
        }
        else
        {
          break_set_cardinality_limit = this_value.v_INTEGER;
          restart_after_cardinality_limit_reached = false;
        }
      }
      else
        text_message(TEXT_FATAL, "cycle_break_sets: expecting GDG or INTEGER or one of 'retain_break_sets', 'prune_break_sets_by_element', 'prune_break_sets_by_table' or 'delete_break_sets'\n"); 
    }
    return_value.type = SCRIPT_P_VOID;
    gdg_analyse_fast(this_gdg, break_set_disposition, delete_break_sets, break_set_cardinality_limit, restart_after_cardinality_limit_reached, break_set_count);
  }

  return return_value;
}

static script_value script_built_in_generate(void *root, int side_effects)
{
  script_value this_value;
  grammar *this_gram;
  unsigned string_count;
  void *this_edge = graph_next_out_edge(root);
  int sentential_forms;
  int order;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "generate", side_effects);
    this_gram = this_value.v_GRAMMAR;

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_INTEGER, "generate", side_effects);
    string_count = this_value.v_INTEGER;

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "generate", side_effects);
    order = this_value.v_INTEGER;
    if (!(order == SCRIPT_BUILT_IN_left || order == SCRIPT_BUILT_IN_right ||
          order == SCRIPT_BUILT_IN_random))
      text_message(TEXT_FATAL, "'generate' parameter 3: expecting 'left', 'right' or 'random'\n");

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "generate", side_effects);
    switch(this_value.v_INTEGER)
    {
      case SCRIPT_BUILT_IN_sentences: sentential_forms = 0; break;
      case SCRIPT_BUILT_IN_sentential_forms: sentential_forms = 1; break;
      default: text_message(TEXT_FATAL, "'generate' parameter 4: expecting 'sentences' or 'sentential_forms'\n");
    }

    gen_generate(this_gram, this_gram->start_rule, string_count, order, sentential_forms, 0);
  }

  this_value.type = SCRIPT_P_EMPTY;
  return this_value;
}

static script_value script_built_in_nfa(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  grammar *this_gram;
  int unrolled = 0;
  int not_left = 0;
  int lookahead;
  int nullable_reductions = 0;
  int nonterminal_lookahead_sets = 0;
  int singleton_lookahead_sets = 0;
  int nfa_kind;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "nfa", side_effects);
    this_gram = this_value.v_GRAMMAR;

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "nfa", side_effects);

    switch (nfa_kind = this_value.v_INTEGER)
    {
      case SCRIPT_BUILT_IN_ll:
        text_message(TEXT_FATAL, "ll NFA construction not implemented\n");
        break;

      case SCRIPT_BUILT_IN_lalr:
        text_message(TEXT_FATAL, "lalr NFA construction not implemented\n");
        break;

      case SCRIPT_BUILT_IN_lr:
      case SCRIPT_BUILT_IN_slr:
      case SCRIPT_BUILT_IN_rolled:
        unrolled = 0;
        break;

      case SCRIPT_BUILT_IN_ri:
      case SCRIPT_BUILT_IN_unrolled:
        unrolled = 1;
        break;

      case SCRIPT_BUILT_IN_unrolled_not_left:
        unrolled = 1;
        not_left = 1;
        break;

      default: text_message(TEXT_FATAL, "'nfa' parameter 2: expecting one of 'll', 'lalr', 'lr', 'slr', 'ri', 'rolled', 'unrolled' or 'unrolled_not_left'\n");
    }

    script_get_parameter(&this_edge, &this_value, SCRIPT_P_INTEGER, "nfa", side_effects);
    lookahead = this_value.v_INTEGER;

    if ((nfa_kind == SCRIPT_BUILT_IN_slr || nfa_kind == SCRIPT_BUILT_IN_lr) && lookahead < 0)
      text_message(TEXT_FATAL, "'nfa' parameter 3 must be positive for slr and lr constructions\n");

    if (nfa_kind == SCRIPT_BUILT_IN_slr)
      lookahead = -lookahead;

    while (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_BUILT_IN_ENUM, "nfa", side_effects);

      switch (nfa_kind = this_value.v_INTEGER)
      {

        case SCRIPT_BUILT_IN_normal_reductions:
          nullable_reductions = 0;
          break;

        case SCRIPT_BUILT_IN_nullable_reductions:
          nullable_reductions = 1;
          break;

        case SCRIPT_BUILT_IN_terminal_lookahead_sets:
          nonterminal_lookahead_sets = 0;
          break;

        case SCRIPT_BUILT_IN_nonterminal_lookahead_sets:
          nonterminal_lookahead_sets = 1;
          break;

        case SCRIPT_BUILT_IN_full_lookahead_sets:
          singleton_lookahead_sets = 0;
          break;

        case SCRIPT_BUILT_IN_singleton_lookahead_sets:
          singleton_lookahead_sets = 1;
          break;

        default: text_message(TEXT_FATAL, "nfa parameter 4: expecting one of 'normal_reductions' or 'nullable_reductions'\n");
      }
    }

    return_value.type = SCRIPT_P_NFA;
    return_value.v_NFA = nfa_construct_nfa(this_gram, unrolled, not_left, lookahead, nullable_reductions, nonterminal_lookahead_sets, singleton_lookahead_sets);
  }

  return return_value;
}

static script_value script_built_in_dfa(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  nfa *this_nfa;
  unsigned label_buffer_size = 0;
  unsigned table_buffer_size = UINT_MAX;   /* default means suppress */
  unsigned hash_buckets = 0;
  unsigned hash_prime = 0;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_NFA, "dfa", side_effects);
    this_nfa = this_value.v_NFA;

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_INTEGER, "dfa", side_effects);
      table_buffer_size = (unsigned) this_value.v_INTEGER;
    }

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_INTEGER, "dfa", side_effects);
      label_buffer_size = (unsigned) this_value.v_INTEGER;
    }

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_INTEGER, "dfa", side_effects);
      hash_buckets = (unsigned) this_value.v_INTEGER;
    }

    if (this_edge != NULL)
    {
      script_get_parameter(&this_edge, &this_value, SCRIPT_P_INTEGER, "dfa", side_effects);
      hash_prime = (unsigned) this_value.v_INTEGER;
    }

    return_value.type = SCRIPT_P_DFA;
    return_value.v_DFA = dfa_construct_dfa(this_nfa, table_buffer_size, label_buffer_size, hash_buckets, hash_prime);
  }

  return return_value;
}

static script_value script_built_in_dfa_statistics(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  dfa* this_dfa;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "dfa_statistics", side_effects);
    this_dfa = this_value.v_DFA;

    return_value.type = SCRIPT_P_VOID;
    dfa_dfa_statistics(this_dfa);
  }

  return return_value;
}

static script_value script_built_in_la_merge(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  dfa *this_dfa;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "la_merge", side_effects);
    this_dfa = this_value.v_DFA;

    return_value.type = SCRIPT_P_DFA;
    return_value.v_DFA = dfa_la_merge(this_dfa);
  }

  return return_value;
}

static script_value script_built_in_earley_parse(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  script_value this_grammar;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_grammar, SCRIPT_P_GRAMMAR, "earley_parse", side_effects);

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'earley_parse': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_DERIVATION;
    return_value.v_DERIVATION = gp_earley_parse(this_grammar.v_GRAMMAR, this_value.v_STRING);
  }

  return return_value;
}

static script_value script_built_in_cyk_recognise(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  script_value this_grammar;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_grammar, SCRIPT_P_GRAMMAR, "cyk_recognise", side_effects);

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'cyk_recognise': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_CYK_TABLE;
    return_value.v_CYK_TABLE = gp_cyk_recognise(this_grammar.v_GRAMMAR, this_value.v_STRING);
  }

  return return_value;
}

static script_value script_built_in_ah_trie(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "ah_trie", side_effects);
    grammar *this_grammar = this_value.v_GRAMMAR;

    return_value.type = SCRIPT_P_AH_TABLE;
    return_value.v_AH_TABLE = ah_ah_table(this_grammar);
  }

  return return_value;
}

static script_value script_built_in_prefix_grammar(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;

  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_GRAMMAR, "prefix_grammar", side_effects);
    grammar *this_grammar = this_value.v_GRAMMAR;

    return_value.type = SCRIPT_P_GRAMMAR;
    return_value.v_POINTER = ahz_left_context_grammar(this_grammar);
  }

  return return_value;
}

static script_value script_built_in_ah_recognise(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_table;
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_table, SCRIPT_P_AH_TABLE, "ah_recognise", side_effects);
    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'ah_recognise': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_INTEGER;
    return_value.v_INTEGER = ah_ah_recognise(this_table.v_AH_TABLE, this_value.v_STRING);
  }

  return return_value;
}

static script_value script_built_in_ri_recognise(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_table;
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_any_parameter(&this_edge, &this_table, side_effects);

    if (this_table.type == SCRIPT_P_GRAMMAR)
    {
      gram_tilde(this_table.v_GRAMMAR, 1);

      this_table.type = SCRIPT_P_AH_TABLE;
      this_table.v_AH_TABLE = ah_ah_table(this_table.v_GRAMMAR);
    }
    else if (this_table.type == SCRIPT_P_AH_TABLE)
    {
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'ri_recognise': expected type AH_TABLE or GRAMMAR but found '%s'\n",
                     script_primitive_type_string(this_table.type));
        this_table.v_AH_TABLE = NULL;
    }

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'ri_recognise': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }

    return_value.type = SCRIPT_P_INTEGER;
    return_value.v_INTEGER = ah_ah_recognise(this_table.v_AH_TABLE, this_value.v_STRING);
  }

  return return_value;
}

static script_value script_built_in_grd_parse(void *root, int side_effects)
{
  script_value return_value;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;
  script_value this_grammar;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_grammar, SCRIPT_P_GRAMMAR, "grd_parse", side_effects);
    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'grd_parse': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_VOID;
    rd_grd_parse(this_grammar.v_GRAMMAR, this_value.v_STRING);
  }

  return return_value;
}

static script_value script_built_in_lr_parse(void *root, int side_effects)
{
  script_value return_value;
  dfa *this_dfa;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "lr_parse", side_effects);
    this_dfa = this_value.v_DFA;

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'lr_parse': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }

    return_value.type = SCRIPT_P_DERIVATION;
    return_value.v_DERIVATION = sr_lr_parse(this_dfa, this_value.v_STRING);
  }

  return return_value;
}

static script_value script_built_in_rnglr_recognise(void *root, int side_effects)
{
  script_value return_value;
  dfa *this_dfa;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "rnglr_recognise", side_effects);
    this_dfa = this_value.v_DFA;

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'rnglr_recognise': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }

    return_value.type = SCRIPT_P_DERIVATION;
    return_value.v_DERIVATION = sr_rnglr_recognise(this_dfa, this_value.v_STRING, 0);
  }

  return return_value;
}

static script_value script_built_in_rnglr_parse(void *root, int side_effects)
{
  script_value return_value;
  dfa *this_dfa;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "rnglr_parse", side_effects);
    this_dfa = this_value.v_DFA;

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'rnglr_parse': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_DERIVATION;
    return_value.v_DERIVATION = sr_rnglr_parse(this_dfa, this_value.v_STRING, 0);
  }

  return return_value;
}

static script_value script_built_in_tomita_1_parse(void *root, int side_effects)
{
  script_value return_value;
  dfa *this_dfa;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "tomita_1_parse", side_effects);
    this_dfa = this_value.v_DFA;

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'tomita_1_parse': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_DERIVATION;
    return_value.v_DERIVATION = sr_tomita_1_parse(this_dfa, this_value.v_STRING, 0, 0);
  }

  return return_value;
}

static script_value script_built_in_tomita_1_nullable_accepts_parse(void *root, int side_effects)
{
  script_value return_value;
  dfa *this_dfa;
  void *this_edge = graph_next_out_edge(root);
  script_value this_value;

  return_value.type = SCRIPT_P_EMPTY;
  if (side_effects)
  {
    script_get_parameter(&this_edge, &this_value, SCRIPT_P_DFA, "tomita_1_nullable_accepts_parse", side_effects);
    this_dfa = this_value.v_DFA;

    script_get_any_parameter(&this_edge, &this_value, side_effects);

    if (this_value.type == SCRIPT_P_STRING)
      ;
    else if (this_value.type == SCRIPT_P_FILE)
    {
      this_value.type == SCRIPT_P_STRING;

      this_value.v_STRING = script_string_from_file(this_value.v_FILE);
    }
    else
    {
        text_message(TEXT_FATAL, "type mismatch in call to function 'tomita_1_nullable_accepts_parse': expected type STRING or FILE but found '%s'\n",
                     script_primitive_type_string(this_value.type));
        this_value.v_STRING = "";
    }


    return_value.type = SCRIPT_P_DERIVATION;
    return_value.v_DERIVATION = sr_tomita_1_parse(this_dfa, this_value.v_STRING, 1, 0);
  }

  return return_value;
}

static script_value script_built_in_date_time(void *root, int side_effects)
{
  script_value return_value;

  if (side_effects)
    return_value.v_INTEGER = ((rdp_tree_node_data*) root)->token;
  return_value.type = SCRIPT_P_STRING;
  return_value.v_STRING = text_time_string();

  return return_value;
}

static script_value script_built_in_CPU_time(void *root, int side_effects)
{
  script_value return_value;

  if (side_effects)
    return_value.v_INTEGER = ((rdp_tree_node_data*) root)->token;
  return_value.type = SCRIPT_P_REAL;
  return_value.v_REAL = (float) (clock() / CLOCKS_PER_SEC);

  return return_value;
}

void script_make_built_in_function(char *name, script_value (*v_BUILT_IN_FUNCTION) (void *root, int side_effects))
{
  script_symbols_data *this_symbol = script_symbol_find(name);

  this_symbol->read_only = 1;

  this_symbol->value = (script_value*) mem_calloc(1, sizeof(script_value));
  this_symbol->value->type = SCRIPT_P_BUILT_IN_FUNCTION;
  this_symbol->value->v_BUILT_IN_FUNCTION = v_BUILT_IN_FUNCTION;
}

void script_make_built_in_string(char *name, char *v_STRING)
{
  script_symbols_data *this_symbol = script_symbol_find(name);

  this_symbol->read_only = 1;

  this_symbol->value = (script_value*) mem_calloc(1, sizeof(script_value));
  this_symbol->value->type = SCRIPT_P_STRING;
  this_symbol->value->v_STRING = v_STRING;
}

void script_make_built_in_boolean(char *name, int v_BOOLEAN)
{
  script_symbols_data *this_symbol = script_symbol_find(name);

  this_symbol->read_only = 1;

  this_symbol->value = (script_value*) mem_calloc(1, sizeof(script_value));
  this_symbol->value->type = SCRIPT_P_BOOLEAN;
  this_symbol->value->v_BOOLEAN = v_BOOLEAN;
}

void script_make_built_in_enum(char *name, int v_INTEGER)
{
  script_symbols_data *this_symbol = script_symbol_find(name);

  this_symbol->read_only = 1;

  this_symbol->value = (script_value*) mem_calloc(1, sizeof(script_value));
  this_symbol->value->type = SCRIPT_P_BUILT_IN_ENUM;
  this_symbol->value->v_INTEGER = v_INTEGER;
}

void script_make_built_in_file(char *name, FILE *v_FILE)
{
  script_symbols_data *this_symbol = script_symbol_find(name);

  this_symbol->read_only = 1;

  this_symbol->value = (script_value*) mem_calloc(1, sizeof(script_value));
  this_symbol->value->type = SCRIPT_P_FILE;
  this_symbol->value->v_FILE = v_FILE;
}

void script_make_built_in_epsilon(char *name)
{
  script_symbols_data *this_symbol = script_symbol_find(name);

  this_symbol->read_only = 1;

  this_symbol->value = (script_value*) mem_calloc(1, sizeof(script_value));
  this_symbol->value->type = SCRIPT_P_EPSILON;

  script_epsilon_symbol = this_symbol;
}

void script_initialise(char *sourcefilename)
{
  script_symbols = symbol_new_table("script symbols", 101, 31, symbol_compare_string, symbol_hash_string, symbol_print_string);
  script_global_scope = symbol_get_scope(script_symbols);

  script_make_built_in_epsilon("#");

  /* Input/output functions */
  script_make_built_in_function("open", script_built_in_open);
  script_make_built_in_function("close", script_built_in_close);
  script_make_built_in_function("flush", script_built_in_flush);
  script_make_built_in_function("read", script_built_in_read);
  script_make_built_in_function("render", script_built_in_render);
  script_make_built_in_function("write", script_built_in_write);

  /* Input/output file types */
  script_make_built_in_enum("read_text", SCRIPT_BUILT_IN_read_text);
  script_make_built_in_enum("write_text", SCRIPT_BUILT_IN_write_text);
  script_make_built_in_enum("read_raw", SCRIPT_BUILT_IN_read_raw);
  script_make_built_in_enum("write_raw", SCRIPT_BUILT_IN_write_raw);
  script_make_built_in_enum("window", SCRIPT_BUILT_IN_window);
  script_make_built_in_file("default_input", stdin);
  script_make_built_in_file("default_output", stdout);

  /* Grammar functions */
  script_make_built_in_function("grammar", script_built_in_grammar);
  script_make_built_in_function("ebnf2bnf", script_built_in_ebnf2bnf);
  script_make_built_in_function("cnf", script_built_in_cnf);
  script_make_built_in_function("gnf", script_built_in_gnf);
  script_make_built_in_function("augment_grammar", script_built_in_augment_grammar);
  script_make_built_in_function("terminalise_grammar", script_built_in_terminalise_grammar);
  script_make_built_in_function("remove_multiple_direct_recursion", script_built_in_remove_multiple_direct_recursion);
  script_make_built_in_function("gdg", script_built_in_gdg);
  script_make_built_in_function("cycle_break_sets", script_built_in_cycle_break_sets);
  script_make_built_in_function("gdg_compress", script_built_in_gdg_compress);
  script_make_built_in_function("generate", script_built_in_generate);
  script_make_built_in_function("nfa", script_built_in_nfa);
  script_make_built_in_function("dfa", script_built_in_dfa);
  script_make_built_in_function("dfa_statistics", script_built_in_dfa_statistics);
  script_make_built_in_function("la_merge", script_built_in_la_merge);
  script_make_built_in_function("earley_parse", script_built_in_earley_parse);
  script_make_built_in_function("cyk_recognise", script_built_in_cyk_recognise);
  script_make_built_in_function("prefix_grammar", script_built_in_prefix_grammar);
  script_make_built_in_function("ah_trie", script_built_in_ah_trie);
  script_make_built_in_function("ah_recognise", script_built_in_ah_recognise);
  script_make_built_in_function("ri_recognise", script_built_in_ri_recognise);
  script_make_built_in_function("grd_parse", script_built_in_grd_parse);
  script_make_built_in_function("lr_parse", script_built_in_lr_parse);
  script_make_built_in_function("tomita_1_parse", script_built_in_tomita_1_parse);
  script_make_built_in_function("tomita_1_nullable_accepts_parse", script_built_in_tomita_1_nullable_accepts_parse);
  script_make_built_in_function("rnglr_recognise", script_built_in_rnglr_recognise);
  script_make_built_in_function("rnglr_parse", script_built_in_rnglr_parse);

  /* Parser output functions */
  script_make_built_in_function("tokeniser", script_built_in_tokeniser);
  script_make_built_in_function("parser_generate", script_built_in_parser_generate);

  /* generator modes */
  script_make_built_in_enum("sentences", SCRIPT_BUILT_IN_sentences);
  script_make_built_in_enum("sentential_forms", SCRIPT_BUILT_IN_sentential_forms);
  script_make_built_in_enum("left", SCRIPT_BUILT_IN_left);
  script_make_built_in_enum("right", SCRIPT_BUILT_IN_right);
  script_make_built_in_enum("random", SCRIPT_BUILT_IN_random);

  /* Automata types */
  script_make_built_in_enum("ll", SCRIPT_BUILT_IN_ll);
  script_make_built_in_enum("slr", SCRIPT_BUILT_IN_slr);
  script_make_built_in_enum("lalr", SCRIPT_BUILT_IN_lalr);
  script_make_built_in_enum("lr", SCRIPT_BUILT_IN_lr);
  script_make_built_in_enum("ri", SCRIPT_BUILT_IN_ri);
  script_make_built_in_enum("rolled", SCRIPT_BUILT_IN_rolled);
  script_make_built_in_enum("unrolled", SCRIPT_BUILT_IN_unrolled);
  script_make_built_in_enum("unrolled_not_left", SCRIPT_BUILT_IN_unrolled_not_left);

  script_make_built_in_enum("nullable_reductions", SCRIPT_BUILT_IN_nullable_reductions);
  script_make_built_in_enum("normal_reductions", SCRIPT_BUILT_IN_normal_reductions);

  script_make_built_in_enum("terminal_lookahead_sets", SCRIPT_BUILT_IN_terminal_lookahead_sets);
  script_make_built_in_enum("nonterminal_lookahead_sets", SCRIPT_BUILT_IN_nonterminal_lookahead_sets);
  script_make_built_in_enum("singleton_lookahead_sets", SCRIPT_BUILT_IN_singleton_lookahead_sets);
  script_make_built_in_enum("full_lookahead_sets", SCRIPT_BUILT_IN_full_lookahead_sets);

  script_make_built_in_enum("terminal", SCRIPT_BUILT_IN_terminal);
  script_make_built_in_enum("nonterminal", SCRIPT_BUILT_IN_nonterminal);

  script_make_built_in_enum("tilde_enabled", SCRIPT_BUILT_IN_tilde_enabled);
  script_make_built_in_enum("tilde_disabled", SCRIPT_BUILT_IN_tilde_disabled);

  script_make_built_in_enum("retain_break_sets", SCRIPT_BUILT_IN_retain_break_sets);
  script_make_built_in_enum("prune_break_sets_by_element", SCRIPT_BUILT_IN_prune_break_sets_by_element);
  script_make_built_in_enum("prune_break_sets_by_set", SCRIPT_BUILT_IN_prune_break_sets_by_set);
  script_make_built_in_enum("prune_break_sets_by_table", SCRIPT_BUILT_IN_prune_break_sets_by_table);

  script_make_built_in_enum("delete_break_sets", SCRIPT_BUILT_IN_delete_break_sets);

  /* GTB internal variables and functions */
  script_make_built_in_boolean("true", 1);
  script_make_built_in_boolean("false", 0);
  script_make_built_in_boolean("gtb_verbose", 0);
  script_make_built_in_string("lex_whitespace", "");
  script_make_built_in_string("gtb_version", GTB_VERSION);  /* GTB name and version */
  script_make_built_in_string("gtb_main_file_name", sourcefilename); /* Name of input file on command line */

  /* Timer functions */
  script_make_built_in_function("date_time", script_built_in_date_time); /* String containing date and time */
  script_make_built_in_function("CPU_time", script_built_in_CPU_time);  /* real number containing CPU time since start */
}

static void script_render_rdt(void *rdt, char *filename)
{
  FILE *vcg_file = fopen(filename, "w");

  if (vcg_file == NULL)
    text_message(TEXT_FATAL, "unable to open VCG file '%s' for write\n", filename);

  text_redirect(vcg_file);
  graph_vcg(rdt, NULL, scan_vcg_print_node, scan_vcg_print_edge);
  text_redirect(stdout);
  fclose(vcg_file);
}

/* Output RPN, conditional on emit. In any case, return the number of RPN instructions that would be emited
   by this subtree */
static unsigned long script_emit_rpn(rdp_tree_node_data * root, int emit)
{
  unsigned long subtree_rpn_size = 0;

  if (strcmp(root->id, "?") == 0)
  {
    /* Measure size of right subtree */
    unsigned long right_subtree_rpn_size = script_emit_rpn((rdp_tree_node_data *) graph_destination(graph_next_out_edge(graph_next_out_edge(root))), 0);

    /* Output left tree */
    unsigned long left_subtree_rpn_size = script_emit_rpn((rdp_tree_node_data *) graph_destination(graph_next_out_edge(root)), emit);

    /* Output branch operator */
    if (emit)
      text_printf("%lu ~?? ", right_subtree_rpn_size + 1);

    /* Output right tree */
    script_emit_rpn((rdp_tree_node_data *) graph_destination(graph_next_out_edge(graph_next_out_edge(root))), emit);

    subtree_rpn_size = left_subtree_rpn_size + right_subtree_rpn_size + 2;
  }
  else if (strcmp(root->id, "@") == 0)
  {
    /* Measure size of right subtree */
    unsigned long right_subtree_rpn_size = script_emit_rpn((rdp_tree_node_data *) graph_destination(graph_next_out_edge(graph_next_out_edge(root))), 0);

    /* Output left tree */
    unsigned long left_subtree_rpn_size = script_emit_rpn((rdp_tree_node_data *) graph_destination(graph_next_out_edge(root)), emit);

    /* Output branch operator */
    if (emit)
      text_printf("%lu ~?? ", right_subtree_rpn_size + 4);

    /* Output right tree */
    script_emit_rpn((rdp_tree_node_data *) graph_destination(graph_next_out_edge(graph_next_out_edge(root))), emit);

    /* Output unconditional branch */
    if (emit)
      text_printf("0 -%lu ~?? ", left_subtree_rpn_size + right_subtree_rpn_size + 5);

    subtree_rpn_size = left_subtree_rpn_size + right_subtree_rpn_size + 5;
  }
  else
  {                             /* Non-control flow operators */
    void *this_edge;
    int is_script_header = strcmp(root->id, "script") == 0;
/*    script_symbols_data *this_script_symbol = (script_symbols_data *) root->symbol_table_entry; */

    /* Output a leading parenthesis if this is a new script region */
    if (emit)
    {
      subtree_rpn_size++;

      if (is_script_header)
        text_printf("( ");
    }

    for (this_edge = graph_next_out_edge(root); this_edge != NULL; this_edge = graph_next_out_edge(this_edge))
      subtree_rpn_size += script_emit_rpn((rdp_tree_node_data *) graph_destination(this_edge), emit);

    if (emit)
    {
      subtree_rpn_size++;

      if (is_script_header)
        text_printf(") ");
      else
        text_printf("%s ", root->id);
    }
  }

#if defined(emit_rpn_trace)
  if (emit)
    text_printf("[%lu] ", subtree_rpn_size);
#endif

  return subtree_rpn_size;
}

static script_value script_execute(rdp_tree_node_data * root, int side_effects)
{
  /* We evaluate left = left op right, making assignment side effects where necessary */
  void *this_edge;

  script_value left_value, right_value, return_value;

  rdp_tree_node_data *left_subtree = NULL;
  rdp_tree_node_data *right_subtree = NULL;

  if (graph_next_out_edge(root) != NULL)
  {
    left_subtree = (rdp_tree_node_data*) graph_destination(graph_next_out_edge(root));

    if (graph_next_out_edge(graph_next_out_edge(root)) != NULL)
      right_subtree = (rdp_tree_node_data*) graph_destination(graph_next_out_edge(graph_next_out_edge(root)));
  }

  return_value.type = SCRIPT_P_VOID;  /* default is return void */

  if (root == NULL)  /* Shouldn't arrive here with a NULL root, but just in case... */
    return return_value;

  if (set_includes_element(&script_get_left_value, root->token))
    left_value = script_execute(left_subtree, side_effects);

  if (set_includes_element(&script_get_right_value, root->token))
    right_value = script_execute(right_subtree, side_effects);

#if defined(SCRIPT_EXECUTE_TRACE)
  text_printf("Script: executing node '%s'", root->id);
    if (root->symbol_table_entry != NULL)
      text_printf(":%p", root->symbol_table_entry);

  text_printf(", side effects %s", side_effects ? "on" : "off");
  text_printf("\n        left child '%s'", left_subtree == NULL ? "NULL" : left_subtree->id);
  if (left_subtree != NULL)
    if (left_subtree->symbol_table_entry != NULL)
      text_printf(":%p", left_subtree->symbol_table_entry);
  text_printf("\n        right child '%s'", right_subtree == NULL ? "NULL" : right_subtree->id, right_subtree == NULL ? NULL : right_subtree->symbol_table_entry);
  if (right_subtree != NULL)
    if (right_subtree->symbol_table_entry != NULL)
      text_printf(":%p", right_subtree->symbol_table_entry);
  text_printf("\n");
#endif

  if (set_includes_element(&script_homogenous_diadic, root->token) && (left_value.type != right_value.type))
    text_message(TEXT_FATAL, "mismatched types for operator '%s'\n", root->id);

  switch (root->token)
  {
    /* Control flow */
    case 0 /* sequence */:
      for (this_edge = graph_next_out_edge(root); this_edge != NULL; this_edge = graph_next_out_edge(this_edge))
        return_value = script_execute((rdp_tree_node_data *) graph_destination(this_edge), side_effects);
      break;

    case RDP_T_63 /* ? */ :  /* select */
      left_value = script_execute(left_subtree, side_effects);

      return_value.type = SCRIPT_P_VOID;

      if (left_value.type != SCRIPT_P_BOOLEAN)
        text_printf("Left hand side of ? operator must be a boolean expression ");
      else
        return_value = script_execute(right_subtree, side_effects && left_value.v_BOOLEAN);
      break;

    case RDP_T_64 /* @ */ :  /* iterate */
      left_value = script_execute(left_subtree, side_effects);

      return_value.type = SCRIPT_P_VOID;

      if (left_value.type != SCRIPT_P_BOOLEAN)
        text_printf("Left hand side of ? operator must be a boolean expression ");
      else
        while (side_effects && left_value.v_BOOLEAN)
        {
          return_value = script_execute(right_subtree, side_effects && left_value.v_BOOLEAN);
          left_value = script_execute(left_subtree, side_effects);
        }
      break;

    /* nonadics */
    case RDP_T_34 /* " */ :   /* String literal */
      return_value.type = SCRIPT_P_STRING;
      return_value.v_STRING = (char*) (root->id);
      break;

    case SCAN_P_ID:           /* variable, function etc */
      return_value = script_read_symbol_value(root, side_effects);
      break;

    case SCAN_P_INTEGER:      /* Integer literal */
      return_value.type = SCRIPT_P_INTEGER;
      return_value.v_INTEGER = root->data.i;
      break;

    case SCAN_P_REAL:         /* Real literal */
      return_value.type = SCRIPT_P_REAL;
      return_value.v_REAL = (float) (root->data.r);
      break;

#define stringify(not_string) #not_string
#define OPERATOR_ADDITIONAL_CASE(op) case op:
#define OPERATOR_START(op) case op: switch (left_value.type) {
#define OPERATOR_FINISH default: text_message(TEXT_FATAL, "%s operator applied to illegal type\n", root->id); } break;

#define MONADIC_CASE(flavour) case SCRIPT_P_##flavour: return_value.type = SCRIPT_P_##flavour; return_value.v_##flavour = c_op left_value.v_##flavour; break;
#define DIADIC_CASE(ret_flavour, flavour) case SCRIPT_P_##flavour: return_value.type = SCRIPT_P_##ret_flavour; return_value.v_##ret_flavour = left_value.v_##flavour c_op right_value.v_##flavour; break;

    /* monadics */
#define c_op ~
    OPERATOR_START(RDP_T_126 /* ~ */)
    MONADIC_CASE(BOOLEAN)
    MONADIC_CASE(NATURAL)
    MONADIC_CASE(INTEGER)
    OPERATOR_FINISH
#undef c_op

    /* Assignment */
    case RDP_T_5861 /* := */ :
      memcpy(&return_value, &right_value, sizeof(script_value));
      break;

    /* Relational operators */
#define c_op <
    OPERATOR_START(RDP_T_60 /* < */ )
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(BOOLEAN, INTEGER)
    DIADIC_CASE(BOOLEAN, NATURAL)
    DIADIC_CASE(BOOLEAN, REAL)
    DIADIC_CASE(BOOLEAN, CHAR)
    case SCRIPT_P_STRING: return_value.v_BOOLEAN = strcmp(left_value.v_STRING, right_value.v_STRING) c_op 0; break;
    OPERATOR_FINISH
#undef c_op

#define c_op <=
    OPERATOR_START(RDP_T_6061 /* <= */ )
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(BOOLEAN, INTEGER)
    DIADIC_CASE(BOOLEAN, NATURAL)
    DIADIC_CASE(BOOLEAN, REAL)
    DIADIC_CASE(BOOLEAN, CHAR)
    case SCRIPT_P_STRING: return_value.v_BOOLEAN = strcmp(left_value.v_STRING, right_value.v_STRING) c_op 0; break;
    OPERATOR_FINISH
#undef c_op

#define c_op ==
    OPERATOR_START(RDP_T_61 /* = */ )
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(BOOLEAN, INTEGER)
    DIADIC_CASE(BOOLEAN, NATURAL)
    DIADIC_CASE(BOOLEAN, REAL)
    DIADIC_CASE(BOOLEAN, CHAR)
    case SCRIPT_P_STRING: return_value.v_BOOLEAN = strcmp(left_value.v_STRING, right_value.v_STRING) c_op 0; break;
    OPERATOR_FINISH
#undef c_op

#define c_op >
    OPERATOR_START(RDP_T_62 /* > */ )
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(BOOLEAN, INTEGER)
    DIADIC_CASE(BOOLEAN, NATURAL)
    DIADIC_CASE(BOOLEAN, REAL)
    DIADIC_CASE(BOOLEAN, CHAR)
    case SCRIPT_P_STRING: return_value.v_BOOLEAN = strcmp(left_value.v_STRING, right_value.v_STRING) c_op 0; break;
    OPERATOR_FINISH
#undef c_op

#define c_op >=
    OPERATOR_START(RDP_T_6261 /* >= */ )
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(BOOLEAN, INTEGER)
    DIADIC_CASE(BOOLEAN, NATURAL)
    DIADIC_CASE(BOOLEAN, REAL)
    DIADIC_CASE(BOOLEAN, CHAR)
    case SCRIPT_P_STRING: return_value.v_BOOLEAN = strcmp(left_value.v_STRING, right_value.v_STRING) c_op 0; break;
    OPERATOR_FINISH
#undef c_op

#define c_op !=
    OPERATOR_START(RDP_T_6062 /* <> */ )
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(BOOLEAN, INTEGER)
    DIADIC_CASE(BOOLEAN, NATURAL)
    DIADIC_CASE(BOOLEAN, REAL)
    DIADIC_CASE(BOOLEAN, CHAR)
    case SCRIPT_P_STRING: return_value.v_BOOLEAN = strcmp(left_value.v_STRING, right_value.v_STRING) c_op 0; break;
    OPERATOR_FINISH
#undef c_op

    /* Diadic logic and arithmentic operators */
#define c_op |=
    OPERATOR_ADDITIONAL_CASE(RDP_T_12461 /* |= */)
    OPERATOR_ADDITIONAL_CASE(RDP_T_61124 /* =| */)
    OPERATOR_START(RDP_T_124 /* | */)
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    OPERATOR_FINISH
#undef c_op

#define c_op &
    OPERATOR_ADDITIONAL_CASE(RDP_T_38 /* & */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_3861 /* &= */)
    OPERATOR_START(RDP_T_6138 /* =& */)
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    OPERATOR_FINISH
#undef c_op

#define c_op ^
    OPERATOR_ADDITIONAL_CASE(RDP_T_36 /* $ */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_3661 /* $= */)
    OPERATOR_START(RDP_T_6136 /* =$ */)
    DIADIC_CASE(BOOLEAN, BOOLEAN)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    OPERATOR_FINISH
#undef c_op

#define c_op +
    OPERATOR_ADDITIONAL_CASE(RDP_T_43 /* + */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_4361 /* += */)
    OPERATOR_START(RDP_T_6143 /* =+ */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    DIADIC_CASE(REAL, REAL)
    OPERATOR_FINISH
#undef c_op

#define c_op -
    OPERATOR_ADDITIONAL_CASE(RDP_T_45 /* - */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_4561 /* -= */)
    OPERATOR_START(RDP_T_6145 /* =- */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    DIADIC_CASE(REAL, REAL)
    OPERATOR_FINISH
#undef c_op

#define c_op %
    OPERATOR_ADDITIONAL_CASE(RDP_T_37 /* % */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_3761 /* %= */)
    OPERATOR_START(RDP_T_6137 /* =% */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    OPERATOR_FINISH
#undef c_op

#define c_op *
    OPERATOR_ADDITIONAL_CASE(RDP_T_42 /* * */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_4261 /* *= */)
    OPERATOR_START(RDP_T_6142 /* =* */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    DIADIC_CASE(REAL, REAL)
    OPERATOR_FINISH
#undef c_op

#define c_op /
    OPERATOR_ADDITIONAL_CASE(RDP_T_47 /* / */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_4761 /* /= */)
    OPERATOR_START(RDP_T_6147 /* =/ */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    DIADIC_CASE(REAL, REAL)
    OPERATOR_FINISH
#undef c_op

#define c_op <<
    OPERATOR_ADDITIONAL_CASE(RDP_T_6060 /* << */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_606061 /* <<= */)
    OPERATOR_START(RDP_T_616060 /* =<< */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    OPERATOR_FINISH
#undef c_op

#define c_op >>
    OPERATOR_ADDITIONAL_CASE(RDP_T_6262 /* >> */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_626261 /* >>= */)
    OPERATOR_START(RDP_T_616262 /* =>> */)
    DIADIC_CASE(INTEGER, INTEGER)
    DIADIC_CASE(NATURAL, NATURAL)
    OPERATOR_FINISH
#undef c_op

#define c_op **
    OPERATOR_ADDITIONAL_CASE(RDP_T_4242 /* ** */)
    OPERATOR_ADDITIONAL_CASE (RDP_T_424261 /* **= */)
    OPERATOR_START(RDP_T_614242 /* =** */)
    case SCRIPT_P_INTEGER: return_value.v_INTEGER = (int) pow((double) left_value.v_INTEGER, (double) right_value.v_INTEGER); break;
    case SCRIPT_P_NATURAL: return_value.v_NATURAL = (unsigned) pow((double) left_value.v_NATURAL, (double) right_value.v_NATURAL); break;
    case SCRIPT_P_REAL: return_value.v_REAL = (float) pow((double) left_value.v_REAL, (double) right_value.v_REAL); break;
    OPERATOR_FINISH
#undef c_op
  }

  /* Now do assignment side-effects */
  if (side_effects && set_includes_element(&script_becomes_return_post, root->token))
    script_write_symbol_value(left_subtree, return_value);
  else if (side_effects && set_includes_element(&script_becomes_return_pre, root->token))
  {
    right_value = script_read_symbol_value(left_subtree, side_effects);
    script_write_symbol_value(left_subtree, return_value);
    return_value = right_value;
  }
#if defined(SCRIPT_EXECUTE_TRACE)
  text_printf("        returning ");
  script_print_value_diagnostic(return_value);
  text_printf("\n");
#endif

  return return_value;
}

void script_process(void *rdt)
{
  rdp_tree_node_data *script_root = (rdp_tree_node_data *) graph_destination(graph_next_out_edge(graph_next_out_edge(graph_root(rdt))));
  script_value return_value;

  script_rules_root = (rdp_tree_node_data *) graph_destination(graph_next_out_edge(graph_root(rdt)));
  script_render_rdt(rdt, "gtb_rdt.vcg");


  set_assign_list(&script_homogenous_diadic,
                  RDP_T_124 /* | */,

                  RDP_T_38 /* & */,

                  RDP_T_36 /* $ */,

                  RDP_T_43 /* + */,

                  RDP_T_45 /* - */,

                  RDP_T_47 /* / */,

                  RDP_T_37 /* % */,

                  RDP_T_42 /* * */,

                  RDP_T_6060 /* << */,

                  RDP_T_6262 /* >> */,

                  RDP_T_4242 /* ** */,


                  RDP_T_62 /* > */,
                  RDP_T_60 /* < */,
                  RDP_T_6061 /* <= */,
                  RDP_T_6261 /* >= */,
                  RDP_T_61 /* = */,
                  RDP_T_6062 /* <> */,
                  SET_END);

  set_assign_list(&script_get_left_value,
                  RDP_T_124 /* | */,
                  RDP_T_12461 /* |= */,
                  RDP_T_61124 /* =| */,

                  RDP_T_38 /* & */,
                  RDP_T_3861 /* &= */,
                  RDP_T_6138 /* =& */,

                  RDP_T_36 /* $ */,
                  RDP_T_3661 /* $= */,
                  RDP_T_6136 /* =$ */,

                  RDP_T_43 /* + */,
                  RDP_T_4361 /* += */,
                  RDP_T_6143 /* =+ */,

                  RDP_T_45 /* - */,
                  RDP_T_4561 /* -= */,
                  RDP_T_6145 /* =- */,

                  RDP_T_47 /* / */,
                  RDP_T_4761 /* /= */,
                  RDP_T_6147 /* =/ */,

                  RDP_T_37 /* % */,
                  RDP_T_3761 /* %= */,
                  RDP_T_6137 /* =% */,

                  RDP_T_42 /* * */,
                  RDP_T_4261 /* *= */,
                  RDP_T_6142 /* =* */,

                  RDP_T_6060 /* << */,
                  RDP_T_606061 /* <<= */,
                  RDP_T_616060 /* =<< */,

                  RDP_T_6262 /* >> */,
                  RDP_T_626261 /* >>= */,
                  RDP_T_616262 /* =>> */,

                  RDP_T_4242 /* ** */,
                  RDP_T_424261 /* **= */,
                  RDP_T_614242 /* =** */,

                  RDP_T_62 /* > */,
                  RDP_T_60 /* < */,
                  RDP_T_6061 /* <= */,
                  RDP_T_6261 /* >= */,
                  RDP_T_61 /* = */,
                  RDP_T_6062 /* <> */,

                  RDP_T_126 /* ~ */,
                  SET_END);

  set_assign_list(&script_get_right_value,
                  RDP_T_124 /* | */,
                  RDP_T_12461 /* |= */,
                  RDP_T_61124 /* =| */,

                  RDP_T_38 /* & */,
                  RDP_T_3861 /* &= */,
                  RDP_T_6138 /* =& */,

                  RDP_T_36 /* $ */,
                  RDP_T_3661 /* $= */,
                  RDP_T_6136 /* =$ */,

                  RDP_T_43 /* + */,
                  RDP_T_4361 /* += */,
                  RDP_T_6143 /* =+ */,

                  RDP_T_45 /* - */,
                  RDP_T_4561 /* -= */,
                  RDP_T_6145 /* =- */,

                  RDP_T_47 /* / */,
                  RDP_T_4761 /* /= */,
                  RDP_T_6147 /* =/ */,

                  RDP_T_37 /* % */,
                  RDP_T_3761 /* %= */,
                  RDP_T_6137 /* =% */,

                  RDP_T_42 /* * */,
                  RDP_T_4261 /* *= */,
                  RDP_T_6142 /* =* */,

                  RDP_T_6060 /* << */,
                  RDP_T_606061 /* <<= */,
                  RDP_T_616060 /* =<< */,

                  RDP_T_6262 /* >> */,
                  RDP_T_626261 /* >>= */,
                  RDP_T_616262 /* =>> */,

                  RDP_T_4242 /* ** */,
                  RDP_T_424261 /* **= */,
                  RDP_T_614242 /* =** */,

                  RDP_T_5861 /* := */,

                  RDP_T_62 /* > */,
                  RDP_T_60 /* < */,
                  RDP_T_6061 /* <= */,
                  RDP_T_6261 /* >= */,
                  RDP_T_61 /* = */,
                  RDP_T_6062 /* <> */,
                  SET_END);

  set_assign_list(&script_becomes_return_post,
                  RDP_T_12461 /* |= */,

                  RDP_T_3861 /* &= */,

                  RDP_T_3661 /* $= */,

                  RDP_T_4361 /* += */,

                  RDP_T_4561 /* -= */,

                  RDP_T_4761 /* /= */,

                  RDP_T_3761 /* %= */,

                  RDP_T_4261 /* *= */,

                  RDP_T_606061 /* <<= */,

                  RDP_T_626261 /* >>= */,

                  RDP_T_424261 /* **= */,

                  RDP_T_5861 /* := */,
                  SET_END);

  set_assign_list(&script_becomes_return_pre,
                  RDP_T_61124 /* =| */,

                  RDP_T_6138 /* =& */,

                  RDP_T_6136 /* =$ */,

                  RDP_T_6143 /* =+ */,

                  RDP_T_6145 /* =- */,

                  RDP_T_6147 /* =/ */,

                  RDP_T_6137 /* =% */,

                  RDP_T_6142 /* =* */,

                  RDP_T_616060 /* =<< */,

                  RDP_T_616262 /* =>> */,

                  RDP_T_614242 /* =** */,
                  SET_END);

  if (graph_next_out_edge(script_rules_root) == NULL)
    text_message(TEXT_WARNING, "no rules in source file\n");

/*
  script_emit_rpn(script_root, 1);
  text_printf("\n");
*/

  return_value = script_execute(script_root, 1);
}


void script_check_for_errors(void)
{
  if (text_total_errors()!= 0)
  {
    text_printf("\n");
    text_message(TEXT_FATAL, "error%s detected in source file \'%s\'\n", text_total_errors()== 1 ? "": "s", rdp_sourcefilename);
  }
}

