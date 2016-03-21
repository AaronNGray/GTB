###############################################################################
#
# GTB release 2.50 by Adrian Johnstone (A.Johnstone@rhul.ac.uk) 1 November 2005
#
###############################################################################
CPPFLAGS = -I src/gtb -I src/gtb_lib -ansi -pedantic

vpath %.cpp src/gtb src/gtb_lib

gtb:	gtb.cpp gtb_ah.cpp gtb_dfa.cpp gtb_gdg.cpp gtb_gdg_analyse_fast.cpp gtb_gen.cpp gtb_gp.cpp gtb_gram.cpp gtb_lex.cpp gtb_nfa.cpp gtb_rd.cpp gtb_rnglr_prs.cpp gtb_rnglr_rec.cpp gtb_scr.cpp gtb_sr.cpp arg.cpp graph.cpp hist.cpp memalloc.cpp scan.cpp scanner.cpp set.cpp symbol.cpp textio.cpp trie.cpp util.cpp
