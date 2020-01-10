/******************************************
* File:	    tries.c			  *
* Author:   Ricardo Rocha                 *
* Comments: Tries module for yap          *
******************************************/



/* -------------------------- */
/*          Includes          */
/* -------------------------- */

#include <YapInterface.h>
#include <stdio.h>
#include <string.h>
#include "tries.h"



/* -------------------------- */
/*      Local Procedures      */
/* -------------------------- */

static TrNode put_trie(TrNode node, YAP_Term entry);
static YAP_Term get_trie(TrNode node, YAP_Term *stack_list, TrNode *cur_node);
static void free_child_nodes(TrNode node);
static void traverse_trie_usage(TrNode node, int depth);
static void traverse_trie(TrNode node, char *str, int str_index, int *arity);



/* -------------------------- */
/*       Local Variables      */
/* -------------------------- */

static struct global_trie_stats GLOBAL_STATS;
static struct local_trie_stats LOCAL_STATS;
static int MODE;
static TrNode TRIES;
static TrHash HASHES;
static YAP_Term TERM_STACK[TERM_STACK_SIZE];
static YAP_Term *stack_args, *stack_args_base, *stack_vars, *stack_vars_base;
static YAP_Functor FunctorComma;
static int max_index;



/* -------------------------- */
/*     Inline Procedures      */
/* -------------------------- */

static inline
TrNode trie_node_check_insert(TrNode parent, YAP_Term t) {
  TrNode child;

  child = TrNode_child(parent);
  if (child == NULL) {
    new_trie_node(child, t, parent, NULL, NULL, NULL);
    TrNode_child(parent) = child;
    return child;
  } else if (! IS_TRIE_HASH(child)) {
    int count = 0;
    do {
      if (TrNode_entry(child) == t) {
        return child;
      }
      count++;
      child = TrNode_next(child);
    } while (child);
    new_trie_node(child, t, parent, NULL, TrNode_child(parent), NULL);
#ifdef ALLOW_REMOVE_TRIE
    TrNode_previous(TrNode_child(parent)) = child;
#endif /* ALLOW_REMOVE_TRIE */
    if (++count > MAX_NODES_PER_TRIE_LEVEL) {
      /* alloc a new trie hash */
      TrHash hash;
      TrNode chain, next, *bucket;
      new_trie_hash(hash, count);
      chain = child;
      do {
        bucket = TrHash_bucket(hash, HASH_TERM(TrNode_entry(chain), BASE_HASH_BUCKETS - 1));
        next = TrNode_next(chain);
        TrNode_next(chain) = *bucket;
#ifdef ALLOW_REMOVE_TRIE
        TrNode_previous(chain) = AS_TR_NODE_NEXT(bucket);
	if (*bucket)
	  TrNode_previous(*bucket) = chain;
#endif /* ALLOW_REMOVE_TRIE */
        *bucket = chain;
        chain = next;
      } while (chain);
      TrNode_child(parent) = (TrNode) hash;
    } else {
      TrNode_child(parent) = child;
    }
    return child;
  } else {
    /* is trie hash */
    TrHash hash;
    TrNode *bucket;
    int count;
    hash = (TrHash) child;
    bucket = TrHash_bucket(hash, HASH_TERM(t, TrHash_seed(hash)));
    child = *bucket;
    count = 0;
    while (child) {
      if (TrNode_entry(child) == t) {
        return child;
      }
      count++;
      child = TrNode_next(child);
    } while (child);
    TrHash_num_nodes(hash)++;
    new_trie_node(child, t, parent, NULL, *bucket, AS_TR_NODE_NEXT(bucket));
#ifdef ALLOW_REMOVE_TRIE
    if (*bucket)
      TrNode_previous(*bucket) = child;
#endif /* ALLOW_REMOVE_TRIE */
    *bucket = child;
    if (count > MAX_NODES_PER_BUCKET && TrHash_num_nodes(hash) > TrHash_num_buckets(hash)) {
      /* expand trie hash */
      TrNode chain, next, *first_bucket, *new_bucket;
      int seed;
      first_bucket = TrHash_buckets(hash);
      bucket = first_bucket + TrHash_num_buckets(hash);
      TrHash_num_buckets(hash) *= 2;
      new_hash_buckets(hash, TrHash_num_buckets(hash)); 
      seed = TrHash_num_buckets(hash) - 1;
      do {
        if (*--bucket) {
          chain = *bucket;
          do {
            new_bucket = TrHash_bucket(hash, HASH_TERM(TrNode_entry(chain), seed));
            next = TrNode_next(chain);
            TrNode_next(chain) = *new_bucket;
#ifdef ALLOW_REMOVE_TRIE
	    TrNode_previous(chain) = AS_TR_NODE_NEXT(bucket);
	    if (*new_bucket)
	      TrNode_previous(*new_bucket) = chain;
#endif /* ALLOW_REMOVE_TRIE */
            *new_bucket = chain;
            chain = next;
          } while (chain);
        }
      } while (bucket != first_bucket);
      free_hash_buckets(first_bucket, TrHash_num_buckets(hash) / 2);
    }
    return child;
  }
}



/* -------------------------- */
/*            API             */     
/* -------------------------- */

void init_tries_module(void) {
  MODE = MODE_STANDARD;
  TRIES = NULL;
  HASHES = NULL;

  MEMORY_IN_USE = 0;
  MEMORY_MAX_USED = 0;
  NODES_IN_USE = 0;
  NODES_MAX_USED = 0;
  HASHES_IN_USE = 0;
  HASHES_MAX_USED = 0;
  BUCKETS_IN_USE = 0;
  BUCKETS_MAX_USED = 0;

  FunctorComma = YAP_MkFunctor(YAP_LookupAtom(","), 2);
  return;
}


TrNode open_trie(void) {
  TrNode new_node;

  new_trie_node(new_node, 0, NULL, NULL, TRIES, AS_TR_NODE_NEXT(&TRIES));
#ifdef ALLOW_REMOVE_TRIE
  TrNode_hits(new_node)++;
  if (TRIES)
    TrNode_previous(TRIES) = new_node;
#endif /* ALLOW_REMOVE_TRIE */
  TRIES = new_node;
  return new_node;
}


void close_trie(TrNode node) {
  if (TrNode_parent(node))
    fprintf(stderr,"\nTries module: invalid top level node\n");
  if (TrNode_child(node))
    free_child_nodes(TrNode_child(node));
#ifdef ALLOW_REMOVE_TRIE
  if (TrNode_next(node)) {
    TrNode_previous(TrNode_next(node)) = TrNode_previous(node);
    TrNode_next(TrNode_previous(node)) = TrNode_next(node);
  } else
    TrNode_next(TrNode_previous(node)) = NULL;
  free_trie_node(node);  
#else
  TrNode_child(node) = NULL;
#endif /* ALLOW_REMOVE_TRIE */
  return;
}


void close_all_tries(void) {
  TrNode aux_node;
  while (TRIES) {
    if (TrNode_child(TRIES))
      free_child_nodes(TrNode_child(TRIES));
    aux_node = TrNode_next(TRIES);
    free_trie_node(TRIES);
    TRIES = aux_node;
  }
  return;
}


TrNode put_trie_entry(TrNode node, YAP_Term entry, int mode) {
  MODE = mode;
  stack_args_base = stack_args = TERM_STACK;
  stack_vars_base = stack_vars = TERM_STACK + TERM_STACK_SIZE - 1;

  node = put_trie(node, entry);

  /* reset var terms */
  while (STACK_NOT_EMPTY(stack_vars++, stack_vars_base)) {
    //  *((YAP_Term *)POP_DOWN(stack_vars)) = *stack_vars;
    POP_DOWN(stack_vars);
    *((YAP_Term *)*stack_vars) = *stack_vars;
  }

#ifdef ALLOW_REMOVE_TRIE
  TrNode_hits(node)++;
#endif /* ALLOW_REMOVE_TRIE */
  return node;
}


YAP_Term get_trie_entry(TrNode node, int mode) {
  MODE = mode;
  stack_vars_base = stack_vars = TERM_STACK;
  stack_args_base = stack_args = TERM_STACK + TERM_STACK_SIZE - 1;
  max_index = -1;

  return get_trie(node, stack_args, &node);
}


#ifdef ALLOW_REMOVE_TRIE
void remove_trie_entry(TrNode node) {
  TrNode parent;

  TrNode_hits(node)--;
  if (TrNode_child(node))
    return;

  while (TrNode_hits(node) == 0) {
    parent = TrNode_parent(node);
    if (TrNode_previous(node)) {
      if (IS_TRIE_HASH(TrNode_child(parent))) {
	TrHash hash = (TrHash) TrNode_child(parent);
	TrHash_num_nodes(hash)--;
	if (TrHash_num_nodes(hash)) {
	  if (TrNode_next(node)) {
	    TrNode_next(TrNode_previous(node)) = TrNode_next(node);
	    TrNode_previous(TrNode_next(node)) = TrNode_previous(node);
	  } else {
	    TrNode_next(TrNode_previous(node)) = NULL;
	  }
	  free_trie_node(node);
	  return;
	}
	if (TrHash_next(hash)) {
	  TrHash_previous(TrHash_next(hash)) = TrHash_previous(hash);
	  TrHash_next(TrHash_previous(hash)) = TrHash_next(hash);
	} else 
	  TrHash_next(TrHash_previous(hash)) = NULL;
	free_hash_buckets(TrHash_buckets(hash), TrHash_num_buckets(hash));
	free_trie_hash(hash);
      } else {
	if (TrNode_next(node)) {
	  TrNode_next(TrNode_previous(node)) = TrNode_next(node);
	  TrNode_previous(TrNode_next(node)) = TrNode_previous(node);
	} else {
	  TrNode_next(TrNode_previous(node)) = NULL;
	}
	free_trie_node(node);
	return;
      }
    } else if (TrNode_next(node)) {
      TrNode_child(parent) = TrNode_next(node);
      TrNode_previous(TrNode_next(node)) = NULL;
      free_trie_node(node);
      return;
    }
    free_trie_node(node);
    node = parent;
  }

  TrNode_child(node) = NULL;
  return;
}
#endif /* ALLOW_REMOVE_TRIE */


void trie_stats(int *nodes, int *hashes, int *buckets, int *memory) {
  *nodes = NODES_IN_USE;
  *hashes = HASHES_IN_USE;
  *buckets = BUCKETS_IN_USE;
  *memory = MEMORY_IN_USE;
}


void trie_max_stats(int *nodes, int *hashes, int *buckets, int *memory) {
  *nodes = NODES_MAX_USED;
  *hashes = HASHES_MAX_USED;
  *buckets = BUCKETS_MAX_USED;
  *memory = MEMORY_MAX_USED;
}


void trie_usage(TrNode node, int *entries, int *nodes, int *virtual_nodes) {
  TRIE_ENTRIES = 0;
  TRIE_NODES = 0;
  TRIE_VIRTUAL_NODES = 0;
  if (TrNode_child(node))
    traverse_trie_usage(TrNode_child(node), 0);
  *entries = TRIE_ENTRIES;
  *nodes = TRIE_NODES;
  *virtual_nodes = TRIE_VIRTUAL_NODES;
  return;
}


void print_trie(TrNode node) {
  fprintf(stdout, "\n----------- TRIE (%p) -----------\n", node);
  if (TrNode_child(node)) {
    int arity[100];
    char str[1000];
    int str_index;
    arity[0] = 0;
    str_index = 0;
    traverse_trie(TrNode_child(node), str, str_index, arity);
  } else
    fprintf(stdout, "                 (empty)\n");
  fprintf(stdout, "----------------------------------------\n");
  return;
}



/* -------------------------- */
/*      Local Procedures      */
/* -------------------------- */

static
TrNode put_trie(TrNode node, YAP_Term entry) {
  YAP_Term t = YAP_Deref(entry);
  if (YAP_IsVarTerm(t)) {
    if (IsTrieVar(t)) {
      node = trie_node_check_insert(node, MkTrieVar((stack_vars_base - 1 - (YAP_Term *)t) / 2));
    } else {
      node = trie_node_check_insert(node, MkTrieVar((stack_vars_base - stack_vars) / 2));
      PUSH_UP(stack_vars, t, stack_args);
      *((YAP_Term *)t) = (YAP_Term)stack_vars;
      PUSH_UP(stack_vars, stack_vars, stack_args);
    }
  } else if (YAP_IsAtomTerm(t)) {
    node = trie_node_check_insert(node, t);
  } else if (YAP_IsIntTerm(t)) {
    node = trie_node_check_insert(node, t);
  } else if (YAP_IsFloatTerm(t)) {
    volatile double f;
    volatile YAP_Term *p;
    f = YAP_FloatOfTerm(t);
    p = (YAP_Term *) &f;
    /* node = trie_node_check_insert(node, FloatInitTag); */
    node = trie_node_check_insert(node, *p);
    node = trie_node_check_insert(node, *(p + 1));
    node = trie_node_check_insert(node, FloatEndTag);
  } else if (YAP_IsPairTerm(t)) {
    node = trie_node_check_insert(node, PairInitTag);
    if (MODE == MODE_STANDARD) {
      do {
	node = put_trie(node, YAP_HeadOfTerm(t));
	t = YAP_Deref(YAP_TailOfTerm(t));
      } while (YAP_IsPairTerm(t));
    } else { // MODE_REVERSE
      YAP_Term *stack_list = stack_args;
      do {
	PUSH_DOWN(stack_args, YAP_HeadOfTerm(t), stack_vars);
	t = YAP_Deref(YAP_TailOfTerm(t));
      } while (YAP_IsPairTerm(t));
      while (STACK_NOT_EMPTY(stack_args, stack_list))
	node = put_trie(node, POP_UP(stack_args));
    }
    node = trie_node_check_insert(node, PairEndTag);
  } else if (YAP_IsApplTerm(t)) {
    YAP_Functor f = YAP_FunctorOfTerm(t);
    if (f == FunctorComma) {
      node = trie_node_check_insert(node, CommaInitTag);
      do {
	node = put_trie(node, YAP_ArgOfTerm(1, t));
	t = YAP_Deref(YAP_ArgOfTerm(2, t));
      } while (YAP_IsApplTerm(t) && YAP_FunctorOfTerm(t) == FunctorComma);
      node = put_trie(node, t);
      node = trie_node_check_insert(node, CommaEndTag);
    } else {
      int i;
      node = trie_node_check_insert(node, ApplTag | ((YAP_Term) f));
      for (i = 1; i <= YAP_ArityOfFunctor(f); i++)
	node = put_trie(node, YAP_ArgOfTerm(i, t));
    }
  } else 
    fprintf(stderr, "\nTries module: unknown type tag\n");
  
  return node;
}


static
YAP_Term get_trie(TrNode node, YAP_Term *stack_mark, TrNode *cur_node) {
  YAP_Term t = (YAP_Term) &t;

  while (TrNode_parent(node)) {
    t = TrNode_entry(node);
    if (YAP_IsVarTerm(t)) {
      int index = TrieVarIndex(t);
      if (index > max_index) {
	int i;
	stack_vars = &stack_vars_base[index + 1];
	if (stack_vars > stack_args + 1)
	  fprintf(stderr, "\nTries module: TERM_STACK full");
	for (i = index; i > max_index; i--)
	  stack_vars_base[i] = 0;
	max_index = index;
      }
      if (stack_vars_base[index]) {
	t = stack_vars_base[index];
      } else {
	t = YAP_MkVarTerm();
	stack_vars_base[index] = t;
      }
      PUSH_UP(stack_args, t, stack_vars);
    } else if (YAP_IsAtomTerm(t)) {
      PUSH_UP(stack_args, t, stack_vars);
    } else if (YAP_IsIntTerm(t)) {
      PUSH_UP(stack_args, t, stack_vars);
    } else if (YAP_IsPairTerm(t)) {
      if (t == PairEndTag) {
	if (MODE == MODE_STANDARD) {
	  t = YAP_MkAtomTerm(YAP_LookupAtom("[]"));
	  PUSH_UP(stack_args, t, stack_vars);
	  node = TrNode_parent(node);
	  t = get_trie(node, &stack_args[1], &node);
	} else { // MODE_REVERSE
	  node = TrNode_parent(node);
	  t = get_trie(node, stack_args, &node);
	}
	PUSH_UP(stack_args, t, stack_vars);
      } else if (t == PairInitTag) {
	YAP_Term t2;
	if (MODE == MODE_STANDARD) {
	  YAP_Term *stack_aux = stack_mark;
	  t = *stack_aux--;
	  while (STACK_NOT_EMPTY(stack_aux, stack_args)) {
	    t2 = *stack_aux--;
	    t = YAP_MkPairTerm(t2, t);
	  }
	  stack_args = stack_mark;
	} else { // MODE_REVERSE
	  t = YAP_MkAtomTerm(YAP_LookupAtom("[]"));
	  while (STACK_NOT_EMPTY(stack_args, stack_mark)) {
	    t2 = POP_DOWN(stack_args);
	    t = YAP_MkPairTerm(t2, t);
	  }
	}
	*cur_node = node;
	return t;
      } else if (t == CommaEndTag) {
	node = TrNode_parent(node);
	t = get_trie(node, stack_args, &node);
	PUSH_UP(stack_args, t, stack_vars);
      } else if (t == CommaInitTag) {
	YAP_Term *stack_aux = stack_mark;
	stack_aux--;
	while (STACK_NOT_EMPTY(stack_aux, stack_args)) {
	  t = YAP_MkApplTerm(FunctorComma, 2, stack_aux);
	  *stack_aux = t;
	  stack_aux--;
	}
	stack_args = stack_mark;
      	*cur_node = node;
	return t;
      } else if (t == FloatEndTag) {
	volatile double f;
	YAP_Term *p;
	p = (YAP_Term *) &f;
	node = TrNode_parent(node);
	*(p + 1) = TrNode_entry(node);
	node = TrNode_parent(node);
	*p = TrNode_entry(node);
	/* node = TrNode_parent(node); */
	t = YAP_MkFloatTerm(f);
	PUSH_UP(stack_args, t, stack_vars);
      } else if (t == FloatInitTag) {
      }
    } else if (ApplTag & t) {
      YAP_Functor f = (YAP_Functor)(~ApplTag & t);
      int arity = YAP_ArityOfFunctor(f);
      t = YAP_MkApplTerm(f, arity, &stack_args[1]);
      stack_args += arity;
      PUSH_UP(stack_args, t, stack_vars);
    } else
      fprintf(stderr, "\nTries module: unknown type tag\n");
    node = TrNode_parent(node);
  }
  *cur_node = node;
  return t;
}


static
void free_child_nodes(TrNode node) {
  if (IS_TRIE_HASH(node)) {
    TrNode *first_bucket, *bucket;
    TrHash hash = (TrHash) node;
    if (TrHash_next(hash)) {
      TrHash_previous(TrHash_next(hash)) = TrHash_previous(hash);
      TrHash_next(TrHash_previous(hash)) = TrHash_next(hash);
    } else 
      TrHash_next(TrHash_previous(hash)) = NULL;
    first_bucket = TrHash_buckets(hash);
    bucket = first_bucket + TrHash_num_buckets(hash);
    do {
      if (*--bucket)
	free_child_nodes(*bucket);
    } while (bucket != first_bucket);
    free_hash_buckets(first_bucket, TrHash_num_buckets(hash));
    free_trie_hash(hash);
    return;
  }
  if (TrNode_next(node))
    free_child_nodes(TrNode_next(node));
  if (TrNode_child(node))
    free_child_nodes(TrNode_child(node));
  free_trie_node(node);
  return;
}


static
void traverse_trie_usage(TrNode node, int depth) {
  if (IS_TRIE_HASH(node)) {
    TrNode *first_bucket, *bucket;
    TrHash hash;
    hash = (TrHash) node;
    first_bucket = TrHash_buckets(hash);
    bucket = first_bucket + TrHash_num_buckets(hash);
    do {
      if (*--bucket) {
        node = *bucket;
        traverse_trie_usage(node, depth);
      }
    } while (bucket != first_bucket);
    return;
  }

  TRIE_NODES++;
  if (TrNode_next(node))
    traverse_trie_usage(TrNode_next(node), depth);
  depth++;
  if (TrNode_child(node)) {
    traverse_trie_usage(TrNode_child(node), depth);
  } else {
    TRIE_ENTRIES++;
    TRIE_VIRTUAL_NODES+= depth;
  }
  return;
}


static
void traverse_trie(TrNode node, char *str, int str_index, int *arity) {
  YAP_Term t;
  int new_arity[100];

  if (IS_TRIE_HASH(node)) {
    TrNode *first_bucket, *bucket;
    TrHash hash;
    hash = (TrHash) node;
    first_bucket = TrHash_buckets(hash);
    bucket = first_bucket + TrHash_num_buckets(hash);
    do {
      if (*--bucket) {
        node = *bucket;
        memcpy(new_arity, arity, 100);
        traverse_trie(node, str, str_index, new_arity);
      }
    } while (bucket != first_bucket);
    return;
  }

  memcpy(new_arity, arity, 100);
  if (TrNode_next(node))
    traverse_trie(TrNode_next(node), str, str_index, new_arity);

  t = TrNode_entry(node);
  if (YAP_IsVarTerm(t)) {
    str_index += sprintf(& str[str_index], "VAR%ld", TrieVarIndex(t));
    while (arity[0]) {
      arity[arity[0]]--;
      if (arity[arity[0]] == 0) {
	str_index += sprintf(& str[str_index], ")");
	arity[0]--;
      } else {
	str_index += sprintf(& str[str_index], ",");
	break;
      }
    }
  } else if (YAP_IsAtomTerm(t)) {
    str_index += sprintf(& str[str_index], "%s", YAP_AtomName(YAP_AtomOfTerm(t)));
    while (arity[0]) {
      arity[arity[0]]--;
      if (arity[arity[0]] == 0) {
	str_index += sprintf(& str[str_index], ")");
	arity[0]--;
      } else {
	str_index += sprintf(& str[str_index], ",");
	break;
      }
    }
  } else if (YAP_IsIntTerm(t)) {
    str_index += sprintf(& str[str_index], "%ld", YAP_IntOfTerm(t));
    while (arity[0]) {
      arity[arity[0]]--;
      if (arity[arity[0]] == 0) {
	str_index += sprintf(& str[str_index], ")");
	arity[0]--;
      } else {
	str_index += sprintf(& str[str_index], ",");
	break;
      }
    }
  } else if (YAP_IsPairTerm(t)) {
    if (t == PairInitTag) {
      str_index += sprintf(& str[str_index], "[");
      arity[0]++;
      arity[arity[0]] = -1;
    } else if (t == CommaInitTag) {
      str_index += sprintf(& str[str_index], "(");
      arity[0]++;
      arity[arity[0]] = -1;
      /*
    } else if (t == FloatInitTag) {
      double f = 0.0;
      str_index += sprintf(& str[str_index], "%f", f);
      while (arity[0]) {
	arity[arity[0]]--;
	if (arity[arity[0]] == 0) {
	  str_index += sprintf(& str[str_index], ")");
	  arity[0]--;
	} else {
	  str_index += sprintf(& str[str_index], ",");
	  break;
	}
      }
      */
    } else {
      if (t == PairEndTag)
	str[str_index - 1] = ']';
      else // (t == CommaEndTag)
	str[str_index - 1] = ')';
      arity[0]--;
      while (arity[0]) {
	arity[arity[0]]--;
	if (arity[arity[0]] == 0) {
	  str_index += sprintf(& str[str_index], ")");
	  arity[0]--;
	} else {
	  str_index += sprintf(& str[str_index], ",");
	  break;
	}
      }
      if (TrNode_child(node)) {
	traverse_trie(TrNode_child(node), str, str_index, arity);
      } else {
	str[str_index] = 0;
	fprintf(stdout, "%s\n", str);
      }
      str[str_index - 1] = ',';
      return;
    }
  } else if (ApplTag & t) {
    str_index += sprintf(& str[str_index], "%s(", YAP_AtomName(YAP_NameOfFunctor((YAP_Functor)(~ApplTag & t))));
    arity[0]++;
    arity[arity[0]] = YAP_ArityOfFunctor((YAP_Functor)(~ApplTag & t));
  } else
    fprintf(stderr, "\nTries module: unknown type tag\n");

  if (TrNode_child(node)) {
    traverse_trie(TrNode_child(node), str, str_index, arity);
  } else {
    str[str_index] = 0;
    fprintf(stdout, "%s\n", str);
  }

  return;
}
