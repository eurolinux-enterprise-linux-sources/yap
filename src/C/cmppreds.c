/*************************************************************************
*									 *
*	 YAP Prolog 							 *
*									 *
*	Yap Prolog was developed at NCCUP - Universidade do Porto	 *
*									 *
* Copyright L.Damas, V.S.Costa and Universidade do Porto 1985-1997	 *
*									 *
**************************************************************************
*									 *
* File:		cmppreds.c						 *
* Last rev:								 *
* mods:									 *
* comments:	comparing two prolog terms				 *
*									 *
*************************************************************************/
#ifdef SCCS
static char     SccsId[] = "%W% %G%";
#endif

#include "Yap.h"
#include "Yatom.h"
#include "Heap.h"
#include "eval.h"
#if HAVE_STRING_H
#include <string.h>
#endif
#include <wchar.h>

STATIC_PROTO(Int compare, (Term, Term));
STATIC_PROTO(Int p_compare, (void));
STATIC_PROTO(Int p_acomp, (void));
STATIC_PROTO(Int a_eq, (Term,Term));
STATIC_PROTO(Int a_dif, (Term,Term));
STATIC_PROTO(Int a_gt, (Term, Term));
STATIC_PROTO(Int a_ge, (Term,Term));
STATIC_PROTO(Int a_lt, (Term,Term));
STATIC_PROTO(Int a_le, (Term,Term));
STATIC_PROTO(Int a_noteq, (Term,Term));
STATIC_PROTO(Int a_gen_lt, (Term,Term));
STATIC_PROTO(Int a_gen_le, (Term,Term));
STATIC_PROTO(Int a_gen_gt, (Term,Term));
STATIC_PROTO(Int a_gen_ge, (Term,Term));

#define rfloat(X)	( X > 0.0 ? 1 : ( X == 0.0 ? 0 : -1))

static int
cmp_atoms(Atom a1, Atom a2)
{
  if (IsWideAtom(a1)) {
    if (IsWideAtom(a2)) {
      return wcscmp((wchar_t *)RepAtom(a1)->StrOfAE,(wchar_t *)RepAtom(a2)->StrOfAE);
    } else {
      /* The standard does not seem to have nothing on this */
      unsigned char *s1 = (unsigned char *)RepAtom(a1)->StrOfAE;
      wchar_t *s2 = (wchar_t *)RepAtom(a2)->StrOfAE;

      while (*s1 == *s2) {
	if (!*s1) return 0;
      }
      return *s1-*s2;
    }
  } else if (IsWideAtom(a2)) {
    /* The standard does not seem to have nothing on this */
    wchar_t *s1 = (wchar_t *)RepAtom(a1)->StrOfAE;
    unsigned char *s2 = (unsigned char *)RepAtom(a2)->StrOfAE;

    while (*s1 == *s2) {
      if (!*s1) return 0;
    }
    return *s1-*s2;
  } else {
    return strcmp(RepAtom(a1)->StrOfAE,RepAtom(a2)->StrOfAE);
  }
}

static int compare_complex(register CELL *pt0, register CELL *pt0_end, register
		   CELL *pt1)
{

  register CELL **to_visit = (CELL **)H;
  register int out = 0;

 loop:
  while (pt0 < pt0_end) {
    register CELL d0, d1;
    ++ pt0;
    ++ pt1;
    d0 = Derefa(pt0);
    d1 = Derefa(pt1);
    if (IsVarTerm(d0)) {
      if (IsVarTerm(d1)) {
	out = Signed(d0) - Signed(d1);
	if (out) goto done;
      }
      else {
	out = -1;
	goto done;
      }
    } else if (IsVarTerm(d1)) {
      out = 1;
      goto done;
    } else {
      if (d0 == d1) continue;
      else if (IsAtomTerm(d0)) {
	if (IsAtomTerm(d1))
	  out = cmp_atoms(AtomOfTerm(d0), AtomOfTerm(d1));
	else if (IsPrimitiveTerm(d1))
	  out = 1;
	else out = -1;
	/* I know out must be != 0 */
	goto done;
      }
      else if (IsIntTerm(d0)) {
	if (IsIntTerm(d1))
	  out = IntOfTerm(d0) - IntOfTerm(d1);
	else if (IsFloatTerm(d1)) {
	  out = 1;
	} else if (IsLongIntTerm(d1)) {
	  out = IntOfTerm(d0) - LongIntOfTerm(d1);
#ifdef USE_GMP
	} else if (IsBigIntTerm(d1)) {
	  MP_INT *b1 = Yap_BigIntOfTerm(d1);
	  if (!mpz_size(b1)) {
	    out = -1; 
	  } else {
	    out = -mpz_cmp_si(b1, IntOfTerm(d0));
	  }
#endif
	} else if (IsRefTerm(d1))
		out = 1 ;
	else out = -1;
	if (out != 0)
	  goto done;
      } else if (IsFloatTerm(d0)) {
	if (IsFloatTerm(d1)){
	  out = rfloat(FloatOfTerm(d0) - FloatOfTerm(d1));
	} else if (IsRefTerm(d1)) {
	  out = 1;
	} else {
	  out = -1;
	}
	if (out != 0)
	  goto done;
      } else if (IsLongIntTerm(d0)) {
	if (IsIntTerm(d1))
	  out = LongIntOfTerm(d0) - IntOfTerm(d1);
	else if (IsFloatTerm(d1)) {
	  out = 1;
	} else if (IsLongIntTerm(d1)) {
	  out = LongIntOfTerm(d0) - LongIntOfTerm(d1);
#ifdef USE_GMP
	} else if (IsBigIntTerm(d1)) {
	  MP_INT *b1 = Yap_BigIntOfTerm(d1);
	  if (!mpz_size(b1)) {
	    out = -1; 
	  } else {
	    out = -mpz_cmp_si(b1, LongIntOfTerm(d0));
	  }
#endif
	} else if (IsRefTerm(d1)) {
	  out = 1 ;
	} else {
	  out = -1;
	}
	if (out != 0)
	  goto done;
      }
#ifdef USE_GMP
      else if (IsBigIntTerm(d0)) {
	MP_INT *b0 = Yap_BigIntOfTerm(d0);

	if (!mpz_size(b0)) {
	  if (IsBigIntTerm(d1)) {
	    MP_INT *b1 = Yap_BigIntOfTerm(d1);
	    out = b0-b1;
	  } else {
	    out = 1;
	  }
	} else if (IsIntTerm(d1))
	  out = mpz_cmp_si(b0, IntOfTerm(d1));
	else if (IsFloatTerm(d1)) {
	  out = 1;
	} else if (IsLongIntTerm(d1))
	  out = mpz_cmp_si(b0, LongIntOfTerm(d1));
	else if (IsBigIntTerm(d1)) {
	  MP_INT *b1 = Yap_BigIntOfTerm(d1);

	  if (!mpz_size(b1)) {
	    out = -1; 
	  } else {
	    out = mpz_cmp(b0, b1);
	  }
	} else if (IsRefTerm(d1))
	  out = 1 ;
	else out = -1;
	if (out != 0)
	  goto done;
      }
#endif
      else if (IsPairTerm(d0)) {
	if (!IsPairTerm(d1)) {
	  if (IsApplTerm(d1)) {
	    Functor f = FunctorOfTerm(d1);
	    if (IsExtensionFunctor(f))
	      out = 1;
	    else if (!(out = 2-ArityOfFunctor(f)))
	       out = strcmp(".",RepAtom(NameOfFunctor(f))->StrOfAE);
	  } else out = 1;
	  goto done;
	}
#ifdef RATIONAL_TREES
	to_visit[0] = pt0;
	to_visit[1] = pt0_end;
	to_visit[2] = pt1;
	to_visit[3] = (CELL *)*pt0;
	to_visit += 4;
	*pt0 = d1;
#else
	/* store the terms to visit */
	if (pt0 < pt0_end) {
	  to_visit[0] = pt0;
	  to_visit[1] = pt0_end;
	  to_visit[2] = pt1;
	  to_visit += 3;
	}
#endif
	pt0 = RepPair(d0) - 1;
	pt0_end = RepPair(d0) + 1;
	pt1 = RepPair(d1) - 1;
	continue;
      }
      else if (IsRefTerm(d0)) {
	if (IsRefTerm(d1))
	  out = Unsigned(RefOfTerm(d1)) -
	    Unsigned(RefOfTerm(d0));
	else out = -1;
	goto done;
      } else if (IsApplTerm(d0)) {
	register Functor f;
	register CELL *ap2, *ap3;
	if (!IsApplTerm(d1)) {
	  out = 1 ;
	  goto done;
	} else {
	  /* store the terms to visit */
	  Functor f2;
	  ap2 = RepAppl(d0);
	  ap3 = RepAppl(d1);
	  f = (Functor)(*ap2);
	  if (IsExtensionFunctor(f)) {
	    out = 1;
	    goto done;
	  }
	  f2 = (Functor)(*ap3);	
	  if (IsExtensionFunctor(f2)) {
	    out = -1;
	    goto done;
	  }
	  /* compare functors */
	  if (f != (Functor)*ap3) {
	    if (!(out = ArityOfFunctor(f)-ArityOfFunctor(f2)))
	       out = cmp_atoms(NameOfFunctor(f), NameOfFunctor(f2));
	    goto done;
	  }
#ifdef RATIONAL_TREES
	to_visit[0] = pt0;
	to_visit[1] = pt0_end;
	to_visit[2] = pt1;
	to_visit[3] = (CELL *)*pt0;
	to_visit += 4;
	*pt0 = d1;
#else
	  /* store the terms to visit */
	  if (pt0 < pt0_end) {
	    to_visit[0] = pt0;
	    to_visit[1] = pt0_end;
	    to_visit[2] = pt1;
	    to_visit += 3;
	  }
#endif
	  d0 = ArityOfFunctor(f);
	  pt0 = ap2;
	  pt0_end = ap2 + d0;
	  pt1 = ap3;
	  continue;
	}
      }

    }
  }
  /* Do we still have compound terms to visit */
  if (to_visit > (CELL **)H) {
#ifdef RATIONAL_TREES
    to_visit -= 4;
    pt0 = to_visit[0];
    pt0_end = to_visit[1];
    pt1 = to_visit[2];
    *pt0 = (CELL)to_visit[3];
#else
    to_visit -= 3;
    pt0 = to_visit[0];
    pt0_end = to_visit[1];
    pt1 = to_visit[2];
#endif
    goto loop;
  }

 done:
  /* failure */
#ifdef RATIONAL_TREES
  while (to_visit > (CELL **)H) {
    to_visit -= 4;
    pt0 = to_visit[0];
    pt0_end = to_visit[1];
    pt1 = to_visit[2];
    *pt0 = (CELL)to_visit[3];
  }
#endif
  return(out);
}

inline static Int 
compare(Term t1, Term t2) /* compare terms t1 and t2	 */
{

  if (t1 == t2)
    return 0;
  if (IsVarTerm(t1)) {
    if (IsVarTerm(t2))
      return Signed(t1) - Signed(t2);
    return -1;
  } else if (IsVarTerm(t2)) {
    /* get rid of variables */
    return 1;
  }
  if (IsAtomOrIntTerm(t1)) {
    if (IsAtomTerm(t1)) {
      if (IsAtomTerm(t2))
	return cmp_atoms(AtomOfTerm(t1),AtomOfTerm(t2));
      if (IsPrimitiveTerm(t2))
	return 1;
      return -1;
    } else {
      if (IsIntTerm(t2))
	return IntOfTerm(t1) - IntOfTerm(t2);
      if (IsFloatTerm(t2)) {
	return 1;
      }
      if (IsLongIntTerm(t2)) {
	return IntOfTerm(t1) - LongIntOfTerm(t2);
      }
#ifdef USE_GMP
      if (IsBigIntTerm(t2)) {
	MP_INT *b1 = Yap_BigIntOfTerm(t2);
	if (!mpz_size(b1)) {
	  return -1; 
	} else {
	  return -mpz_cmp_si(b1,IntOfTerm(t1));
	}
      }
#endif
      if (IsRefTerm(t2))
	return 1;
      return -1;
    }
  } else if (IsPairTerm(t1)) {
    if (IsApplTerm(t2)) {
      Functor f = FunctorOfTerm(t2);
      if (IsExtensionFunctor(f))
	return 1;
      else {
	int out;
	if (!(out = 2-ArityOfFunctor(f)))
	  out = strcmp(".",RepAtom(NameOfFunctor(f))->StrOfAE);
	return(out);
      }
    }
    if (IsPairTerm(t2)) {
      return(compare_complex(RepPair(t1)-1,
			     RepPair(t1)+1,
			     RepPair(t2)-1));
    }
    else return 1;
  } else {
    /* compound term */
    Functor fun1 = FunctorOfTerm(t1);

    if (IsExtensionFunctor(fun1)) {
      /* float, long, big, dbref */
      switch ((CELL)fun1) {
      case double_e:
	{
	  if (IsFloatTerm(t2))
	    return(rfloat(FloatOfTerm(t1) - FloatOfTerm(t2)));
	  if (IsRefTerm(t2))
	    return 1;
	  return -1;
	}
      case long_int_e:
	{
	  if (IsIntTerm(t2))
	    return LongIntOfTerm(t1) - IntOfTerm(t2);
	  if (IsFloatTerm(t2)) {
	    return 1;
	  }
	  if (IsLongIntTerm(t2))
	    return LongIntOfTerm(t1) - LongIntOfTerm(t2);
#ifdef USE_GMP
	  if (IsBigIntTerm(t2)) {
	    MP_INT *b1 = Yap_BigIntOfTerm(t2);
	    if (!mpz_size(b1)) {
	      return -1; 
	    } else {
	      return -mpz_cmp_si(b1, LongIntOfTerm(t1));
	    }
	  }
#endif
	  if (IsRefTerm(t2))
	    return 1;
	  return -1;
	}
#ifdef USE_GMP
      case big_int_e:
	{
	  MP_INT *b0 = Yap_BigIntOfTerm(t1);

	  if (!mpz_size(b0)) {
	    if (IsBigIntTerm(t2)) {
	      MP_INT *b1 = Yap_BigIntOfTerm(t2);
	      return b0-b1;
	    } else {
	      return 1;
	    }
	  } else if (IsIntTerm(t2))
	    return mpz_cmp_si(Yap_BigIntOfTerm(t1), IntOfTerm(t2));
	  if (IsFloatTerm(t2)) {
	    return 1;
	  }
	  if (IsLongIntTerm(t2))
	    return mpz_cmp_si(Yap_BigIntOfTerm(t1), LongIntOfTerm(t2));
	  if (IsBigIntTerm(t2)) {
	    MP_INT *b1 = Yap_BigIntOfTerm(t2);

	    if (!mpz_size(b1)) {
	      return -1; 
	    } else {
	      return mpz_cmp(b0, b1);
	    }
	  }
	  if (IsRefTerm(t2))
	    return 1;
	  return -1;
	}
#endif
      case db_ref_e:
	if (IsRefTerm(t2))
	  return Unsigned(RefOfTerm(t2)) -
	    Unsigned(RefOfTerm(t1));
	return -1;
      }
    }
    if (!IsApplTerm(t2)) {
      if (IsPairTerm(t2)) {
	Int out;
	Functor f = FunctorOfTerm(t1);

	if (!(out = ArityOfFunctor(f))-2)
	  out = strcmp(RepAtom(NameOfFunctor(f))->StrOfAE,".");
	return out;
      }
      return 1;
    } else {
      Functor fun2 = FunctorOfTerm(t2);
      Int r;

      if (IsExtensionFunctor(fun2)) {
	return 1;
      }
      r = ArityOfFunctor(fun1) - ArityOfFunctor(fun2);
      if (r)
	return r;
      r = cmp_atoms(NameOfFunctor(fun1), NameOfFunctor(fun2));
      if (r)
	return r;
      else
	return(compare_complex(RepAppl(t1),
			       RepAppl(t1)+ArityOfFunctor(fun1),
			       RepAppl(t2)));
    }
  }
}

int Yap_compare_terms(CELL d0, CELL d1)
{
  return (compare(Deref(d0),Deref(d1)));
}

static Int 
p_compare(void)
{				/* compare(?Op,?T1,?T2)	 */
  Int             r = compare(Deref(ARG2), Deref(ARG3));
  Atom            p;

  if (r < 0)
    p = AtomLT;
  else if (r > 0)
    p = AtomGT;
  else
    p = AtomEQ;
  return Yap_unify_constant(ARG1, MkAtomTerm(p));
}

inline static int
int_cmp(Int dif)
{
    if (dif < 0)
      return(Yap_unify_constant(ARG1,MkAtomTerm(AtomLT)));
    else if (dif > 0)
      return(Yap_unify_constant(ARG1,MkAtomTerm(AtomGT)));
    else
      return(Yap_unify_constant(ARG1,MkAtomTerm(AtomEQ)));
}

inline static int
flt_cmp(Float dif)
{
    if (dif < 0.0)
      return(Yap_unify_constant(ARG1,MkAtomTerm(AtomLT)));
    else if (dif > 0.0)
      return(Yap_unify_constant(ARG1,MkAtomTerm(AtomGT)));
    else
      return(Yap_unify_constant(ARG1,MkAtomTerm(AtomEQ)));
}


static Int 
p_acomp(void)
{				/* $a_compare(?R,+X,+Y) */
  register blob_type  bt1;
  Term t1 = Deref(ARG1);
  Term t2 = Deref(ARG2);
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "=:=/2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t2, "=:=/2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2)) {
    return(flt_cmp(FloatOfTerm(t1)-FloatOfTerm(t2)));
  }
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2)) {
    return(int_cmp(IntegerOfTerm(t1)-IntegerOfTerm(t2)));
  }
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(int_cmp(v1.Int-v2.Int));
      case double_e:
	return(flt_cmp(v1.Int-v2.dbl));
#ifdef USE_GMP
      case big_int_e:
	return(int_cmp(-mpz_cmp_si(v2.big,v1.Int)));
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(flt_cmp(v1.dbl-v2.Int));
      case double_e:
	return(flt_cmp(v1.dbl-v2.dbl));
#ifdef USE_GMP
      case big_int_e:
	return(flt_cmp(v1.dbl-mpz_get_d(v2.big)));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(int_cmp(mpz_cmp_si(v1.big,v2.Int)));
      case double_e:
	return(flt_cmp(mpz_get_d(v1.big)-v2.dbl));
      case big_int_e:
	return(int_cmp(mpz_cmp(v1.big,v2.big)));
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}

static Int 
a_eq(Term t1, Term t2)
{				/* A =:= B		 */
  blob_type bt1;
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "=:=/2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t2, "=:=/2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2))
    return (FloatOfTerm(t1) == FloatOfTerm(t2));
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2))
    return (IntegerOfTerm(t1) == IntegerOfTerm(t2));
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.Int == v2.Int);
      case double_e:
	return(v1.Int == v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(-mpz_cmp_si(v2.big,v1.Int) == 0);
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.dbl == v2.Int);
      case double_e:
	return(v1.dbl == v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(v1.dbl == mpz_get_d(v2.big));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(mpz_cmp_si(v1.big,v2.Int) == 0);
      case double_e:
	return(mpz_get_d(v1.big) == v2.dbl);
      case big_int_e:
	return(mpz_cmp(v1.big,v2.big) == 0);
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}

static Int 
a_dif(Term t1, Term t2)
{				/* A =\\= B		 */
  blob_type bt1;
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "=\\=/2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t2, "=\\=/2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2))
    return (FloatOfTerm(t1) != FloatOfTerm(t2));
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2))
    return (IntegerOfTerm(t1) != IntegerOfTerm(t2));
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.Int != v2.Int);
      case double_e:
	return(v1.Int != v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(-mpz_cmp_si(v2.big,v1.Int) != 0);
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.dbl != v2.Int);
      case double_e:
	return(v1.dbl != v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(v1.dbl != mpz_get_d(v2.big));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(mpz_cmp_si(v1.big,v2.Int) != 0);
      case double_e:
	return(mpz_get_d(v1.big) != v2.dbl);
      case big_int_e:
	return(mpz_cmp(v1.big,v2.big) != 0);
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}

static Int 
a_gt(Term t1, Term t2)
{				/* A > B		 */
  blob_type bt1;
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, ">/2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t2, ">/2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2))
    return (FloatOfTerm(t1) > FloatOfTerm(t2));
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2))
    return (IntegerOfTerm(t1) > IntegerOfTerm(t2));
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.Int > v2.Int);
      case double_e:
	return(v1.Int > v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(-mpz_cmp_si(v2.big,v1.Int) > 0);
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.dbl > v2.Int);
      case double_e:
	return(v1.dbl > v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(v1.dbl > mpz_get_d(v2.big));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(mpz_cmp_si(v1.big,v2.Int) > 0);
      case double_e:
	return(mpz_get_d(v1.big) > v2.dbl);
      case big_int_e:
	return(mpz_cmp(v1.big,v2.big) > 0);
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}

static Int 
a_ge(Term t1, Term t2)
{				/* A >= B		 */
  blob_type bt1;
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, ">=/2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t1, ">=/2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2))
    return (FloatOfTerm(t1) >= FloatOfTerm(t2));
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2))
    return (IntegerOfTerm(t1) >= IntegerOfTerm(t2));
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.Int >= v2.Int);
      case double_e:
	return(v1.Int >= v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(-mpz_cmp_si(v2.big,v1.Int) >= 0);
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.dbl >= v2.Int);
      case double_e:
	return(v1.dbl >= v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(v1.dbl >= mpz_get_d(v2.big));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(mpz_cmp_si(v1.big,v2.Int) >= 0);
      case double_e:
	return(mpz_get_d(v1.big) >= v2.dbl);
      case big_int_e:
	return(mpz_cmp(v1.big,v2.big) >= 0);
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}

static Int 
a_lt(Term t1, Term t2)
{				/* A < B       */
  blob_type bt1;
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "</2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t2, "</2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2))
    return (FloatOfTerm(t1) < FloatOfTerm(t2));
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2))
    return (IntegerOfTerm(t1) < IntegerOfTerm(t2));
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.Int < v2.Int);
      case double_e:
	return(v1.Int < v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(-mpz_cmp_si(v2.big,v1.Int) < 0);
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.dbl < v2.Int);
      case double_e:
	return(v1.dbl < v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(v1.dbl < mpz_get_d(v2.big));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(mpz_cmp_si(v1.big,v2.Int) < 0);
      case double_e:
	return(mpz_get_d(v1.big) < v2.dbl);
      case big_int_e:
	return(mpz_cmp(v1.big,v2.big) < 0);
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}

static Int 
a_le(Term t1, Term t2)
{				/* A <= B */
  blob_type bt1;
  union arith_ret v1;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "=</2");
    return(FALSE);
  }
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR, t2, "=</2");
    return(FALSE);
  }
  if (IsFloatTerm(t1) && IsFloatTerm(t2))
    return (FloatOfTerm(t1) <= FloatOfTerm(t2));
  if (IsIntegerTerm(t1) && IsIntegerTerm(t2))
    return (IntegerOfTerm(t1) <= IntegerOfTerm(t2));
  bt1 = Yap_Eval(t1, &v1);
  switch (bt1) {
  case  long_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.Int <= v2.Int);
      case double_e:
	return(v1.Int <= v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(-mpz_cmp_si(v2.big,v1.Int) <= 0);
#endif
      default:
	return(FALSE);
      }
    }
  case double_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(v1.dbl <= v2.Int);
      case double_e:
	return(v1.dbl <= v2.dbl);
#ifdef USE_GMP
      case big_int_e:
	return(v1.dbl <= mpz_get_d(v2.big));
#endif
      default:
	return(FALSE);
      }
    }
#ifdef USE_GMP
  case big_int_e:
    {
      union arith_ret v2;
      blob_type bt2 = Yap_Eval(t2, &v2);

      switch (bt2) {
      case  long_int_e:
	return(mpz_cmp_si(v1.big,v2.Int) <= 0);
      case double_e:
	return(mpz_get_d(v1.big) <= v2.dbl);
      case big_int_e:
	return(mpz_cmp(v1.big,v2.big) <= 0);
      default:
	return(FALSE);
      }
    }
#endif
  default:
    return(FALSE);
  }
}


static Int 
a_noteq(Term t1, Term t2)
{
  return (compare(t1, t2) != 0);
}

static Int 
a_gen_lt(Term t1, Term t2)
{
  return (compare(t1, t2) < 0);
}

static Int 
a_gen_le(Term t1, Term t2)
{
  return (compare(t1, t2) <= 0);
}

static Int 
a_gen_gt(Term t1, Term t2)
{
  return (compare(t1, t2) > 0);
}

static Int 
a_gen_ge(Term t1, Term t2)
{
  return (compare(t1, t2) >= 0);
}


void 
Yap_InitCmpPreds(void)
{
  Yap_InitCmpPred("=:=", 2, a_eq, SafePredFlag | BinaryTestPredFlag);
  Yap_InitCmpPred("=\\=", 2, a_dif, SafePredFlag | BinaryTestPredFlag);
  Yap_InitCmpPred(">", 2, a_gt,  SafePredFlag | BinaryTestPredFlag);
  Yap_InitCmpPred("=<", 2, a_le, SafePredFlag | BinaryTestPredFlag);
  Yap_InitCmpPred("<", 2, a_lt, SafePredFlag | BinaryTestPredFlag);
  Yap_InitCmpPred(">=", 2, a_ge, SafePredFlag | BinaryTestPredFlag);
  Yap_InitCPred("$a_compare", 3, p_acomp, TestPredFlag | SafePredFlag|HiddenPredFlag);
  Yap_InitCmpPred("\\==", 2, a_noteq, BinaryTestPredFlag | SafePredFlag);
  Yap_InitCmpPred("@<", 2, a_gen_lt, BinaryTestPredFlag | SafePredFlag);
  Yap_InitCmpPred("@=<", 2, a_gen_le, BinaryTestPredFlag | SafePredFlag);
  Yap_InitCmpPred("@>", 2, a_gen_gt, BinaryTestPredFlag | SafePredFlag);
  Yap_InitCmpPred("@>=", 2, a_gen_ge, BinaryTestPredFlag | SafePredFlag);
  Yap_InitCPred("compare", 3, p_compare, TestPredFlag | SafePredFlag);
}
