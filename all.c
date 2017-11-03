/*
 *  R : A Computer Langage for Statistical Data Analysis
 *  Copyright (C) 1995, 1996  Robert Gentleman and Ross Ihaka
 *  Copyright (C) 1998-2017   The R Core Team.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/


 *  Matching and Partial Matching for Strings
 *
 *  In theory all string matching code should be placed in this file
 *  At present there are still a couple of rogue matchers about.
 *
 *
 *  psmatch(char *, char *, int);
 *
 *  This code will perform partial matching for list tags.  When
 *  exact is 1, and exact match is required (typically after ...)
 *  otherwise partial matching is performed.
 *
 *  Examples:
 *
 *	psmatch("aaa", "aaa", 0) -> 1
 *	psmatch("aaa", "aa", 0) -> 1
 *	psmatch("aa", "aaa", 0) -> 0
 *
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include "Defn.h"


/* used in subscript.c and subassign.c */
Rboolean NonNullStringMatch(SEXP s, SEXP t)
{
    /* "" or NA string matches nothing */
    if (s == NA_STRING || t == NA_STRING) return FALSE;
    if (CHAR(s)[0] && CHAR(t)[0] && Seql(s, t))
	return TRUE;
    else
	return FALSE;
}

/* currently unused outside this file */
Rboolean psmatch(const char *f, const char *t, Rboolean exact)
{
    if (exact)
	return (Rboolean)!strcmp(f, t);
    /* else */
    while (*t) {
	if (*t != *f)   return FALSE;
	t++;
	f++;
    }
    return TRUE;
}


/* Matching formals and arguments */

/* Are these are always native charset? */
Rboolean pmatch(SEXP formal, SEXP tag, Rboolean exact)
{
    const char *f, *t;
    const void *vmax = vmaxget();
    switch (TYPEOF(formal)) {
    case SYMSXP:
	f = CHAR(PRINTNAME(formal));
	break;
    case CHARSXP:
	f = CHAR(formal);
	break;
    case STRSXP:
	f = translateChar(STRING_ELT(formal, 0));
	break;
    default:
	goto fail;
    }
    switch(TYPEOF(tag)) {
    case SYMSXP:
	t = CHAR(PRINTNAME(tag));
	break;
    case CHARSXP:
	t = CHAR(tag);
	break;
    case STRSXP:
	t = translateChar(STRING_ELT(tag, 0));
	break;
    default:
	goto fail;
    }
    Rboolean res = psmatch(f, t, exact);
    vmaxset(vmax);
    return res;
 fail:
    error(_("invalid partial string match"));
    return FALSE;/* for -Wall */
}


/* Destructively Extract A Named List Element. */
/* Returns the first partially matching tag found. */
/* Pattern is a C string. */

static SEXP matchPar_int(const char *tag, SEXP *list, Rboolean exact)
{
    if (*list == R_NilValue)
	return R_MissingArg;
    else if (TAG(*list) != R_NilValue &&
	     psmatch(tag, CHAR(PRINTNAME(TAG(*list))), exact)) {
	SEXP s = *list;
	*list = CDR(*list);
	return CAR(s);
    }
    else {
	SEXP last = *list;
	SEXP next = CDR(*list);
	while (next != R_NilValue) {
	    if (TAG(next) != R_NilValue &&
		psmatch(tag, CHAR(PRINTNAME(TAG(next))), exact)) {
		SETCDR(last, CDR(next));
		return CAR(next);
	    }
	    else {
		last = next;
		next = CDR(next);
	    }
	}
	return R_MissingArg;
    }
}

/* unused outside this file */
SEXP attribute_hidden matchPar(const char *tag, SEXP * list)
{
    return matchPar_int(tag, list, FALSE);
}



/* Destructively Extract A Named List Element. */
/* Returns the first partially matching tag found. */
/* Pattern is a symbol. */

SEXP attribute_hidden matchArg(SEXP tag, SEXP * list)
{
    return matchPar(CHAR(PRINTNAME(tag)), list);
}


/* Destructively Extract A Named List Element. */
/* Returns the first exactly matching tag found. */
/* Pattern is a symbol. */

SEXP attribute_hidden matchArgExact(SEXP tag, SEXP * list)
{
      return matchPar_int(CHAR(PRINTNAME(tag)), list, TRUE);
}


/* Match the supplied arguments with the formals and */
/* return the matched arguments in actuals. */

#define ARGUSED(x) LEVELS(x)
#define SET_ARGUSED(x,v) SETLEVELS(x,v)


/* We need to leave 'supplied' unchanged in case we call UseMethod */
/* MULTIPLE_MATCHES was added by RI in Jan 2005 but never activated:
   code in R-2-8-branch */

SEXP attribute_hidden matchArgs(SEXP formals, SEXP supplied, SEXP call)
{
    Rboolean seendots;
    int i, arg_i = 0;
    SEXP f, a, b, dots, actuals;

    actuals = R_NilValue;
    for (f = formals ; f != R_NilValue ; f = CDR(f), arg_i++) {
	/* CONS_NR is used since argument lists created here are only
	   used internally and so should not increment reference
	   counts */
	actuals = CONS_NR(R_MissingArg, actuals);
	SET_MISSING(actuals, 1);
    }
    /* We use fargused instead of ARGUSED/SET_ARGUSED on elements of
       formals to avoid modification of the formals SEXPs.  A gc can
       cause matchArgs to be called from finalizer code, resulting in
       another matchArgs call with the same formals.  In R-2.10.x, this
       corrupted the ARGUSED data of the formals and resulted in an
       incorrect "formal argument 'foo' matched by multiple actual
       arguments" error.
     */
    int fargused[arg_i ? arg_i : 1]; // avoid undefined behaviour
    memset(fargused, 0, sizeof(fargused));

    for(b = supplied; b != R_NilValue; b = CDR(b)) SET_ARGUSED(b, 0);

    PROTECT(actuals);

    /* First pass: exact matches by tag */
    /* Grab matched arguments and check */
    /* for multiple exact matches. */

    f = formals;
    a = actuals;
    arg_i = 0;
    while (f != R_NilValue) {
      SEXP ftag = TAG(f);
      const char *ftag_name = CHAR(PRINTNAME(ftag));
      if (ftag != R_DotsSymbol && ftag != R_NilValue) {
	    for (b = supplied, i = 1; b != R_NilValue; b = CDR(b), i++) {
	      SEXP btag = TAG(b);
	      if (btag != R_NilValue) {
		  const char *btag_name = CHAR(PRINTNAME(btag));
		  if (streql( ftag_name, btag_name )) {
		      if (fargused[arg_i] == 2)
			  errorcall(call,
	                      _("formal argument \"%s\" matched by multiple actual arguments"),
	                      CHAR(PRINTNAME(TAG(f))));
		      if (ARGUSED(b) == 2)
			  errorcall(call,
	                      _("argument %d matches multiple formal arguments"),
                              i);
		      SETCAR(a, CAR(b));
		      if(CAR(b) != R_MissingArg) SET_MISSING(a, 0);
		      SET_ARGUSED(b, 2);
		      fargused[arg_i] = 2;
		  }
	      }
	    }
	}
	f = CDR(f);
	a = CDR(a);
        arg_i++;
    }

    /* Second pass: partial matches based on tags */
    /* An exact match is required after first ... */
    /* The location of the first ... is saved in "dots" */

    dots = R_NilValue;
    seendots = FALSE;
    f = formals;
    a = actuals;
    arg_i = 0;
    while (f != R_NilValue) {
	if (fargused[arg_i] == 0) {
	    if (TAG(f) == R_DotsSymbol && !seendots) {
		/* Record where ... value goes */
		dots = a;
		seendots = TRUE;
	    } else {
		for (b = supplied, i = 1; b != R_NilValue; b = CDR(b), i++) {
		    if (ARGUSED(b) != 2 && TAG(b) != R_NilValue &&
			pmatch(TAG(f), TAG(b), seendots)) {
			if (ARGUSED(b))
			    errorcall(call,
				_("argument %d matches multiple formal arguments"), i);
			if (fargused[arg_i] == 1)
			    errorcall(call,
				_("formal argument \"%s\" matched by multiple actual arguments"),
				CHAR(PRINTNAME(TAG(f))));
			if (R_warn_partial_match_args) {
			    warningcall(call,
					_("partial argument match of '%s' to '%s'"),
					CHAR(PRINTNAME(TAG(b))),
					CHAR(PRINTNAME(TAG(f))) );
			}
			SETCAR(a, CAR(b));
			if (CAR(b) != R_MissingArg) SET_MISSING(a, 0);
			SET_ARGUSED(b, 1);
			fargused[arg_i] = 1;
		    }
		}
	    }
	}
	f = CDR(f);
	a = CDR(a);
        arg_i++;
    }

    /* Third pass: matches based on order */
    /* All args specified in tag=value form */
    /* have now been matched.  If we find ... */
    /* we gobble up all the remaining args. */
    /* Otherwise we bind untagged values in */
    /* order to any unmatched formals. */

    f = formals;
    a = actuals;
    b = supplied;
    seendots = FALSE;

    while (f != R_NilValue && b != R_NilValue && !seendots) {
	if (TAG(f) == R_DotsSymbol) {
	    /* Skip ... matching until all tags done */
	    seendots = TRUE;
	    f = CDR(f);
	    a = CDR(a);
	} else if (CAR(a) != R_MissingArg) {
	    /* Already matched by tag */
	    /* skip to next formal */
	    f = CDR(f);
	    a = CDR(a);
	} else if (ARGUSED(b) || TAG(b) != R_NilValue) {
	    /* This value used or tagged , skip to next value */
	    /* The second test above is needed because we */
	    /* shouldn't consider tagged values for positional */
	    /* matches. */
	    /* The formal being considered remains the same */
	    b = CDR(b);
	} else {
	    /* We have a positional match */
	    SETCAR(a, CAR(b));
	    if(CAR(b) != R_MissingArg) SET_MISSING(a, 0);
	    SET_ARGUSED(b, 1);
	    b = CDR(b);
	    f = CDR(f);
	    a = CDR(a);
	}
    }

    if (dots != R_NilValue) {
	/* Gobble up all unused actuals */
	SET_MISSING(dots, 0);
	i = 0;
	for(a = supplied; a != R_NilValue ; a = CDR(a)) if(!ARGUSED(a)) i++;

	if (i) {
	    a = allocList(i);
	    SET_TYPEOF(a, DOTSXP);
	    f = a;
	    for(b = supplied; b != R_NilValue; b = CDR(b))
		if(!ARGUSED(b)) {
		    SETCAR(f, CAR(b));
		    SET_TAG(f, TAG(b));
		    f = CDR(f);
		}
	    SETCAR(dots, a);
	}
    } else {
	/* Check that all arguments are used */
	SEXP unused = R_NilValue, last = R_NilValue;
	for (b = supplied; b != R_NilValue; b = CDR(b))
	    if (!ARGUSED(b)) {
		if(last == R_NilValue) {
		    PROTECT(unused = CONS(CAR(b), R_NilValue));
		    SET_TAG(unused, TAG(b));
		    last = unused;
		} else {
		    SETCDR(last, CONS(CAR(b), R_NilValue));
		    last = CDR(last);
		    SET_TAG(last, TAG(b));
		}
	    }

	if(last != R_NilValue) {
            /* show bad arguments in call without evaluating them */
            SEXP unusedForError = R_NilValue, last = R_NilValue;

            for(b = unused ; b != R_NilValue ; b = CDR(b)) {
                SEXP tagB = TAG(b), carB = CAR(b) ;
                if (TYPEOF(carB) == PROMSXP) carB = PREXPR(carB) ;
                if (last == R_NilValue) {
                    PROTECT(last = CONS(carB, R_NilValue));
                    SET_TAG(last, tagB);
                    unusedForError = last;
                } else {
                    SETCDR(last, CONS(carB, R_NilValue));
                    last = CDR(last);
                    SET_TAG(last, tagB);
                }
            }
	    errorcall(call /* R_GlobalContext->call */,
		      ngettext("unused argument %s",
			       "unused arguments %s",
			       (unsigned long) length(unusedForError)),
		      strchr(CHAR(asChar(deparse1line(unusedForError, 0))), '('));
	}
    }
    UNPROTECT(1);
    return(actuals);
}


/* patchArgsByActuals - patch promargs (given as 'supplied') to be promises
   for the respective actuals in the given environment 'cloenv'.  This is
   used by NextMethod to allow patching of arguments to the current closure
   before dispatching to the next method.  The implementation is based on
   matchArgs, but there is no error/warning checking, assuming that it has
   already been done by a call to matchArgs when the current closure was
   invoked.
*/

typedef enum {
    FS_UNMATCHED       = 0, /* the formal was not matched by any supplied arg */
    FS_MATCHED_PRESENT = 1, /* the formal was matched by a non-missing arg */
    FS_MATCHED_MISSING = 2, /* the formal was matched, but by a missing arg */
    FS_MATCHED_LOCAL   = 3, /* the formal was matched by a missing arg, but
                               a local variable of the same name as the formal
                               has been used */
} fstype_t;

static R_INLINE
void patchArgument(SEXP suppliedSlot, SEXP name, fstype_t *farg, SEXP cloenv) {
    SEXP value = CAR(suppliedSlot);
    if (value == R_MissingArg) {
        value = findVarInFrame3(cloenv, name, TRUE);
        if (value == R_MissingArg) {
            if (farg) *farg = FS_MATCHED_MISSING;
            return;
        }
        if (farg) *farg = FS_MATCHED_LOCAL;
    } else
        if (farg) *farg = FS_MATCHED_PRESENT;

    SETCAR(suppliedSlot, mkPROMISE(name, cloenv));
}

SEXP attribute_hidden
patchArgsByActuals(SEXP formals, SEXP supplied, SEXP cloenv)
{
    int i, seendots, farg_i;
    SEXP f, a, b, prsupplied;

    int nfarg = length(formals);
    if (!nfarg) nfarg = 1; // avoid undefined behaviour
    fstype_t farg[nfarg];
    for(i = 0; i < nfarg; i++) farg[i] = FS_UNMATCHED;

    /* Shallow-duplicate supplied arguments */

    PROTECT(prsupplied = allocList(length(supplied)));
    for(b = supplied, a = prsupplied; b != R_NilValue; b = CDR(b), a = CDR(a)) {
        SETCAR(a, CAR(b));
        SET_ARGUSED(a, 0);
        SET_TAG(a, TAG(b));
    }

    /* First pass: exact matches by tag */

    f = formals;
    farg_i = 0;
    while (f != R_NilValue) {
	if (TAG(f) != R_DotsSymbol) {
	    for (b = prsupplied; b != R_NilValue; b = CDR(b)) {
		if (TAG(b) != R_NilValue && pmatch(TAG(f), TAG(b), 1)) {
		    patchArgument(b, TAG(f), &farg[farg_i], cloenv);
		    SET_ARGUSED(b, 2);
		    break; /* Previous invocation of matchArgs */
		           /* ensured unique matches */
		}
	    }
	}
	f = CDR(f);
	farg_i++;
    }

    /* Second pass: partial matches based on tags */
    /* An exact match is required after first ... */
    /* The location of the first ... is saved in "dots" */

    seendots = 0;
    f = formals;
    farg_i = 0;
    while (f != R_NilValue) {
	if (farg[farg_i] == FS_UNMATCHED) {
	    if (TAG(f) == R_DotsSymbol && !seendots) {
		seendots = 1;
	    } else {
		for (b = prsupplied; b != R_NilValue; b = CDR(b)) {
		    if (!ARGUSED(b) && TAG(b) != R_NilValue &&
			pmatch(TAG(f), TAG(b), seendots)) {

			patchArgument(b, TAG(f), &farg[farg_i], cloenv);
			SET_ARGUSED(b, 1);
			break; /* Previous invocation of matchArgs */
			       /* ensured unique matches */
		    }
		}
	    }
	}
	f = CDR(f);
	farg_i++;
    }

    /* Third pass: matches based on order */
    /* All args specified in tag=value form */
    /* have now been matched.  If we find ... */
    /* we gobble up all the remaining args. */
    /* Otherwise we bind untagged values in */
    /* order to any unmatched formals. */

    f = formals;
    b = prsupplied;
    farg_i = 0;
    while (f != R_NilValue && b != R_NilValue) {
	if (TAG(f) == R_DotsSymbol) {
	    /* Done, ... and following args cannot be patched */
	    break;
	} else if (farg[farg_i] == FS_MATCHED_PRESENT) {
	    /* Note that this check corresponds to CAR(b) == R_MissingArg */
	    /* in matchArgs */

	    /* Already matched by tag */
	    /* skip to next formal */
	    f = CDR(f);
	    farg_i++;
	} else if (ARGUSED(b) || TAG(b) != R_NilValue) {
	    /* This value is used or tagged, skip to next value */
	    /* The second test above is needed because we */
	    /* shouldn't consider tagged values for positional */
	    /* matches. */
	    /* The formal being considered remains the same */
	    b = CDR(b);
	} else {
	    /* We have a positional match */
	    if (farg[farg_i] == FS_MATCHED_LOCAL)
	        /* Another supplied argument, a missing with a tag, has */
	        /* been patched to a promise reading this formal, because */
	        /* there was a local variable of that name. Hence, we have */
	        /* to turn this supplied argument into a missing. */
	        /* Otherwise, we would supply a value twice, confusing */
	        /* argument matching in subsequently called functions. */
	        SETCAR(b, R_MissingArg);
	    else
	        patchArgument(b, TAG(f), NULL, cloenv);

	    SET_ARGUSED(b, 1);
	    b = CDR(b);
	    f = CDR(f);
	    farg_i++;
	}
    }

    /* Previous invocation of matchArgs ensured all args are used */
    UNPROTECT(1);
    return(prsupplied);
}
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 1995, 1996  Robert Gentleman and Ross Ihaka
 *  Copyright (C) 1998--2016  The R Core Team.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 */

/*
 *	This code implements a non-moving generational collector
 *      with two or three generations.
 *
 *	Memory allocated by R_alloc is maintained in a stack.  Code
 *	that R_allocs memory must use vmaxget and vmaxset to obtain
 *	and reset the stack pointer.
 */

#define USE_RINTERNALS

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdarg.h>

#include <R_ext/RS.h> /* for S4 allocation */
#include <R_ext/Print.h>

/* Declarations for Valgrind.

   These are controlled by the
     --with-valgrind-instrumentation=
   option to configure, which sets VALGRIND_LEVEL to the
   supplied value (default 0) and defines NVALGRIND if
   the value is 0.

   level 0 is no additional instrumentation
   level 1 marks uninitialized numeric, logical, integer, raw,
	   complex vectors and R_alloc memory
   level 2 marks the data section of vector nodes as inaccessible
	   when they are freed.

   level 3 was withdrawn in R 3.2.0.

   It may be necessary to define NVALGRIND for a non-gcc
   compiler on a supported architecture if it has different
   syntax for inline assembly language from gcc.

   For Win32, Valgrind is useful only if running under Wine.
*/
#ifdef Win32
# ifndef USE_VALGRIND_FOR_WINE
# define NVALGRIND 1
#endif
#endif


#ifndef VALGRIND_LEVEL
# define VALGRIND_LEVEL 0
#endif

#ifndef NVALGRIND
# ifdef HAVE_VALGRIND_MEMCHECK_H
#  include "valgrind/memcheck.h"
# else
// internal version of headers
#  include "vg/memcheck.h"
# endif
#endif


#define R_USE_SIGNALS 1
#include <Defn.h>
#include <Internal.h>
#include <R_ext/GraphicsEngine.h> /* GEDevDesc, GEgetDevice */
#include <R_ext/Rdynload.h>
#include <R_ext/Rallocators.h> /* for R_allocator_t structure */
#include <Rmath.h> // R_pow_di
#include <Print.h> // R_print

#if defined(Win32)
extern void *Rm_malloc(size_t n);
extern void *Rm_calloc(size_t n_elements, size_t element_size);
extern void Rm_free(void * p);
extern void *Rm_realloc(void * p, size_t n);
#define calloc Rm_calloc
#define malloc Rm_malloc
#define realloc Rm_realloc
#define free Rm_free
#endif

/* malloc uses size_t.  We are assuming here that size_t is at least
   as large as unsigned long.  Changed from int at 1.6.0 to (i) allow
   2-4Gb objects on 32-bit system and (ii) objects limited only by
   length on a 64-bit system.
*/

static int gc_reporting = 0;
static int gc_count = 0;

/* These are used in profiling to separate out time in GC */
int R_gc_running() { return R_in_gc; }

#ifdef TESTING_WRITE_BARRIER
# define PROTECTCHECK
#endif

#ifdef PROTECTCHECK
/* This is used to help detect unprotected SEXP values.  It is most
   useful if the strict barrier is enabled as well. The strategy is:

       All GCs are full GCs

       New nodes are marked as NEWSXP

       After a GC all free nodes that are not of type NEWSXP are
       marked as type FREESXP

       Most calls to accessor functions check their SEXP inputs and
       SEXP outputs with CHK() to see if a reachable node is a
       FREESXP and signal an error if a FREESXP is found.

   Combined with GC torture this can help locate where an unprotected
   SEXP is being used.

   This approach will miss cases where an unprotected node has been
   re-allocated.  For these cases it is possible to set
   gc_inhibit_release to TRUE.  FREESXP nodes will not be reallocated,
   or large ones released, until gc_inhibit_release is set to FALSE
   again.  This will of course result in memory growth and should be
   used with care and typically in combination with OS mechanisms to
   limit process memory usage.  LT */

/* Before a node is marked as a FREESXP by the collector the previous
   type is recorded.  For now using the LEVELS field seems
   reasonable.  */
#define OLDTYPE(s) LEVELS(s)
#define SETOLDTYPE(s, t) SETLEVELS(s, t)

static R_INLINE SEXP CHK(SEXP x)
{
    /* **** NULL check because of R_CurrentExpr */
    if (x != NULL && TYPEOF(x) == FREESXP)
	error("unprotected object (%p) encountered (was %s)",
	      x, sexptype2char(OLDTYPE(x)));
    return x;
}
#else
#define CHK(x) x
#endif

/* The following three variables definitions are used to record the
   address and type of the first bad type seen during a collection,
   and for FREESXP nodes they record the old type as well. */
static SEXPTYPE bad_sexp_type_seen = 0;
static SEXP bad_sexp_type_sexp = NULL;
#ifdef PROTECTCHECK
static SEXPTYPE bad_sexp_type_old_type = 0;
#endif
static int bad_sexp_type_line = 0;

static R_INLINE void register_bad_sexp_type(SEXP s, int line)
{
    if (bad_sexp_type_seen == 0) {
	bad_sexp_type_seen = TYPEOF(s);
	bad_sexp_type_sexp = s;
	bad_sexp_type_line = line;
#ifdef PROTECTCHECK
	if (TYPEOF(s) == FREESXP)
	    bad_sexp_type_old_type = OLDTYPE(s);
#endif
    }
}

/* also called from typename() in inspect.c */
attribute_hidden
const char *sexptype2char(SEXPTYPE type) {
    switch (type) {
    case NILSXP:	return "NILSXP";
    case SYMSXP:	return "SYMSXP";
    case LISTSXP:	return "LISTSXP";
    case CLOSXP:	return "CLOSXP";
    case ENVSXP:	return "ENVSXP";
    case PROMSXP:	return "PROMSXP";
    case LANGSXP:	return "LANGSXP";
    case SPECIALSXP:	return "SPECIALSXP";
    case BUILTINSXP:	return "BUILTINSXP";
    case CHARSXP:	return "CHARSXP";
    case LGLSXP:	return "LGLSXP";
    case INTSXP:	return "INTSXP";
    case REALSXP:	return "REALSXP";
    case CPLXSXP:	return "CPLXSXP";
    case STRSXP:	return "STRSXP";
    case DOTSXP:	return "DOTSXP";
    case ANYSXP:	return "ANYSXP";
    case VECSXP:	return "VECSXP";
    case EXPRSXP:	return "EXPRSXP";
    case BCODESXP:	return "BCODESXP";
    case EXTPTRSXP:	return "EXTPTRSXP";
    case WEAKREFSXP:	return "WEAKREFSXP";
    case S4SXP:		return "S4SXP";
    case RAWSXP:	return "RAWSXP";
    case NEWSXP:	return "NEWSXP"; /* should never happen */
    case FREESXP:	return "FREESXP";
    default:		return "<unknown>";
    }
}

#define GC_TORTURE

static int gc_pending = 0;
#ifdef GC_TORTURE
/* **** if the user specified a wait before starting to force
   **** collections it might make sense to also wait before starting
   **** to inhibit releases */
static int gc_force_wait = 0;
static int gc_force_gap = 0;
static Rboolean gc_inhibit_release = FALSE;
#define FORCE_GC (gc_pending || (gc_force_wait > 0 ? (--gc_force_wait > 0 ? 0 : (gc_force_wait = gc_force_gap, 1)) : 0))
#else
# define FORCE_GC gc_pending
#endif

#ifdef R_MEMORY_PROFILING
static void R_ReportAllocation(R_size_t);
static void R_ReportNewPage();
#endif

#define GC_PROT(X) do { \
    int __wait__ = gc_force_wait; \
    int __gap__ = gc_force_gap;			   \
    Rboolean __release__ = gc_inhibit_release;	   \
    X;						   \
    gc_force_wait = __wait__;			   \
    gc_force_gap = __gap__;			   \
    gc_inhibit_release = __release__;		   \
}  while(0)

static void R_gc_internal(R_size_t size_needed);
static void R_gc_full(R_size_t size_needed);
static void mem_err_heap(R_size_t size);
static void mem_err_malloc(R_size_t size);

static SEXPREC UnmarkedNodeTemplate;
#define NODE_IS_MARKED(s) (MARK(s)==1)
#define MARK_NODE(s) (MARK(s)=1)
#define UNMARK_NODE(s) (MARK(s)=0)


/* Tuning Constants. Most of these could be made settable from R,
   within some reasonable constraints at least.  Since there are quite
   a lot of constants it would probably make sense to put together
   several "packages" representing different space/speed tradeoffs
   (e.g. very aggressive freeing and small increments to conserve
   memory; much less frequent releasing and larger increments to
   increase speed). */

/* There are three levels of collections.  Level 0 collects only the
   youngest generation, level 1 collects the two youngest generations,
   and level 2 collects all generations.  Higher level collections
   occur at least after specified numbers of lower level ones.  After
   LEVEL_0_FREQ level zero collections a level 1 collection is done;
   after every LEVEL_1_FREQ level 1 collections a level 2 collection
   occurs.  Thus, roughly, every LEVEL_0_FREQ-th collection is a level
   1 collection and every (LEVEL_0_FREQ * LEVEL_1_FREQ)-th collection
   is a level 2 collection.  */
#define LEVEL_0_FREQ 20
#define LEVEL_1_FREQ 5
static int collect_counts_max[] = { LEVEL_0_FREQ, LEVEL_1_FREQ };

/* When a level N collection fails to produce at least MinFreeFrac *
   R_NSize free nodes and MinFreeFrac * R_VSize free vector space, the
   next collection will be a level N + 1 collection.

   This constant is also used in heap size adjustment as a minimal
   fraction of the minimal heap size levels that should be available
   for allocation. */
static double R_MinFreeFrac = 0.2;

/* When pages are released, a number of free nodes equal to
   R_MaxKeepFrac times the number of allocated nodes for each class is
   retained.  Pages not needed to meet this requirement are released.
   An attempt to release pages is made every R_PageReleaseFreq level 1
   or level 2 collections. */
static double R_MaxKeepFrac = 0.5;
static int R_PageReleaseFreq = 1;

/* The heap size constants R_NSize and R_VSize are used for triggering
   collections.  The initial values set by defaults or command line
   arguments are used as minimal values.  After full collections these
   levels are adjusted up or down, though not below the minimal values
   or above the maximum values, towards maintain heap occupancy within
   a specified range.  When the number of nodes in use reaches
   R_NGrowFrac * R_NSize, the value of R_NSize is incremented by
   R_NGrowIncrMin + R_NGrowIncrFrac * R_NSize.  When the number of
   nodes in use falls below R_NShrinkFrac, R_NSize is decremented by
   R_NShrinkIncrMin + R_NShrinkFrac * R_NSize.  Analogous adjustments
   are made to R_VSize.

   This mechanism for adjusting the heap size constants is very
   primitive but hopefully adequate for now.  Some modeling and
   experimentation would be useful.  We want the heap sizes to get set
   at levels adequate for the current computations.  The present
   mechanism uses only the size of the current live heap to provide
   information about the current needs; since the current live heap
   size can be very volatile, the adjustment mechanism only makes
   gradual adjustments.  A more sophisticated strategy would use more
   of the live heap history.

   Some of the settings can now be adjusted by environment variables.
*/
static double R_NGrowFrac = 0.70;
static double R_NShrinkFrac = 0.30;

static double R_VGrowFrac = 0.70;
static double R_VShrinkFrac = 0.30;

#ifdef SMALL_MEMORY
/* On machines with only 32M of memory (or on a classic Mac OS port)
   it might be a good idea to use settings like these that are more
   aggressive at keeping memory usage down. */
static double R_NGrowIncrFrac = 0.0, R_NShrinkIncrFrac = 0.2;
static int R_NGrowIncrMin = 50000, R_NShrinkIncrMin = 0;
static double R_VGrowIncrFrac = 0.0, R_VShrinkIncrFrac = 0.2;
static int R_VGrowIncrMin = 100000, R_VShrinkIncrMin = 0;
#else
static double R_NGrowIncrFrac = 0.2, R_NShrinkIncrFrac = 0.2;
static int R_NGrowIncrMin = 40000, R_NShrinkIncrMin = 0;
static double R_VGrowIncrFrac = 0.2, R_VShrinkIncrFrac = 0.2;
static int R_VGrowIncrMin = 80000, R_VShrinkIncrMin = 0;
#endif

static void init_gc_grow_settings()
{
    char *arg;

    arg = getenv("R_GC_MEM_GROW");
    if (arg != NULL) {
	int which = (int) atof(arg);
	switch (which) {
	case 0: /* very conservative -- the SMALL_MEMORY settings */
	    R_NGrowIncrFrac = 0.0;
	    R_VGrowIncrFrac = 0.0;
	    break;
	case 1: /* default */
	    break;
	case 2: /* somewhat aggressive */
	    R_NGrowIncrFrac = 0.3;
	    R_VGrowIncrFrac = 0.3;
	    break;
	case 3: /* more aggressive */
	    R_NGrowIncrFrac = 0.4;
	    R_VGrowIncrFrac = 0.4;
	    R_NGrowFrac = 0.5;
	    R_VGrowFrac = 0.5;
	    break;
	}
    }
    arg = getenv("R_GC_GROWFRAC");
    if (arg != NULL) {
	double frac = atof(arg);
	if (0.35 <= frac && frac <= 0.75) {
	    R_NGrowFrac = frac;
	    R_VGrowFrac = frac;
	}
    }
    arg = getenv("R_GC_GROWINCRFRAC");
    if (arg != NULL) {
	double frac = atof(arg);
	if (0.05 <= frac && frac <= 0.80) {
	    R_NGrowIncrFrac = frac;
	    R_VGrowIncrFrac = frac;
	}
    }
    arg = getenv("R_GC_NGROWINCRFRAC");
    if (arg != NULL) {
	double frac = atof(arg);
	if (0.05 <= frac && frac <= 0.80)
	    R_NGrowIncrFrac = frac;
    }
    arg = getenv("R_GC_VGROWINCRFRAC");
    if (arg != NULL) {
	double frac = atof(arg);
	if (0.05 <= frac && frac <= 0.80)
	    R_VGrowIncrFrac = frac;
    }
}

/* Maximal Heap Limits.  These variables contain upper limits on the
   heap sizes.  They could be made adjustable from the R level,
   perhaps by a handler for a recoverable error.

   Access to these values is provided with reader and writer
   functions; the writer function insures that the maximal values are
   never set below the current ones. */
static R_size_t R_MaxVSize = R_SIZE_T_MAX;
static R_size_t R_MaxNSize = R_SIZE_T_MAX;
static int vsfac = 1; /* current units for vsize: changes at initialization */

R_size_t attribute_hidden R_GetMaxVSize(void)
{
    if (R_MaxVSize == R_SIZE_T_MAX) return R_SIZE_T_MAX;
    return R_MaxVSize*vsfac;
}

void attribute_hidden R_SetMaxVSize(R_size_t size)
{
    if (size == R_SIZE_T_MAX) return;
    if (size / vsfac >= R_VSize) R_MaxVSize = (size+1)/vsfac;
}

R_size_t attribute_hidden R_GetMaxNSize(void)
{
    return R_MaxNSize;
}

void attribute_hidden R_SetMaxNSize(R_size_t size)
{
    if (size >= R_NSize) R_MaxNSize = size;
}

void attribute_hidden R_SetPPSize(R_size_t size)
{
    R_PPStackSize = (int) size;
}

/* Miscellaneous Globals. */

static SEXP R_VStack = NULL;		/* R_alloc stack pointer */
static SEXP R_PreciousList = NULL;      /* List of Persistent Objects */
static R_size_t R_LargeVallocSize = 0;
static R_size_t R_SmallVallocSize = 0;
static R_size_t orig_R_NSize;
static R_size_t orig_R_VSize;

static R_size_t R_N_maxused=0;
static R_size_t R_V_maxused=0;

/* Node Classes.  Non-vector nodes are of class zero. Small vector
   nodes are in classes 1, ..., NUM_SMALL_NODE_CLASSES, and large
   vector nodes are in class LARGE_NODE_CLASS. Vectors with
   custom allocators are in CUSTOM_NODE_CLASS. For vector nodes the
   node header is followed in memory by the vector data, offset from
   the header by SEXPREC_ALIGN. */

#define NUM_NODE_CLASSES 8

/* sxpinfo allocates 3 bits for the node class, so at most 8 are allowed */
#if NUM_NODE_CLASSES > 8
# error NUM_NODE_CLASSES must be at most 8
#endif

#define LARGE_NODE_CLASS  (NUM_NODE_CLASSES - 1)
#define CUSTOM_NODE_CLASS (NUM_NODE_CLASSES - 2)
#define NUM_SMALL_NODE_CLASSES (NUM_NODE_CLASSES - 2)

/* the number of VECREC's in nodes of the small node classes */
static int NodeClassSize[NUM_SMALL_NODE_CLASSES] = { 0, 1, 2, 4, 8, 16 };

#define NODE_CLASS(s) ((s)->sxpinfo.gccls)
#define SET_NODE_CLASS(s,v) (((s)->sxpinfo.gccls) = (v))


/* Node Generations. */

#define NUM_OLD_GENERATIONS 2

/* sxpinfo allocates one bit for the old generation count, so only 1
   or 2 is allowed */
#if NUM_OLD_GENERATIONS > 2 || NUM_OLD_GENERATIONS < 1
# error number of old generations must be 1 or 2
#endif

#define NODE_GENERATION(s) ((s)->sxpinfo.gcgen)
#define SET_NODE_GENERATION(s,g) ((s)->sxpinfo.gcgen=(g))

#define NODE_GEN_IS_YOUNGER(s,g) \
  (! NODE_IS_MARKED(s) || NODE_GENERATION(s) < (g))
#define NODE_IS_OLDER(x, y) \
  (NODE_IS_MARKED(x) && \
   (! NODE_IS_MARKED(y) || NODE_GENERATION(x) > NODE_GENERATION(y)))

static int num_old_gens_to_collect = 0;
static int gen_gc_counts[NUM_OLD_GENERATIONS + 1];
static int collect_counts[NUM_OLD_GENERATIONS];


/* Node Pages.  Non-vector nodes and small vector nodes are allocated
   from fixed size pages.  The pages for each node class are kept in a
   linked list. */

typedef union PAGE_HEADER {
  union PAGE_HEADER *next;
  double align;
} PAGE_HEADER;

#define BASE_PAGE_SIZE 2000
#define R_PAGE_SIZE \
  (((BASE_PAGE_SIZE - sizeof(PAGE_HEADER)) / sizeof(SEXPREC)) \
   * sizeof(SEXPREC) \
   + sizeof(PAGE_HEADER))
#define NODE_SIZE(c) \
  ((c) == 0 ? sizeof(SEXPREC) : \
   sizeof(SEXPREC_ALIGN) + NodeClassSize[c] * sizeof(VECREC))

#define PAGE_DATA(p) ((void *) (p + 1))
#define VHEAP_FREE() (R_VSize - R_LargeVallocSize - R_SmallVallocSize)


/* The Heap Structure.  Nodes for each class/generation combination
   are arranged in circular doubly-linked lists.  The double linking
   allows nodes to be removed in constant time; this is used by the
   collector to move reachable nodes out of free space and into the
   appropriate generation.  The circularity eliminates the need for
   end checks.  In addition, each link is anchored at an artificial
   node, the Peg SEXPREC's in the structure below, which simplifies
   pointer maintenance.  The circular doubly-linked arrangement is
   taken from Baker's in-place incremental collector design; see
   ftp://ftp.netcom.com/pub/hb/hbaker/NoMotionGC.html or the Jones and
   Lins GC book.  The linked lists are implemented by adding two
   pointer fields to the SEXPREC structure, which increases its size
   from 5 to 7 words. Other approaches are possible but don't seem
   worth pursuing for R.

   There are two options for dealing with old-to-new pointers.  The
   first option is to make sure they never occur by transferring all
   referenced younger objects to the generation of the referrer when a
   reference to a newer object is assigned to an older one.  This is
   enabled by defining EXPEL_OLD_TO_NEW.  The second alternative is to
   keep track of all nodes that may contain references to newer nodes
   and to "age" the nodes they refer to at the beginning of each
   collection.  This is the default.  The first option is simpler in
   some ways, but will create more floating garbage and add a bit to
   the execution time, though the difference is probably marginal on
   both counts.*/
/*#define EXPEL_OLD_TO_NEW*/
static struct {
    SEXP Old[NUM_OLD_GENERATIONS], New, Free;
    SEXPREC OldPeg[NUM_OLD_GENERATIONS], NewPeg;
#ifndef EXPEL_OLD_TO_NEW
    SEXP OldToNew[NUM_OLD_GENERATIONS];
    SEXPREC OldToNewPeg[NUM_OLD_GENERATIONS];
#endif
    int OldCount[NUM_OLD_GENERATIONS], AllocCount, PageCount;
    PAGE_HEADER *pages;
} R_GenHeap[NUM_NODE_CLASSES];

static R_size_t R_NodesInUse = 0;

#define NEXT_NODE(s) (s)->gengc_next_node
#define PREV_NODE(s) (s)->gengc_prev_node
#define SET_NEXT_NODE(s,t) (NEXT_NODE(s) = (t))
#define SET_PREV_NODE(s,t) (PREV_NODE(s) = (t))


/* Node List Manipulation */

/* unsnap node s from its list */
#define UNSNAP_NODE(s) do { \
  SEXP un__n__ = (s); \
  SEXP next = NEXT_NODE(un__n__); \
  SEXP prev = PREV_NODE(un__n__); \
  SET_NEXT_NODE(prev, next); \
  SET_PREV_NODE(next, prev); \
} while(0)

/* snap in node s before node t */
#define SNAP_NODE(s,t) do { \
  SEXP sn__n__ = (s); \
  SEXP next = (t); \
  SEXP prev = PREV_NODE(next); \
  SET_NEXT_NODE(sn__n__, next); \
  SET_PREV_NODE(next, sn__n__); \
  SET_NEXT_NODE(prev, sn__n__); \
  SET_PREV_NODE(sn__n__, prev); \
} while (0)

/* move all nodes on from_peg to to_peg */
#define BULK_MOVE(from_peg,to_peg) do { \
  SEXP __from__ = (from_peg); \
  SEXP __to__ = (to_peg); \
  SEXP first_old = NEXT_NODE(__from__); \
  SEXP last_old = PREV_NODE(__from__); \
  SEXP first_new = NEXT_NODE(__to__); \
  SET_PREV_NODE(first_old, __to__); \
  SET_NEXT_NODE(__to__, first_old); \
  SET_PREV_NODE(first_new, last_old); \
  SET_NEXT_NODE(last_old, first_new); \
  SET_NEXT_NODE(__from__, __from__); \
  SET_PREV_NODE(__from__, __from__); \
} while (0);


/* Processing Node Children */

/* This macro calls dc__action__ for each child of __n__, passing
   dc__extra__ as a second argument for each call. */
/* When the CHARSXP hash chains are maintained through the ATTRIB
   field it is important that we NOT trace those fields otherwise too
   many CHARSXPs will be kept alive artificially. As a safety we don't
   ignore all non-NULL ATTRIB values for CHARSXPs but only those that
   are themselves CHARSXPs, which is what they will be if they are
   part of a hash chain.  Theoretically, for CHARSXPs the ATTRIB field
   should always be either R_NilValue or a CHARSXP. */
#ifdef PROTECTCHECK
# define HAS_GENUINE_ATTRIB(x) \
    (TYPEOF(x) != FREESXP && ATTRIB(x) != R_NilValue && \
     (TYPEOF(x) != CHARSXP || TYPEOF(ATTRIB(x)) != CHARSXP))
#else
# define HAS_GENUINE_ATTRIB(x) \
    (ATTRIB(x) != R_NilValue && \
     (TYPEOF(x) != CHARSXP || TYPEOF(ATTRIB(x)) != CHARSXP))
#endif

#ifdef PROTECTCHECK
#define FREE_FORWARD_CASE case FREESXP: if (gc_inhibit_release) break;
#else
#define FREE_FORWARD_CASE
#endif
#define DO_CHILDREN(__n__,dc__action__,dc__extra__) do { \
  if (HAS_GENUINE_ATTRIB(__n__)) \
    dc__action__(ATTRIB(__n__), dc__extra__); \
  switch (TYPEOF(__n__)) { \
  case NILSXP: \
  case BUILTINSXP: \
  case SPECIALSXP: \
  case CHARSXP: \
  case LGLSXP: \
  case INTSXP: \
  case REALSXP: \
  case CPLXSXP: \
  case WEAKREFSXP: \
  case RAWSXP: \
  case S4SXP: \
    break; \
  case STRSXP: \
  case EXPRSXP: \
  case VECSXP: \
    { \
      R_xlen_t i; \
      for (i = 0; i < XLENGTH(__n__); i++) \
	dc__action__(VECTOR_ELT(__n__, i), dc__extra__); \
    } \
    break; \
  case ENVSXP: \
    dc__action__(FRAME(__n__), dc__extra__); \
    dc__action__(ENCLOS(__n__), dc__extra__); \
    dc__action__(HASHTAB(__n__), dc__extra__); \
    break; \
  case CLOSXP: \
  case PROMSXP: \
  case LISTSXP: \
  case LANGSXP: \
  case DOTSXP: \
  case SYMSXP: \
  case BCODESXP: \
    dc__action__(TAG(__n__), dc__extra__); \
    dc__action__(CAR(__n__), dc__extra__); \
    dc__action__(CDR(__n__), dc__extra__); \
    break; \
  case EXTPTRSXP: \
    dc__action__(EXTPTR_PROT(__n__), dc__extra__); \
    dc__action__(EXTPTR_TAG(__n__), dc__extra__); \
    break; \
  FREE_FORWARD_CASE \
  default: \
    register_bad_sexp_type(__n__, __LINE__);		\
  } \
} while(0)


/* Forwarding Nodes.  These macros mark nodes or children of nodes and
   place them on the forwarding list.  The forwarding list is assumed
   to be in a local variable of the caller named named
   forwarded_nodes. */

#define FORWARD_NODE(s) do { \
  SEXP fn__n__ = (s); \
  if (fn__n__ && ! NODE_IS_MARKED(fn__n__)) { \
    CHECK_FOR_FREE_NODE(fn__n__) \
    MARK_NODE(fn__n__); \
    UNSNAP_NODE(fn__n__); \
    SET_NEXT_NODE(fn__n__, forwarded_nodes); \
    forwarded_nodes = fn__n__; \
  } \
} while (0)

#define FC_FORWARD_NODE(__n__,__dummy__) FORWARD_NODE(__n__)
#define FORWARD_CHILDREN(__n__) DO_CHILDREN(__n__,FC_FORWARD_NODE, 0)

/* This macro should help localize where a FREESXP node is encountered
   in the GC */
#ifdef PROTECTCHECK
#define CHECK_FOR_FREE_NODE(s) { \
    SEXP cf__n__ = (s); \
    if (TYPEOF(cf__n__) == FREESXP && ! gc_inhibit_release) \
	register_bad_sexp_type(cf__n__, __LINE__); \
}
#else
#define CHECK_FOR_FREE_NODE(s)
#endif


/* Node Allocation. */

#define CLASS_GET_FREE_NODE(c,s) do { \
  SEXP __n__ = R_GenHeap[c].Free; \
  if (__n__ == R_GenHeap[c].New) { \
    GetNewPage(c); \
    __n__ = R_GenHeap[c].Free; \
  } \
  R_GenHeap[c].Free = NEXT_NODE(__n__); \
  R_NodesInUse++; \
  (s) = __n__; \
} while (0)

#define NO_FREE_NODES() (R_NodesInUse >= R_NSize)
#define GET_FREE_NODE(s) CLASS_GET_FREE_NODE(0,s)

/* versions that assume nodes are avaialble without adding a new page */
#define CLASS_QUICK_GET_FREE_NODE(c,s) do {		\
	SEXP __n__ = R_GenHeap[c].Free;			\
	if (__n__ == R_GenHeap[c].New)			\
	    error("need new page - should not happen");	\
	R_GenHeap[c].Free = NEXT_NODE(__n__);		\
	R_NodesInUse++;					\
	(s) = __n__;					\
    } while (0)

#define QUICK_GET_FREE_NODE(s) CLASS_QUICK_GET_FREE_NODE(0,s)

/* QUICK versions can be used if (CLASS_)NEED_NEW_PAGE returns FALSE */
#define CLASS_NEED_NEW_PAGE(c) (R_GenHeap[c].Free == R_GenHeap[c].New)
#define NEED_NEW_PAGE() CLASS_NEED_NEW_PAGE(0)


/* Debugging Routines. */

#ifdef DEBUG_GC
static void CheckNodeGeneration(SEXP x, int g)
{
    if (x && NODE_GENERATION(x) < g) {
	REprintf("untraced old-to-new reference\n");
    }
}

static void DEBUG_CHECK_NODE_COUNTS(char *where)
{
    int i, OldCount, NewCount, OldToNewCount, gen;
    SEXP s;

    REprintf("Node counts %s:\n", where);
    for (i = 0; i < NUM_NODE_CLASSES; i++) {
	for (s = NEXT_NODE(R_GenHeap[i].New), NewCount = 0;
	     s != R_GenHeap[i].New;
	     s = NEXT_NODE(s)) {
	    NewCount++;
	    if (i != NODE_CLASS(s))
		REprintf("Inconsistent class assignment for node!\n");
	}
	for (gen = 0, OldCount = 0, OldToNewCount = 0;
	     gen < NUM_OLD_GENERATIONS;
	     gen++) {
	    for (s = NEXT_NODE(R_GenHeap[i].Old[gen]);
		 s != R_GenHeap[i].Old[gen];
		 s = NEXT_NODE(s)) {
		OldCount++;
		if (i != NODE_CLASS(s))
		    REprintf("Inconsistent class assignment for node!\n");
		if (gen != NODE_GENERATION(s))
		    REprintf("Inconsistent node generation\n");
		DO_CHILDREN(s, CheckNodeGeneration, gen);
	    }
	    for (s = NEXT_NODE(R_GenHeap[i].OldToNew[gen]);
		 s != R_GenHeap[i].OldToNew[gen];
		 s = NEXT_NODE(s)) {
		OldToNewCount++;
		if (i != NODE_CLASS(s))
		    REprintf("Inconsistent class assignment for node!\n");
		if (gen != NODE_GENERATION(s))
		    REprintf("Inconsistent node generation\n");
	    }
	}
	REprintf("Class: %d, New = %d, Old = %d, OldToNew = %d, Total = %d\n",
		 i,
		 NewCount, OldCount, OldToNewCount,
		 NewCount + OldCount + OldToNewCount);
    }
}

static void DEBUG_GC_SUMMARY(int full_gc)
{
    int i, gen, OldCount;
    REprintf("\n%s, VSize = %lu", full_gc ? "Full" : "Minor",
	     R_SmallVallocSize + R_LargeVallocSize);
    for (i = 1; i < NUM_NODE_CLASSES; i++) {
	for (gen = 0, OldCount = 0; gen < NUM_OLD_GENERATIONS; gen++)
	    OldCount += R_GenHeap[i].OldCount[gen];
	REprintf(", class %d: %d", i, OldCount);
    }
}
#else
#define DEBUG_CHECK_NODE_COUNTS(s)
#define DEBUG_GC_SUMMARY(x)
#endif /* DEBUG_GC */

#ifdef DEBUG_ADJUST_HEAP
static void DEBUG_ADJUST_HEAP_PRINT(double node_occup, double vect_occup)
{
    int i;
    R_size_t alloc;
    REprintf("Node occupancy: %.0f%%\nVector occupancy: %.0f%%\n",
	     100.0 * node_occup, 100.0 * vect_occup);
    alloc = R_LargeVallocSize +
	sizeof(SEXPREC_ALIGN) * R_GenHeap[LARGE_NODE_CLASS].AllocCount;
    for (i = 0; i < NUM_SMALL_NODE_CLASSES; i++)
	alloc += R_PAGE_SIZE * R_GenHeap[i].PageCount;
    REprintf("Total allocation: %lu\n", alloc);
    REprintf("Ncells %lu\nVcells %lu\n", R_NSize, R_VSize);
}
#else
#define DEBUG_ADJUST_HEAP_PRINT(node_occup, vect_occup)
#endif /* DEBUG_ADJUST_HEAP */

#ifdef DEBUG_RELEASE_MEM
static void DEBUG_RELEASE_PRINT(int rel_pages, int maxrel_pages, int i)
{
    if (maxrel_pages > 0) {
	int gen, n;
	REprintf("Class: %d, pages = %d, maxrel = %d, released = %d\n", i,
		 R_GenHeap[i].PageCount, maxrel_pages, rel_pages);
	for (gen = 0, n = 0; gen < NUM_OLD_GENERATIONS; gen++)
	    n += R_GenHeap[i].OldCount[gen];
	REprintf("Allocated = %d, in use = %d\n", R_GenHeap[i].AllocCount, n);
    }
}
#else
#define DEBUG_RELEASE_PRINT(rel_pages, maxrel_pages, i)
#endif /* DEBUG_RELEASE_MEM */

#ifdef COMPUTE_REFCNT_VALUES
#define INIT_REFCNT(x) do {			\
	SEXP __x__ = (x);			\
	SET_REFCNT(__x__, 0);			\
	SET_TRACKREFS(__x__, TRUE);		\
    } while (0)
#else
#define INIT_REFCNT(x) do {} while (0)
#endif

/* Page Allocation and Release. */

static void GetNewPage(int node_class)
{
    SEXP s, base;
    char *data;
    PAGE_HEADER *page;
    int node_size, page_count, i;  // FIXME: longer type?

    node_size = NODE_SIZE(node_class);
    page_count = (R_PAGE_SIZE - sizeof(PAGE_HEADER)) / node_size;

    page = malloc(R_PAGE_SIZE);
    if (page == NULL) {
	R_gc_full(0);
	page = malloc(R_PAGE_SIZE);
	if (page == NULL)
	    mem_err_malloc((R_size_t) R_PAGE_SIZE);
    }
#ifdef R_MEMORY_PROFILING
    R_ReportNewPage();
#endif
    page->next = R_GenHeap[node_class].pages;
    R_GenHeap[node_class].pages = page;
    R_GenHeap[node_class].PageCount++;

    data = PAGE_DATA(page);
    base = R_GenHeap[node_class].New;
    for (i = 0; i < page_count; i++, data += node_size) {
	s = (SEXP) data;
	R_GenHeap[node_class].AllocCount++;
	SNAP_NODE(s, base);
#if  VALGRIND_LEVEL > 1
	if (NodeClassSize[node_class] > 0)
	    VALGRIND_MAKE_MEM_NOACCESS(DATAPTR(s), NodeClassSize[node_class]*sizeof(VECREC));
#endif
	s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
	INIT_REFCNT(s);
	SET_NODE_CLASS(s, node_class);
#ifdef PROTECTCHECK
	TYPEOF(s) = NEWSXP;
#endif
	base = s;
	R_GenHeap[node_class].Free = s;
    }
}

static void ReleasePage(PAGE_HEADER *page, int node_class)
{
    SEXP s;
    char *data;
    int node_size, page_count, i;

    node_size = NODE_SIZE(node_class);
    page_count = (R_PAGE_SIZE - sizeof(PAGE_HEADER)) / node_size;
    data = PAGE_DATA(page);

    for (i = 0; i < page_count; i++, data += node_size) {
	s = (SEXP) data;
	UNSNAP_NODE(s);
	R_GenHeap[node_class].AllocCount--;
    }
    R_GenHeap[node_class].PageCount--;
    free(page);
}

static void TryToReleasePages(void)
{
    SEXP s;
    int i;
    static int release_count = 0;

    if (release_count == 0) {
	release_count = R_PageReleaseFreq;
	for (i = 0; i < NUM_SMALL_NODE_CLASSES; i++) {
	    int pages_free = 0;
	    PAGE_HEADER *page, *last, *next;
	    int node_size = NODE_SIZE(i);
	    int page_count = (R_PAGE_SIZE - sizeof(PAGE_HEADER)) / node_size;
	    int maxrel, maxrel_pages, rel_pages, gen;

	    maxrel = R_GenHeap[i].AllocCount;
	    for (gen = 0; gen < NUM_OLD_GENERATIONS; gen++)
		maxrel -= (1.0 + R_MaxKeepFrac) * R_GenHeap[i].OldCount[gen];
	    maxrel_pages = maxrel > 0 ? maxrel / page_count : 0;

	    /* all nodes in New space should be both free and unmarked */
	    for (page = R_GenHeap[i].pages, rel_pages = 0, last = NULL;
		 rel_pages < maxrel_pages && page != NULL;) {
		int j, in_use;
		char *data = PAGE_DATA(page);

		next = page->next;
		for (in_use = 0, j = 0; j < page_count;
		     j++, data += node_size) {
		    s = (SEXP) data;
		    if (NODE_IS_MARKED(s)) {
			in_use = 1;
			break;
		    }
		}
		if (! in_use) {
		    ReleasePage(page, i);
		    if (last == NULL)
			R_GenHeap[i].pages = next;
		    else
			last->next = next;
		    pages_free++;
		    rel_pages++;
		}
		else last = page;
		page = next;
	    }
	    DEBUG_RELEASE_PRINT(rel_pages, maxrel_pages, i);
	    R_GenHeap[i].Free = NEXT_NODE(R_GenHeap[i].New);
	}
    }
    else release_count--;
}

/* compute size in VEC units so result will fit in LENGTH field for FREESXPs */
static R_INLINE R_size_t getVecSizeInVEC(SEXP s)
{
    if (IS_GROWABLE(s))
	SETLENGTH(s, XTRUELENGTH(s));

    R_size_t size;
    switch (TYPEOF(s)) {	/* get size in bytes */
    case CHARSXP:
	size = XLENGTH(s) + 1;
	break;
    case RAWSXP:
	size = XLENGTH(s);
	break;
    case LGLSXP:
    case INTSXP:
	size = XLENGTH(s) * sizeof(int);
	break;
    case REALSXP:
	size = XLENGTH(s) * sizeof(double);
	break;
    case CPLXSXP:
	size = XLENGTH(s) * sizeof(Rcomplex);
	break;
    case STRSXP:
    case EXPRSXP:
    case VECSXP:
	size = XLENGTH(s) * sizeof(SEXP);
	break;
    default:
	register_bad_sexp_type(s, __LINE__);
	size = 0;
    }
    return BYTE2VEC(size);
}

static void custom_node_free(void *ptr);

static void ReleaseLargeFreeVectors()
{
    for (int node_class = CUSTOM_NODE_CLASS; node_class <= LARGE_NODE_CLASS; node_class++) {
	SEXP s = NEXT_NODE(R_GenHeap[node_class].New);
	while (s != R_GenHeap[node_class].New) {
	    SEXP next = NEXT_NODE(s);
	    if (CHAR(s) != NULL) {
		R_size_t size;
#ifdef PROTECTCHECK
		if (TYPEOF(s) == FREESXP)
		    size = XLENGTH(s);
		else
		    /* should not get here -- arrange for a warning/error? */
		    size = getVecSizeInVEC(s);
#else
		size = getVecSizeInVEC(s);
#endif
		UNSNAP_NODE(s);
		R_GenHeap[node_class].AllocCount--;
		if (node_class == LARGE_NODE_CLASS) {
		    R_LargeVallocSize -= size;
#ifdef LONG_VECTOR_SUPPORT
		    if (IS_LONG_VEC(s))
			free(((char *) s) - sizeof(R_long_vec_hdr_t));
		    else
			free(s);
#else
		    free(s);
#endif
		} else {
#ifdef LONG_VECTOR_SUPPORT
		    if (IS_LONG_VEC(s))
			custom_node_free(((char *) s) - sizeof(R_long_vec_hdr_t));
		    else
			custom_node_free(s);
#else
		    custom_node_free(s);
#endif
		}
	    }
	    s = next;
	}
    }
}


/* Heap Size Adjustment. */

static void AdjustHeapSize(R_size_t size_needed)
{
    R_size_t R_MinNFree = (R_size_t)(orig_R_NSize * R_MinFreeFrac);
    R_size_t R_MinVFree = (R_size_t)(orig_R_VSize * R_MinFreeFrac);
    R_size_t NNeeded = R_NodesInUse + R_MinNFree;
    R_size_t VNeeded = R_SmallVallocSize + R_LargeVallocSize
	+ size_needed + R_MinVFree;
    double node_occup = ((double) NNeeded) / R_NSize;
    double vect_occup =	((double) VNeeded) / R_VSize;

    if (node_occup > R_NGrowFrac) {
	R_size_t change = (R_size_t)(R_NGrowIncrMin + R_NGrowIncrFrac * R_NSize);
	if (R_MaxNSize >= R_NSize + change)
	    R_NSize += change;
    }
    else if (node_occup < R_NShrinkFrac) {
	R_NSize -= (R_NShrinkIncrMin + R_NShrinkIncrFrac * R_NSize);
	if (R_NSize < NNeeded)
	    R_NSize = (NNeeded < R_MaxNSize) ? NNeeded: R_MaxNSize;
	if (R_NSize < orig_R_NSize)
	    R_NSize = orig_R_NSize;
    }

    if (vect_occup > 1.0 && VNeeded < R_MaxVSize)
	R_VSize = VNeeded;
    if (vect_occup > R_VGrowFrac) {
	R_size_t change = (R_size_t)(R_VGrowIncrMin + R_VGrowIncrFrac * R_VSize);
	if (R_MaxVSize - R_VSize >= change)
	    R_VSize += change;
    }
    else if (vect_occup < R_VShrinkFrac) {
	R_VSize -= R_VShrinkIncrMin + R_VShrinkIncrFrac * R_VSize;
	if (R_VSize < VNeeded)
	    R_VSize = VNeeded;
	if (R_VSize < orig_R_VSize)
	    R_VSize = orig_R_VSize;
    }

    DEBUG_ADJUST_HEAP_PRINT(node_occup, vect_occup);
}


/* Managing Old-to-New References. */

#define AGE_NODE(s,g) do { \
  SEXP an__n__ = (s); \
  int an__g__ = (g); \
  if (an__n__ && NODE_GEN_IS_YOUNGER(an__n__, an__g__)) { \
    if (NODE_IS_MARKED(an__n__)) \
       R_GenHeap[NODE_CLASS(an__n__)].OldCount[NODE_GENERATION(an__n__)]--; \
    else \
      MARK_NODE(an__n__); \
    SET_NODE_GENERATION(an__n__, an__g__); \
    UNSNAP_NODE(an__n__); \
    SET_NEXT_NODE(an__n__, forwarded_nodes); \
    forwarded_nodes = an__n__; \
  } \
} while (0)

static void AgeNodeAndChildren(SEXP s, int gen)
{
    SEXP forwarded_nodes = NULL;
    AGE_NODE(s, gen);
    while (forwarded_nodes != NULL) {
	s = forwarded_nodes;
	forwarded_nodes = NEXT_NODE(forwarded_nodes);
	if (NODE_GENERATION(s) != gen)
	    REprintf("****snapping into wrong generation\n");
	SNAP_NODE(s, R_GenHeap[NODE_CLASS(s)].Old[gen]);
	R_GenHeap[NODE_CLASS(s)].OldCount[gen]++;
	DO_CHILDREN(s, AGE_NODE, gen);
    }
}

static void old_to_new(SEXP x, SEXP y)
{
#ifdef EXPEL_OLD_TO_NEW
    AgeNodeAndChildren(y, NODE_GENERATION(x));
#else
    UNSNAP_NODE(x);
    SNAP_NODE(x, R_GenHeap[NODE_CLASS(x)].OldToNew[NODE_GENERATION(x)]);
#endif
}

#ifdef COMPUTE_REFCNT_VALUES
#define FIX_REFCNT(x, old, new) do {					\
	if (TRACKREFS(x)) {						\
	    SEXP __old__ = (old);					\
	    SEXP __new__ = (new);					\
	    if (__old__ != __new__) {					\
		if (__old__) DECREMENT_REFCNT(__old__);			\
		if (__new__) INCREMENT_REFCNT(__new__);			\
	    }								\
	}								\
    } while (0)
#else
#define FIX_REFCNT(x, old, new) do {} while (0)
#endif

#define CHECK_OLD_TO_NEW(x,y) do { \
  if (NODE_IS_OLDER(CHK(x), CHK(y))) old_to_new(x,y);  } while (0)


/* Node Sorting.  SortNodes attempts to improve locality of reference
   by rearranging the free list to place nodes on the same place page
   together and order nodes within pages.  This involves a sweep of the
   heap, so it should not be done too often, but doing it at least
   occasionally does seem essential.  Sorting on each full colllection is
   probably sufficient.
*/

#define SORT_NODES
#ifdef SORT_NODES
static void SortNodes(void)
{
    SEXP s;
    int i;

    for (i = 0; i < NUM_SMALL_NODE_CLASSES; i++) {
	PAGE_HEADER *page;
	int node_size = NODE_SIZE(i);
	int page_count = (R_PAGE_SIZE - sizeof(PAGE_HEADER)) / node_size;

	SET_NEXT_NODE(R_GenHeap[i].New, R_GenHeap[i].New);
	SET_PREV_NODE(R_GenHeap[i].New, R_GenHeap[i].New);
	for (page = R_GenHeap[i].pages; page != NULL; page = page->next) {
	    int j;
	    char *data = PAGE_DATA(page);

	    for (j = 0; j < page_count; j++, data += node_size) {
		s = (SEXP) data;
		if (! NODE_IS_MARKED(s))
		    SNAP_NODE(s, R_GenHeap[i].New);
	    }
	}
	R_GenHeap[i].Free = NEXT_NODE(R_GenHeap[i].New);
    }
}
#endif


/* Finalization and Weak References */

/* The design of this mechanism is very close to the one described in
   "Stretching the storage manager: weak pointers and stable names in
   Haskell" by Peyton Jones, Marlow, and Elliott (at
   www.research.microsoft.com/Users/simonpj/papers/weak.ps.gz). --LT */

static SEXP R_weak_refs = NULL;

#define READY_TO_FINALIZE_MASK 1

#define SET_READY_TO_FINALIZE(s) ((s)->sxpinfo.gp |= READY_TO_FINALIZE_MASK)
#define CLEAR_READY_TO_FINALIZE(s) ((s)->sxpinfo.gp &= ~READY_TO_FINALIZE_MASK)
#define IS_READY_TO_FINALIZE(s) ((s)->sxpinfo.gp & READY_TO_FINALIZE_MASK)

#define FINALIZE_ON_EXIT_MASK 2

#define SET_FINALIZE_ON_EXIT(s) ((s)->sxpinfo.gp |= FINALIZE_ON_EXIT_MASK)
#define CLEAR_FINALIZE_ON_EXIT(s) ((s)->sxpinfo.gp &= ~FINALIZE_ON_EXIT_MASK)
#define FINALIZE_ON_EXIT(s) ((s)->sxpinfo.gp & FINALIZE_ON_EXIT_MASK)

#define WEAKREF_SIZE 4
#define WEAKREF_KEY(w) VECTOR_ELT(w, 0)
#define SET_WEAKREF_KEY(w, k) SET_VECTOR_ELT(w, 0, k)
#define WEAKREF_VALUE(w) VECTOR_ELT(w, 1)
#define SET_WEAKREF_VALUE(w, v) SET_VECTOR_ELT(w, 1, v)
#define WEAKREF_FINALIZER(w) VECTOR_ELT(w, 2)
#define SET_WEAKREF_FINALIZER(w, f) SET_VECTOR_ELT(w, 2, f)
#define WEAKREF_NEXT(w) VECTOR_ELT(w, 3)
#define SET_WEAKREF_NEXT(w, n) SET_VECTOR_ELT(w, 3, n)

static SEXP MakeCFinalizer(R_CFinalizer_t cfun);

static SEXP NewWeakRef(SEXP key, SEXP val, SEXP fin, Rboolean onexit)
{
    SEXP w;

    switch (TYPEOF(key)) {
    case NILSXP:
    case ENVSXP:
    case EXTPTRSXP:
    case BCODESXP:
	break;
    default: error(_("can only weakly reference/finalize reference objects"));
    }

    PROTECT(key);
    PROTECT(val = MAYBE_REFERENCED(val) ? duplicate(val) : val);
    PROTECT(fin);
    w = allocVector(VECSXP, WEAKREF_SIZE);
    SET_TYPEOF(w, WEAKREFSXP);
    if (key != R_NilValue) {
	/* If the key is R_NilValue we don't register the weak reference.
	   This is used in loading saved images. */
	SET_WEAKREF_KEY(w, key);
	SET_WEAKREF_VALUE(w, val);
	SET_WEAKREF_FINALIZER(w, fin);
	SET_WEAKREF_NEXT(w, R_weak_refs);
	CLEAR_READY_TO_FINALIZE(w);
	if (onexit)
	    SET_FINALIZE_ON_EXIT(w);
	else
	    CLEAR_FINALIZE_ON_EXIT(w);
	R_weak_refs = w;
    }
    UNPROTECT(3);
    return w;
}

SEXP R_MakeWeakRef(SEXP key, SEXP val, SEXP fin, Rboolean onexit)
{
    switch (TYPEOF(fin)) {
    case NILSXP:
    case CLOSXP:
    case BUILTINSXP:
    case SPECIALSXP:
	break;
    default: error(_("finalizer must be a function or NULL"));
    }
    return NewWeakRef(key, val, fin, onexit);
}

SEXP R_MakeWeakRefC(SEXP key, SEXP val, R_CFinalizer_t fin, Rboolean onexit)
{
    SEXP w;
    PROTECT(key);
    PROTECT(val);
    w = NewWeakRef(key, val, MakeCFinalizer(fin), onexit);
    UNPROTECT(2);
    return w;
}

static Rboolean R_finalizers_pending = FALSE;
static void CheckFinalizers(void)
{
    SEXP s;
    R_finalizers_pending = FALSE;
    for (s = R_weak_refs; s != R_NilValue; s = WEAKREF_NEXT(s)) {
	if (! NODE_IS_MARKED(WEAKREF_KEY(s)) && ! IS_READY_TO_FINALIZE(s))
	    SET_READY_TO_FINALIZE(s);
	if (IS_READY_TO_FINALIZE(s))
	    R_finalizers_pending = TRUE;
    }
}

/* C finalizers are stored in a CHARSXP.  It would be nice if we could
   use EXTPTRSXP's but these only hold a void *, and function pointers
   are not guaranteed to be compatible with a void *.  There should be
   a cleaner way of doing this, but this will do for now. --LT */
/* Changed to RAWSXP in 2.8.0 */
static Rboolean isCFinalizer(SEXP fun)
{
    return TYPEOF(fun) == RAWSXP;
    /*return TYPEOF(fun) == EXTPTRSXP;*/
}

static SEXP MakeCFinalizer(R_CFinalizer_t cfun)
{
    SEXP s = allocVector(RAWSXP, sizeof(R_CFinalizer_t));
    *((R_CFinalizer_t *) RAW(s)) = cfun;
    return s;
    /*return R_MakeExternalPtr((void *) cfun, R_NilValue, R_NilValue);*/
}

static R_CFinalizer_t GetCFinalizer(SEXP fun)
{
    return *((R_CFinalizer_t *) RAW(fun));
    /*return (R_CFinalizer_t) R_ExternalPtrAddr(fun);*/
}

SEXP R_WeakRefKey(SEXP w)
{
    if (TYPEOF(w) != WEAKREFSXP)
	error(_("not a weak reference"));
    return WEAKREF_KEY(w);
}

SEXP R_WeakRefValue(SEXP w)
{
    SEXP v;
    if (TYPEOF(w) != WEAKREFSXP)
	error(_("not a weak reference"));
    v = WEAKREF_VALUE(w);
    if (v != R_NilValue && NAMED(v) <= 1)
	SET_NAMED(v, 2);
    return v;
}

void R_RunWeakRefFinalizer(SEXP w)
{
    SEXP key, fun, e;
    if (TYPEOF(w) != WEAKREFSXP)
	error(_("not a weak reference"));
    key = WEAKREF_KEY(w);
    fun = WEAKREF_FINALIZER(w);
    SET_WEAKREF_KEY(w, R_NilValue);
    SET_WEAKREF_VALUE(w, R_NilValue);
    SET_WEAKREF_FINALIZER(w, R_NilValue);
    if (! IS_READY_TO_FINALIZE(w))
	SET_READY_TO_FINALIZE(w); /* insures removal from list on next gc */
    PROTECT(key);
    PROTECT(fun);
    if (isCFinalizer(fun)) {
	/* Must be a C finalizer. */
	R_CFinalizer_t cfun = GetCFinalizer(fun);
	cfun(key);
    }
    else if (fun != R_NilValue) {
	/* An R finalizer. */
	PROTECT(e = LCONS(fun, LCONS(key, R_NilValue)));
	eval(e, R_GlobalEnv);
	UNPROTECT(1);
    }
    UNPROTECT(2);
}

static Rboolean RunFinalizers(void)
{
    /* Prevent this function from running again when already in
       progress. Jumps can only occur inside the top level context
       where they will be caught, so the flag is guaranteed to be
       reset at the end. */
    static Rboolean running = FALSE;
    if (running) return FALSE;
    running = TRUE;

    volatile SEXP s, last;
    volatile Rboolean finalizer_run = FALSE;

    for (s = R_weak_refs, last = R_NilValue; s != R_NilValue;) {
	SEXP next = WEAKREF_NEXT(s);
	if (IS_READY_TO_FINALIZE(s)) {
	    /**** use R_ToplevelExec here? */
	    RCNTXT thiscontext;
	    RCNTXT * volatile saveToplevelContext;
	    volatile int savestack;
	    volatile SEXP topExp, oldHStack, oldRStack, oldRVal;
	    volatile Rboolean oldvis;
	    PROTECT(oldHStack = R_HandlerStack);
	    PROTECT(oldRStack = R_RestartStack);
	    PROTECT(oldRVal = R_ReturnedValue);
	    oldvis = R_Visible;
	    R_HandlerStack = R_NilValue;
	    R_RestartStack = R_NilValue;

	    finalizer_run = TRUE;

	    /* A top level context is established for the finalizer to
	       insure that any errors that might occur do not spill
	       into the call that triggered the collection. */
	    begincontext(&thiscontext, CTXT_TOPLEVEL, R_NilValue, R_GlobalEnv,
			 R_BaseEnv, R_NilValue, R_NilValue);
	    saveToplevelContext = R_ToplevelContext;
	    PROTECT(topExp = R_CurrentExpr);
	    savestack = R_PPStackTop;
	    /* The value of 'next' is protected to make it safe
	       for this routine to be called recursively from a
	       gc triggered by a finalizer. */
	    PROTECT(next);
	    if (! SETJMP(thiscontext.cjmpbuf)) {
		R_GlobalContext = R_ToplevelContext = &thiscontext;

		/* The entry in the weak reference list is removed
		   before running the finalizer.  This insures that a
		   finalizer is run only once, even if running it
		   raises an error. */
		if (last == R_NilValue)
		    R_weak_refs = next;
		else
		    SET_WEAKREF_NEXT(last, next);
		R_RunWeakRefFinalizer(s);
	    }
	    endcontext(&thiscontext);
	    UNPROTECT(1); /* next */
	    R_ToplevelContext = saveToplevelContext;
	    R_PPStackTop = savestack;
	    R_CurrentExpr = topExp;
	    R_HandlerStack = oldHStack;
	    R_RestartStack = oldRStack;
	    R_ReturnedValue = oldRVal;
	    R_Visible = oldvis;
	    UNPROTECT(4);/* topExp, oldRVal, oldRStack, oldHStack */
	}
	else last = s;
	s = next;
    }
    running = FALSE;
    R_finalizers_pending = FALSE;
    return finalizer_run;
}

void R_RunExitFinalizers(void)
{
    SEXP s;

    R_checkConstants(TRUE);

    for (s = R_weak_refs; s != R_NilValue; s = WEAKREF_NEXT(s))
	if (FINALIZE_ON_EXIT(s))
	    SET_READY_TO_FINALIZE(s);
    RunFinalizers();
}

void R_RunPendingFinalizers(void)
{
    if (R_finalizers_pending)
	RunFinalizers();
}

void R_RegisterFinalizerEx(SEXP s, SEXP fun, Rboolean onexit)
{
    R_MakeWeakRef(s, R_NilValue, fun, onexit);
}

void R_RegisterFinalizer(SEXP s, SEXP fun)
{
    R_RegisterFinalizerEx(s, fun, FALSE);
}

void R_RegisterCFinalizerEx(SEXP s, R_CFinalizer_t fun, Rboolean onexit)
{
    R_MakeWeakRefC(s, R_NilValue, fun, onexit);
}

void R_RegisterCFinalizer(SEXP s, R_CFinalizer_t fun)
{
    R_RegisterCFinalizerEx(s, fun, FALSE);
}

/* R interface function */

SEXP attribute_hidden do_regFinaliz(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    int onexit;

    checkArity(op, args);

    if (TYPEOF(CAR(args)) != ENVSXP && TYPEOF(CAR(args)) != EXTPTRSXP)
	error(_("first argument must be environment or external pointer"));
    if (TYPEOF(CADR(args)) != CLOSXP)
	error(_("second argument must be a function"));

    onexit = asLogical(CADDR(args));
    if(onexit == NA_LOGICAL)
	error(_("third argument must be 'TRUE' or 'FALSE'"));

    R_RegisterFinalizerEx(CAR(args), CADR(args), onexit);
    return R_NilValue;
}


/* The Generational Collector. */

#define PROCESS_NODES() do { \
    while (forwarded_nodes != NULL) { \
	s = forwarded_nodes; \
	forwarded_nodes = NEXT_NODE(forwarded_nodes); \
	SNAP_NODE(s, R_GenHeap[NODE_CLASS(s)].Old[NODE_GENERATION(s)]); \
	R_GenHeap[NODE_CLASS(s)].OldCount[NODE_GENERATION(s)]++; \
	FORWARD_CHILDREN(s); \
    } \
} while (0)

static void RunGenCollect(R_size_t size_needed)
{
    int i, gen, gens_collected;
    RCNTXT *ctxt;
    SEXP s;
    SEXP forwarded_nodes;

    bad_sexp_type_seen = 0;

    /* determine number of generations to collect */
    while (num_old_gens_to_collect < NUM_OLD_GENERATIONS) {
	if (collect_counts[num_old_gens_to_collect]-- <= 0) {
	    collect_counts[num_old_gens_to_collect] =
		collect_counts_max[num_old_gens_to_collect];
	    num_old_gens_to_collect++;
	}
	else break;
    }

#ifdef PROTECTCHECK
    num_old_gens_to_collect = NUM_OLD_GENERATIONS;
#endif

 again:
    gens_collected = num_old_gens_to_collect;

#ifndef EXPEL_OLD_TO_NEW
    /* eliminate old-to-new references in generations to collect by
       transferring referenced nodes to referring generation */
    for (gen = 0; gen < num_old_gens_to_collect; gen++) {
	for (i = 0; i < NUM_NODE_CLASSES; i++) {
	    s = NEXT_NODE(R_GenHeap[i].OldToNew[gen]);
	    while (s != R_GenHeap[i].OldToNew[gen]) {
		SEXP next = NEXT_NODE(s);
		DO_CHILDREN(s, AgeNodeAndChildren, gen);
		UNSNAP_NODE(s);
		if (NODE_GENERATION(s) != gen)
		    REprintf("****snapping into wrong generation\n");
		SNAP_NODE(s, R_GenHeap[i].Old[gen]);
		s = next;
	    }
	}
    }
#endif

    DEBUG_CHECK_NODE_COUNTS("at start");

    /* unmark all marked nodes in old generations to be collected and
       move to New space */
    for (gen = 0; gen < num_old_gens_to_collect; gen++) {
	for (i = 0; i < NUM_NODE_CLASSES; i++) {
	    R_GenHeap[i].OldCount[gen] = 0;
	    s = NEXT_NODE(R_GenHeap[i].Old[gen]);
	    while (s != R_GenHeap[i].Old[gen]) {
		SEXP next = NEXT_NODE(s);
		if (gen < NUM_OLD_GENERATIONS - 1)
		    SET_NODE_GENERATION(s, gen + 1);
		UNMARK_NODE(s);
		s = next;
	    }
	    if (NEXT_NODE(R_GenHeap[i].Old[gen]) != R_GenHeap[i].Old[gen])
		BULK_MOVE(R_GenHeap[i].Old[gen], R_GenHeap[i].New);
	}
    }

    forwarded_nodes = NULL;

#ifndef EXPEL_OLD_TO_NEW
    /* scan nodes in uncollected old generations with old-to-new pointers */
    for (gen = num_old_gens_to_collect; gen < NUM_OLD_GENERATIONS; gen++)
	for (i = 0; i < NUM_NODE_CLASSES; i++)
	    for (s = NEXT_NODE(R_GenHeap[i].OldToNew[gen]);
		 s != R_GenHeap[i].OldToNew[gen];
		 s = NEXT_NODE(s))
		FORWARD_CHILDREN(s);
#endif

    /* forward all roots */
    FORWARD_NODE(R_NilValue);	           /* Builtin constants */
    FORWARD_NODE(NA_STRING);
    FORWARD_NODE(R_BlankString);
    FORWARD_NODE(R_BlankScalarString);
    FORWARD_NODE(R_CurrentExpression);
    FORWARD_NODE(R_UnboundValue);
    FORWARD_NODE(R_RestartToken);
    FORWARD_NODE(R_MissingArg);
    FORWARD_NODE(R_InBCInterpreter);

    FORWARD_NODE(R_GlobalEnv);	           /* Global environment */
    FORWARD_NODE(R_BaseEnv);
    FORWARD_NODE(R_EmptyEnv);
    FORWARD_NODE(R_Warnings);	           /* Warnings, if any */
    FORWARD_NODE(R_ReturnedValue);

    FORWARD_NODE(R_HandlerStack);          /* Condition handler stack */
    FORWARD_NODE(R_RestartStack);          /* Available restarts stack */

    FORWARD_NODE(R_BCbody);                /* Current byte code object */
    FORWARD_NODE(R_Srcref);                /* Current source reference */

    FORWARD_NODE(R_TrueValue);
    FORWARD_NODE(R_FalseValue);
    FORWARD_NODE(R_LogicalNAValue);

    FORWARD_NODE(R_print.na_string);
    FORWARD_NODE(R_print.na_string_noquote);

    if (R_SymbolTable != NULL)             /* in case of GC during startup */
	for (i = 0; i < HSIZE; i++)        /* Symbol table */
	    FORWARD_NODE(R_SymbolTable[i]);

    if (R_CurrentExpr != NULL)	           /* Current expression */
	FORWARD_NODE(R_CurrentExpr);

    for (i = 0; i < R_MaxDevices; i++) {   /* Device display lists */
	pGEDevDesc gdd = GEgetDevice(i);
	if (gdd) {
	    FORWARD_NODE(gdd->displayList);
	    FORWARD_NODE(gdd->savedSnapshot);
	    if (gdd->dev)
		FORWARD_NODE(gdd->dev->eventEnv);
	}
    }

    for (ctxt = R_GlobalContext ; ctxt != NULL ; ctxt = ctxt->nextcontext) {
	FORWARD_NODE(ctxt->conexit);       /* on.exit expressions */
	FORWARD_NODE(ctxt->promargs);	   /* promises supplied to closure */
	FORWARD_NODE(ctxt->callfun);       /* the closure called */
	FORWARD_NODE(ctxt->sysparent);     /* calling environment */
	FORWARD_NODE(ctxt->call);          /* the call */
	FORWARD_NODE(ctxt->cloenv);        /* the closure environment */
	FORWARD_NODE(ctxt->bcbody);        /* the current byte code object */
	FORWARD_NODE(ctxt->handlerstack);  /* the condition handler stack */
	FORWARD_NODE(ctxt->restartstack);  /* the available restarts stack */
	FORWARD_NODE(ctxt->srcref);	   /* the current source reference */
	FORWARD_NODE(ctxt->returnValue);   /* For on.exit calls */
    }

    FORWARD_NODE(R_PreciousList);

    for (i = 0; i < R_PPStackTop; i++)	   /* Protected pointers */
	FORWARD_NODE(R_PPStack[i]);

    FORWARD_NODE(R_VStack);		   /* R_alloc stack */

    for (R_bcstack_t *sp = R_BCNodeStackBase; sp < R_BCNodeStackTop; sp++) {
#ifdef TYPED_STACK
	if (sp->tag == RAWMEM_TAG)
	    sp += sp->u.ival;
	else if (sp->tag == 0 || IS_PARTIAL_SXP_TAG(sp->tag))
	    FORWARD_NODE(sp->u.sxpval);
#else
	FORWARD_NODE(*sp);
#endif
    }
    FORWARD_NODE(R_CachedScalarReal);
    FORWARD_NODE(R_CachedScalarInteger);

    /* main processing loop */
    PROCESS_NODES();

    /* identify weakly reachable nodes */
    {
	Rboolean recheck_weak_refs;
	do {
	    recheck_weak_refs = FALSE;
	    for (s = R_weak_refs; s != R_NilValue; s = WEAKREF_NEXT(s)) {
		if (NODE_IS_MARKED(WEAKREF_KEY(s))) {
		    if (! NODE_IS_MARKED(WEAKREF_VALUE(s))) {
			recheck_weak_refs = TRUE;
			FORWARD_NODE(WEAKREF_VALUE(s));
		    }
		    if (! NODE_IS_MARKED(WEAKREF_FINALIZER(s))) {
			recheck_weak_refs = TRUE;
			FORWARD_NODE(WEAKREF_FINALIZER(s));
		    }
		}
	    }
	    PROCESS_NODES();
	} while (recheck_weak_refs);
    }

    /* mark nodes ready for finalizing */
    CheckFinalizers();

    /* process the weak reference chain */
    for (s = R_weak_refs; s != R_NilValue; s = WEAKREF_NEXT(s)) {
	FORWARD_NODE(s);
	FORWARD_NODE(WEAKREF_KEY(s));
	FORWARD_NODE(WEAKREF_VALUE(s));
	FORWARD_NODE(WEAKREF_FINALIZER(s));
    }
    PROCESS_NODES();

    DEBUG_CHECK_NODE_COUNTS("after processing forwarded list");

    /* process CHARSXP cache */
    if (R_StringHash != NULL) /* in case of GC during initialization */
    {
	SEXP t;
	int nc = 0;
	for (i = 0; i < LENGTH(R_StringHash); i++) {
	    s = VECTOR_ELT(R_StringHash, i);
	    t = R_NilValue;
	    while (s != R_NilValue) {
		if (! NODE_IS_MARKED(CXHEAD(s))) { /* remove unused CHARSXP and cons cell */
		    if (t == R_NilValue) /* head of list */
			VECTOR_ELT(R_StringHash, i) = CXTAIL(s);
		    else
			CXTAIL(t) = CXTAIL(s);
		    s = CXTAIL(s);
		    continue;
		}
		FORWARD_NODE(s);
		FORWARD_NODE(CXHEAD(s));
		t = s;
		s = CXTAIL(s);
	    }
	    if(VECTOR_ELT(R_StringHash, i) != R_NilValue) nc++;
	}
	SET_TRUELENGTH(R_StringHash, nc); /* SET_HASHPRI, really */
    }
    FORWARD_NODE(R_StringHash);
    PROCESS_NODES();

#ifdef PROTECTCHECK
    for(i=0; i< NUM_SMALL_NODE_CLASSES;i++){
	s = NEXT_NODE(R_GenHeap[i].New);
	while (s != R_GenHeap[i].New) {
	    SEXP next = NEXT_NODE(s);
	    if (TYPEOF(s) != NEWSXP) {
		if (TYPEOF(s) != FREESXP) {
		    SETOLDTYPE(s, TYPEOF(s));
		    TYPEOF(s) = FREESXP;
		}
		if (gc_inhibit_release)
		    FORWARD_NODE(s);
	    }
	    s = next;
	}
    }
    for (i = CUSTOM_NODE_CLASS; i <= LARGE_NODE_CLASS; i++) {
	s = NEXT_NODE(R_GenHeap[i].New);
	while (s != R_GenHeap[i].New) {
	    SEXP next = NEXT_NODE(s);
	    if (TYPEOF(s) != NEWSXP) {
		if (TYPEOF(s) != FREESXP) {
		    /**** could also leave this alone and restore the old
			  node type in ReleaseLargeFreeVectors before
			  calculating size */
		    if (CHAR(s) != NULL) {
			R_size_t size = getVecSizeInVEC(s);
			SETLENGTH(s, size);
		    }
		    SETOLDTYPE(s, TYPEOF(s));
		    TYPEOF(s) = FREESXP;
		}
		if (gc_inhibit_release)
		    FORWARD_NODE(s);
	    }
	    s = next;
	}
    }
    if (gc_inhibit_release)
	PROCESS_NODES();
#endif

    /* release large vector allocations */
    ReleaseLargeFreeVectors();

    DEBUG_CHECK_NODE_COUNTS("after releasing large allocated nodes");

    /* tell Valgrind about free nodes */
#if VALGRIND_LEVEL > 1
    for(i = 1; i< NUM_NODE_CLASSES; i++) {
	for(s = NEXT_NODE(R_GenHeap[i].New);
	    s != R_GenHeap[i].Free;
	    s = NEXT_NODE(s)) {
	    VALGRIND_MAKE_MEM_NOACCESS(DATAPTR(s),
				       NodeClassSize[i]*sizeof(VECREC));
	}
    }
#endif

    /* reset Free pointers */
    for (i = 0; i < NUM_NODE_CLASSES; i++)
	R_GenHeap[i].Free = NEXT_NODE(R_GenHeap[i].New);


    /* update heap statistics */
    R_Collected = R_NSize;
    R_SmallVallocSize = 0;
    for (gen = 0; gen < NUM_OLD_GENERATIONS; gen++) {
	for (i = 1; i < NUM_SMALL_NODE_CLASSES; i++)
	    R_SmallVallocSize += R_GenHeap[i].OldCount[gen] * NodeClassSize[i];
	for (i = 0; i < NUM_NODE_CLASSES; i++)
	    R_Collected -= R_GenHeap[i].OldCount[gen];
    }
    R_NodesInUse = R_NSize - R_Collected;

    if (num_old_gens_to_collect < NUM_OLD_GENERATIONS) {
	if (R_Collected < R_MinFreeFrac * R_NSize ||
	    VHEAP_FREE() < size_needed + R_MinFreeFrac * R_VSize) {
	    num_old_gens_to_collect++;
	    if (R_Collected <= 0 || VHEAP_FREE() < size_needed)
		goto again;
	}
	else num_old_gens_to_collect = 0;
    }
    else num_old_gens_to_collect = 0;

    gen_gc_counts[gens_collected]++;

    if (gens_collected == NUM_OLD_GENERATIONS) {
	/**** do some adjustment for intermediate collections? */
	AdjustHeapSize(size_needed);
	TryToReleasePages();
	DEBUG_CHECK_NODE_COUNTS("after heap adjustment");
    }
    else if (gens_collected > 0) {
	TryToReleasePages();
	DEBUG_CHECK_NODE_COUNTS("after heap adjustment");
    }
#ifdef SORT_NODES
    if (gens_collected == NUM_OLD_GENERATIONS)
	SortNodes();
#endif

    if (R_check_constants > 2 ||
	    (R_check_constants > 1 && gens_collected == NUM_OLD_GENERATIONS))
	R_checkConstants(TRUE);

    if (gc_reporting) {
	REprintf("Garbage collection %d = %d", gc_count, gen_gc_counts[0]);
	for (i = 0; i < NUM_OLD_GENERATIONS; i++)
	    REprintf("+%d", gen_gc_counts[i + 1]);
	REprintf(" (level %d) ... ", gens_collected);
	DEBUG_GC_SUMMARY(gens_collected == NUM_OLD_GENERATIONS);
    }
}

/* public interface for controlling GC torture settings */
/* maybe, but in no header */
void R_gc_torture(int gap, int wait, Rboolean inhibit)
{
    if (gap != NA_INTEGER && gap >= 0)
	gc_force_wait = gc_force_gap = gap;
    if (gap > 0) {
	if (wait != NA_INTEGER && wait > 0)
	    gc_force_wait = wait;
    }
#ifdef PROTECTCHECK
    if (gap > 0) {
	if (inhibit != NA_LOGICAL)
	    gc_inhibit_release = inhibit;
    }
    else gc_inhibit_release = FALSE;
#endif
}

SEXP attribute_hidden do_gctorture(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    int gap;
    SEXP old = ScalarLogical(gc_force_wait > 0);

    checkArity(op, args);

    if (isLogical(CAR(args))) {
	Rboolean on = asLogical(CAR(args));
	if (on == NA_LOGICAL) gap = NA_INTEGER;
	else if (on) gap = 1;
	else gap = 0;
    }
    else gap = asInteger(CAR(args));

    R_gc_torture(gap, 0, FALSE);

    return old;
}

SEXP attribute_hidden do_gctorture2(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    int gap, wait;
    Rboolean inhibit;
    int old = gc_force_gap;

    checkArity(op, args);
    gap = asInteger(CAR(args));
    wait = asInteger(CADR(args));
    inhibit = asLogical(CADDR(args));
    R_gc_torture(gap, wait, inhibit);

    return ScalarInteger(old);
}

/* initialize gctorture settings from environment variables */
static void init_gctorture(void)
{
    char *arg = getenv("R_GCTORTURE");
    if (arg != NULL) {
	int gap = atoi(arg);
	if (gap > 0) {
	    gc_force_wait = gc_force_gap = gap;
	    arg = getenv("R_GCTORTURE_WAIT");
	    if (arg != NULL) {
		int wait = atoi(arg);
		if (wait > 0)
		    gc_force_wait = wait;
	    }
#ifdef PROTECTCHECK
	    arg = getenv("R_GCTORTURE_INHIBIT_RELEASE");
	    if (arg != NULL) {
		int inhibit = atoi(arg);
		if (inhibit > 0) gc_inhibit_release = TRUE;
		else gc_inhibit_release = FALSE;
	    }
#endif
	}
    }
}

SEXP attribute_hidden do_gcinfo(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    int i;
    SEXP old = ScalarLogical(gc_reporting);
    checkArity(op, args);
    i = asLogical(CAR(args));
    if (i != NA_LOGICAL)
	gc_reporting = i;
    return old;
}

/* reports memory use to profiler in eval.c */

void attribute_hidden get_current_mem(size_t *smallvsize,
				      size_t *largevsize,
				      size_t *nodes)
{
    *smallvsize = R_SmallVallocSize;
    *largevsize = R_LargeVallocSize;
    *nodes = R_NodesInUse * sizeof(SEXPREC);
    return;
}

SEXP attribute_hidden do_gc(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    SEXP value;
    int ogc, reset_max;
    R_size_t onsize = R_NSize /* can change during collection */;

    checkArity(op, args);
    ogc = gc_reporting;
    gc_reporting = asLogical(CAR(args));
    reset_max = asLogical(CADR(args));
    num_old_gens_to_collect = NUM_OLD_GENERATIONS;
    R_gc();

    gc_reporting = ogc;
    /*- now return the [used , gc trigger size] for cells and heap */
    PROTECT(value = allocVector(REALSXP, 14));
    REAL(value)[0] = onsize - R_Collected;
    REAL(value)[1] = R_VSize - VHEAP_FREE();
    REAL(value)[4] = R_NSize;
    REAL(value)[5] = R_VSize;
    /* next four are in 0.1Mb, rounded up */
    REAL(value)[2] = 0.1*ceil(10. * (onsize - R_Collected)/Mega * sizeof(SEXPREC));
    REAL(value)[3] = 0.1*ceil(10. * (R_VSize - VHEAP_FREE())/Mega * vsfac);
    REAL(value)[6] = 0.1*ceil(10. * R_NSize/Mega * sizeof(SEXPREC));
    REAL(value)[7] = 0.1*ceil(10. * R_VSize/Mega * vsfac);
    REAL(value)[8] = (R_MaxNSize < R_SIZE_T_MAX) ?
	0.1*ceil(10. * R_MaxNSize/Mega * sizeof(SEXPREC)) : NA_REAL;
    REAL(value)[9] = (R_MaxVSize < R_SIZE_T_MAX) ?
	0.1*ceil(10. * R_MaxVSize/Mega * vsfac) : NA_REAL;
    if (reset_max){
	    R_N_maxused = onsize - R_Collected;
	    R_V_maxused = R_VSize - VHEAP_FREE();
    }
    REAL(value)[10] = R_N_maxused;
    REAL(value)[11] = R_V_maxused;
    REAL(value)[12] = 0.1*ceil(10. * R_N_maxused/Mega*sizeof(SEXPREC));
    REAL(value)[13] = 0.1*ceil(10. * R_V_maxused/Mega*vsfac);
    UNPROTECT(1);
    return value;
}


static void NORET mem_err_heap(R_size_t size)
{
    errorcall(R_NilValue, _("vector memory exhausted (limit reached?)"));
}


static void NORET mem_err_cons(void)
{
    errorcall(R_NilValue, _("cons memory exhausted (limit reached?)"));
}

static void NORET mem_err_malloc(R_size_t size)
{
    errorcall(R_NilValue, _("memory exhausted (limit reached?)"));
}

/* InitMemory : Initialise the memory to be used in R. */
/* This includes: stack space, node space and vector space */

#define PP_REDZONE_SIZE 1000L
static int R_StandardPPStackSize, R_RealPPStackSize;

void attribute_hidden InitMemory()
{
    int i;
    int gen;

    init_gctorture();
    init_gc_grow_settings();

    gc_reporting = R_Verbose;
    R_StandardPPStackSize = R_PPStackSize;
    R_RealPPStackSize = R_PPStackSize + PP_REDZONE_SIZE;
    if (!(R_PPStack = (SEXP *) malloc(R_RealPPStackSize * sizeof(SEXP))))
	R_Suicide("couldn't allocate memory for pointer stack");
    R_PPStackTop = 0;
#if VALGRIND_LEVEL > 1
    VALGRIND_MAKE_MEM_NOACCESS(R_PPStack+R_PPStackSize, PP_REDZONE_SIZE);
#endif
    vsfac = sizeof(VECREC);
    R_VSize = (R_VSize + 1)/vsfac;
    if (R_MaxVSize < R_SIZE_T_MAX) R_MaxVSize = (R_MaxVSize + 1)/vsfac;

    UNMARK_NODE(&UnmarkedNodeTemplate);

    for (i = 0; i < NUM_NODE_CLASSES; i++) {
      for (gen = 0; gen < NUM_OLD_GENERATIONS; gen++) {
	R_GenHeap[i].Old[gen] = &R_GenHeap[i].OldPeg[gen];
	SET_PREV_NODE(R_GenHeap[i].Old[gen], R_GenHeap[i].Old[gen]);
	SET_NEXT_NODE(R_GenHeap[i].Old[gen], R_GenHeap[i].Old[gen]);

#ifndef EXPEL_OLD_TO_NEW
	R_GenHeap[i].OldToNew[gen] = &R_GenHeap[i].OldToNewPeg[gen];
	SET_PREV_NODE(R_GenHeap[i].OldToNew[gen], R_GenHeap[i].OldToNew[gen]);
	SET_NEXT_NODE(R_GenHeap[i].OldToNew[gen], R_GenHeap[i].OldToNew[gen]);
#endif

	R_GenHeap[i].OldCount[gen] = 0;
      }
      R_GenHeap[i].New = &R_GenHeap[i].NewPeg;
      SET_PREV_NODE(R_GenHeap[i].New, R_GenHeap[i].New);
      SET_NEXT_NODE(R_GenHeap[i].New, R_GenHeap[i].New);
    }

    for (i = 0; i < NUM_NODE_CLASSES; i++)
	R_GenHeap[i].Free = NEXT_NODE(R_GenHeap[i].New);

    SET_NODE_CLASS(&UnmarkedNodeTemplate, 0);
    orig_R_NSize = R_NSize;
    orig_R_VSize = R_VSize;

    /* R_NilValue */
    /* THIS MUST BE THE FIRST CONS CELL ALLOCATED */
    /* OR ARMAGEDDON HAPPENS. */
    /* Field assignments for R_NilValue must not go through write barrier
       since the write barrier prevents assignments to R_NilValue's fields.
       because of checks for nil */
    GET_FREE_NODE(R_NilValue);
    R_NilValue->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(R_NilValue);
    SET_REFCNT(R_NilValue, REFCNTMAX);
    SET_TYPEOF(R_NilValue, NILSXP);
    CAR(R_NilValue) = R_NilValue;
    CDR(R_NilValue) = R_NilValue;
    TAG(R_NilValue) = R_NilValue;
    ATTRIB(R_NilValue) = R_NilValue;
    MARK_NOT_MUTABLE(R_NilValue);

    R_BCNodeStackBase =
	(R_bcstack_t *) malloc(R_BCNODESTACKSIZE * sizeof(R_bcstack_t));
    if (R_BCNodeStackBase == NULL)
	R_Suicide("couldn't allocate node stack");
#ifdef BC_INT_STACK
    R_BCIntStackBase =
      (IStackval *) malloc(R_BCINTSTACKSIZE * sizeof(IStackval));
    if (R_BCIntStackBase == NULL)
	R_Suicide("couldn't allocate integer stack");
#endif
    R_BCNodeStackTop = R_BCNodeStackBase;
    R_BCNodeStackEnd = R_BCNodeStackBase + R_BCNODESTACKSIZE;
#ifdef BC_INT_STACK
    R_BCIntStackTop = R_BCIntStackBase;
    R_BCIntStackEnd = R_BCIntStackBase + R_BCINTSTACKSIZE;
#endif

    R_weak_refs = R_NilValue;

    R_HandlerStack = R_RestartStack = R_NilValue;

    /*  Unbound values which are to be preserved through GCs */
    R_PreciousList = R_NilValue;

    /*  The current source line */
    R_Srcref = R_NilValue;

    /* R_TrueValue and R_FalseValue */
    R_TrueValue = mkTrue();
    MARK_NOT_MUTABLE(R_TrueValue);
    R_FalseValue = mkFalse();
    MARK_NOT_MUTABLE(R_FalseValue);
    R_LogicalNAValue = allocVector(LGLSXP, 1);
    LOGICAL(R_LogicalNAValue)[0] = NA_LOGICAL;
    MARK_NOT_MUTABLE(R_LogicalNAValue);
}

/* Since memory allocated from the heap is non-moving, R_alloc just
   allocates off the heap as RAWSXP/REALSXP and maintains the stack of
   allocations through the ATTRIB pointer.  The stack pointer R_VStack
   is traced by the collector. */
void *vmaxget(void)
{
    return (void *) R_VStack;
}

void vmaxset(const void *ovmax)
{
    R_VStack = (SEXP) ovmax;
}

char *R_alloc(size_t nelem, int eltsize)
{
    R_size_t size = nelem * eltsize;
    /* doubles are a precaution against integer overflow on 32-bit */
    double dsize = (double) nelem * eltsize;
    if (dsize > 0) {
	SEXP s;
#ifdef LONG_VECTOR_SUPPORT
	/* 64-bit platform: previous version used REALSXPs */
	if(dsize > R_XLEN_T_MAX)  /* currently 4096 TB */
	    error(_("cannot allocate memory block of size %0.f Tb"),
		  dsize/R_pow_di(1024.0, 4));
	s = allocVector(RAWSXP, size + 1);
#else
	if(dsize > R_LEN_T_MAX) /* must be in the Gb range */
	    error(_("cannot allocate memory block of size %0.1f Gb"),
		  dsize/R_pow_di(1024.0, 3));
	s = allocVector(RAWSXP, size + 1);
#endif
	ATTRIB(s) = R_VStack;
	R_VStack = s;
	return (char *) DATAPTR(s);
    }
    /* One programmer has relied on this, but it is undocumented! */
    else return NULL;
}

#ifdef HAVE_STDALIGN_H
# include <stdalign.h>
#endif

#include <stdint.h>

long double *R_allocLD(size_t nelem)
{
#if __alignof_is_defined
    // This is C11: picky compilers may warn.
    size_t ld_align = alignof(long double);
#elif __GNUC__
    // This is C99, but do not rely on it.
    size_t ld_align = offsetof(struct { char __a; long double __b; }, __b);
#else
    size_t ld_align = 0x0F; // value of x86_64, known others are 4 or 8
#endif
    if (ld_align > 8) {
	uintptr_t tmp = (uintptr_t) R_alloc(nelem + 1, sizeof(long double));
	tmp = (tmp + ld_align - 1) & ~ld_align;
	return (long double *) tmp;
    } else {
	return (long double *) R_alloc(nelem, sizeof(long double));
    }
}


/* S COMPATIBILITY */

char *S_alloc(long nelem, int eltsize)
{
    R_size_t size  = nelem * eltsize;
    char *p = R_alloc(nelem, eltsize);

    if(p) memset(p, 0, size);
    return p;
}


char *S_realloc(char *p, long new, long old, int size)
{
    size_t nold;
    char *q;
    /* shrinking is a no-op */
    if(new <= old) return p; // so nnew > 0 below
    q = R_alloc((size_t)new, size);
    nold = (size_t)old * size;
    memcpy(q, p, nold);
    memset(q + nold, 0, (size_t)new*size - nold);
    return q;
}

/* "allocSExp" allocate a SEXPREC */
/* call gc if necessary */

SEXP allocSExp(SEXPTYPE t)
{
    SEXP s;
    if (FORCE_GC || NO_FREE_NODES()) {
	R_gc_internal(0);
	if (NO_FREE_NODES())
	    mem_err_cons();
    }
    GET_FREE_NODE(s);
    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(s);
    SET_TYPEOF(s, t);
    CAR(s) = R_NilValue;
    CDR(s) = R_NilValue;
    TAG(s) = R_NilValue;
    ATTRIB(s) = R_NilValue;
    return s;
}

static SEXP allocSExpNonCons(SEXPTYPE t)
{
    SEXP s;
    if (FORCE_GC || NO_FREE_NODES()) {
	R_gc_internal(0);
	if (NO_FREE_NODES())
	    mem_err_cons();
    }
    GET_FREE_NODE(s);
    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(s);
    SET_TYPEOF(s, t);
    TAG(s) = R_NilValue;
    ATTRIB(s) = R_NilValue;
    return s;
}

/* cons is defined directly to avoid the need to protect its arguments
   unless a GC will actually occur. */
SEXP cons(SEXP car, SEXP cdr)
{
    SEXP s;
    if (FORCE_GC || NO_FREE_NODES()) {
	PROTECT(car);
	PROTECT(cdr);
	R_gc_internal(0);
	UNPROTECT(2);
	if (NO_FREE_NODES())
	    mem_err_cons();
    }

    if (NEED_NEW_PAGE()) {
	PROTECT(car);
	PROTECT(cdr);
	GET_FREE_NODE(s);
	UNPROTECT(2);
    }
    else
	QUICK_GET_FREE_NODE(s);

    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(s);
    SET_TYPEOF(s, LISTSXP);
    CAR(s) = CHK(car); if (car) INCREMENT_REFCNT(car);
    CDR(s) = CHK(cdr); if (cdr) INCREMENT_REFCNT(cdr);
    TAG(s) = R_NilValue;
    ATTRIB(s) = R_NilValue;
    return s;
}

SEXP CONS_NR(SEXP car, SEXP cdr)
{
    SEXP s;
    if (FORCE_GC || NO_FREE_NODES()) {
	PROTECT(car);
	PROTECT(cdr);
	R_gc_internal(0);
	UNPROTECT(2);
	if (NO_FREE_NODES())
	    mem_err_cons();
    }

    if (NEED_NEW_PAGE()) {
	PROTECT(car);
	PROTECT(cdr);
	GET_FREE_NODE(s);
	UNPROTECT(2);
    }
    else
	QUICK_GET_FREE_NODE(s);

    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(s);
    DISABLE_REFCNT(s);
    SET_TYPEOF(s, LISTSXP);
    CAR(s) = CHK(car);
    CDR(s) = CHK(cdr);
    TAG(s) = R_NilValue;
    ATTRIB(s) = R_NilValue;
    return s;
}

/*----------------------------------------------------------------------

  NewEnvironment

  Create an environment by extending "rho" with a frame obtained by
  pairing the variable names given by the tags on "namelist" with
  the values given by the elements of "valuelist".

  NewEnvironment is defined directly to avoid the need to protect its
  arguments unless a GC will actually occur.  This definition allows
  the namelist argument to be shorter than the valuelist; in this
  case the remaining values must be named already.  (This is useful
  in cases where the entire valuelist is already named--namelist can
  then be R_NilValue.)

  The valuelist is destructively modified and used as the
  environment's frame.
*/
SEXP NewEnvironment(SEXP namelist, SEXP valuelist, SEXP rho)
{
    SEXP v, n, newrho;

    if (FORCE_GC || NO_FREE_NODES()) {
	PROTECT(namelist);
	PROTECT(valuelist);
	PROTECT(rho);
	R_gc_internal(0);
	UNPROTECT(3);
	if (NO_FREE_NODES())
	    mem_err_cons();
    }

    if (NEED_NEW_PAGE()) {
	PROTECT(namelist);
	PROTECT(valuelist);
	PROTECT(rho);
	GET_FREE_NODE(newrho);
	UNPROTECT(3);
    }
    else
	QUICK_GET_FREE_NODE(newrho);

    newrho->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(newrho);
    SET_TYPEOF(newrho, ENVSXP);
    FRAME(newrho) = valuelist;
    ENCLOS(newrho) = CHK(rho);
    HASHTAB(newrho) = R_NilValue;
    ATTRIB(newrho) = R_NilValue;

    v = CHK(valuelist);
    n = CHK(namelist);
    while (v != R_NilValue && n != R_NilValue) {
	SET_TAG(v, TAG(n));
	v = CDR(v);
	n = CDR(n);
    }
    return (newrho);
}

/* mkPROMISE is defined directly do avoid the need to protect its arguments
   unless a GC will actually occur. */
SEXP attribute_hidden mkPROMISE(SEXP expr, SEXP rho)
{
    SEXP s;
    if (FORCE_GC || NO_FREE_NODES()) {
	PROTECT(expr);
	PROTECT(rho);
	R_gc_internal(0);
	UNPROTECT(2);
	if (NO_FREE_NODES())
	    mem_err_cons();
    }

    if (NEED_NEW_PAGE()) {
	PROTECT(expr);
	PROTECT(rho);
	GET_FREE_NODE(s);
	UNPROTECT(2);
    }
    else
	QUICK_GET_FREE_NODE(s);

    /* precaution to ensure code does not get modified via
       substitute() and the like */
    if (NAMED(expr) < 2) SET_NAMED(expr, 2);

    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
    INIT_REFCNT(s);
    SET_TYPEOF(s, PROMSXP);
    PRCODE(s) = CHK(expr);
    PRENV(s) = CHK(rho);
    PRVALUE(s) = R_UnboundValue;
    PRSEEN(s) = 0;
    ATTRIB(s) = R_NilValue;
    return s;
}

SEXP R_mkEVPROMISE(SEXP expr, SEXP val)
{
    SEXP prom = mkPROMISE(expr, R_NilValue);
    SET_PRVALUE(prom, val);
    return prom;
}

SEXP R_mkEVPROMISE_NR(SEXP expr, SEXP val)
{
    SEXP prom = mkPROMISE(expr, R_NilValue);
    DISABLE_REFCNT(prom);
    SET_PRVALUE(prom, val);
    return prom;
}

/* support for custom allocators that allow vectors to be allocated
   using non-standard means such as COW mmap() */

static void *custom_node_alloc(R_allocator_t *allocator, size_t size) {
    if (!allocator || !allocator->mem_alloc) return NULL;
    void *ptr = allocator->mem_alloc(allocator, size + sizeof(R_allocator_t));
    if (ptr) {
	R_allocator_t *ca = (R_allocator_t*) ptr;
	*ca = *allocator;
	return (void*) (ca + 1);
    }
    return NULL;
}

static void custom_node_free(void *ptr) {
    if (ptr) {
	R_allocator_t *allocator = ((R_allocator_t*) ptr) - 1;
	allocator->mem_free(allocator, (void*)allocator);
    }
}

/* All vector objects must be a multiple of sizeof(SEXPREC_ALIGN)
   bytes so that alignment is preserved for all objects */

/* Allocate a vector object (and also list-like objects).
   This ensures only validity of list-like (LISTSXP, VECSXP, EXPRSXP),
   STRSXP and CHARSXP types;  e.g., atomic types remain un-initialized
   and must be initialized upstream, e.g., in do_makevector().
*/
#define intCHARSXP 73

SEXP allocVector3(SEXPTYPE type, R_xlen_t length, R_allocator_t *allocator)
{
    SEXP s;     /* For the generational collector it would be safer to
		   work in terms of a VECSEXP here, but that would
		   require several casts below... */
    R_size_t size = 0, alloc_size, old_R_VSize;
    int node_class;
#if VALGRIND_LEVEL > 0
    R_size_t actual_size = 0;
#endif

    /* Handle some scalars directly to improve speed. */
    if (length == 1) {
	switch(type) {
	case REALSXP:
	case INTSXP:
	case LGLSXP:
	    node_class = 1;
	    alloc_size = NodeClassSize[1];
	    if (FORCE_GC || NO_FREE_NODES() || VHEAP_FREE() < alloc_size) {
		R_gc_internal(alloc_size);
		if (NO_FREE_NODES())
		    mem_err_cons();
		if (VHEAP_FREE() < alloc_size)
		    mem_err_heap(size);
	    }

	    CLASS_GET_FREE_NODE(node_class, s);
#if VALGRIND_LEVEL > 1
	    switch(type) {
	    case REALSXP: actual_size = sizeof(double); break;
	    case INTSXP: actual_size = sizeof(int); break;
	    case LGLSXP: actual_size = sizeof(int); break;
	    }
	    VALGRIND_MAKE_MEM_UNDEFINED(DATAPTR(s), actual_size);
#endif
	    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
	    SET_NODE_CLASS(s, node_class);
	    R_SmallVallocSize += alloc_size;
	    ATTRIB(s) = R_NilValue;
	    SET_TYPEOF(s, type);
	    SET_SHORT_VEC_LENGTH(s, (R_len_t) length); // is 1
	    SET_SHORT_VEC_TRUELENGTH(s, 0);
	    SET_NAMED(s, 0);
	    INIT_REFCNT(s);
	    return(s);
	}
    }

    if (length > R_XLEN_T_MAX)
	error(_("vector is too large")); /**** put length into message */
    else if (length < 0 )
	error(_("negative length vectors are not allowed"));
    /* number of vector cells to allocate */
    switch (type) {
    case NILSXP:
	return R_NilValue;
    case RAWSXP:
	size = BYTE2VEC(length);
#if VALGRIND_LEVEL > 0
	actual_size = length;
#endif
	break;
    case CHARSXP:
	error("use of allocVector(CHARSXP ...) is defunct\n");
    case intCHARSXP:
	type = CHARSXP;
	size = BYTE2VEC(length + 1);
#if VALGRIND_LEVEL > 0
	actual_size = length + 1;
#endif
	break;
    case LGLSXP:
    case INTSXP:
	if (length <= 0)
	    size = 0;
	else {
	    if (length > R_SIZE_T_MAX / sizeof(int))
		error(_("cannot allocate vector of length %d"), length);
	    size = INT2VEC(length);
#if VALGRIND_LEVEL > 0
	    actual_size = length*sizeof(int);
#endif
	}
	break;
    case REALSXP:
	if (length <= 0)
	    size = 0;
	else {
	    if (length > R_SIZE_T_MAX / sizeof(double))
		error(_("cannot allocate vector of length %d"), length);
	    size = FLOAT2VEC(length);
#if VALGRIND_LEVEL > 0
	    actual_size = length * sizeof(double);
#endif
	}
	break;
    case CPLXSXP:
	if (length <= 0)
	    size = 0;
	else {
	    if (length > R_SIZE_T_MAX / sizeof(Rcomplex))
		error(_("cannot allocate vector of length %d"), length);
	    size = COMPLEX2VEC(length);
#if VALGRIND_LEVEL > 0
	    actual_size = length * sizeof(Rcomplex);
#endif
	}
	break;
    case STRSXP:
    case EXPRSXP:
    case VECSXP:
	if (length <= 0)
	    size = 0;
	else {
	    if (length > R_SIZE_T_MAX / sizeof(SEXP))
		error(_("cannot allocate vector of length %d"), length);
	    size = PTR2VEC(length);
#if VALGRIND_LEVEL > 0
	    actual_size = length * sizeof(SEXP);
#endif
	}
	break;
    case LANGSXP:
	if(length == 0) return R_NilValue;
#ifdef LONG_VECTOR_SUPPORT
	if (length > R_SHORT_LEN_MAX) error("invalid length for pairlist");
#endif
	s = allocList((int) length);
	SET_TYPEOF(s, LANGSXP);
	return s;
    case LISTSXP:
#ifdef LONG_VECTOR_SUPPORT
	if (length > R_SHORT_LEN_MAX) error("invalid length for pairlist");
#endif
	return allocList((int) length);
    default:
	error(_("invalid type/length (%s/%d) in vector allocation"),
	      type2char(type), length);
    }

    if (allocator) {
	node_class = CUSTOM_NODE_CLASS;
	alloc_size = size;
    } else {
	if (size <= NodeClassSize[1]) {
	    node_class = 1;
	    alloc_size = NodeClassSize[1];
	}
	else {
	    node_class = LARGE_NODE_CLASS;
	    alloc_size = size;
	    for (int i = 2; i < NUM_SMALL_NODE_CLASSES; i++) {
		if (size <= NodeClassSize[i]) {
		    node_class = i;
		    alloc_size = NodeClassSize[i];
		    break;
		}
	    }
	}
    }

    /* save current R_VSize to roll back adjustment if malloc fails */
    old_R_VSize = R_VSize;

    /* we need to do the gc here so allocSExp doesn't! */
    if (FORCE_GC || NO_FREE_NODES() || VHEAP_FREE() < alloc_size) {
	R_gc_internal(alloc_size);
	if (NO_FREE_NODES())
	    mem_err_cons();
	if (VHEAP_FREE() < alloc_size)
	    mem_err_heap(size);
    }

    if (size > 0) {
	if (node_class < NUM_SMALL_NODE_CLASSES) {
	    CLASS_GET_FREE_NODE(node_class, s);
#if VALGRIND_LEVEL > 1
	    VALGRIND_MAKE_MEM_UNDEFINED(DATAPTR(s), actual_size);
#endif
	    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
	    INIT_REFCNT(s);
	    SET_NODE_CLASS(s, node_class);
	    R_SmallVallocSize += alloc_size;
	    SET_SHORT_VEC_LENGTH(s, (R_len_t) length);
	}
	else {
	    Rboolean success = FALSE;
	    R_size_t hdrsize = sizeof(SEXPREC_ALIGN);
#ifdef LONG_VECTOR_SUPPORT
	    if (length > R_SHORT_LEN_MAX)
		hdrsize = sizeof(SEXPREC_ALIGN) + sizeof(R_long_vec_hdr_t);
#endif
	    void *mem = NULL; /* initialize to suppress warning */
	    if (size < (R_SIZE_T_MAX / sizeof(VECREC)) - hdrsize) { /*** not sure this test is quite right -- why subtract the header? LT */
		mem = allocator ?
		    custom_node_alloc(allocator, hdrsize + size * sizeof(VECREC)) :
		    malloc(hdrsize + size * sizeof(VECREC));
		if (mem == NULL) {
		    /* If we are near the address space limit, we
		       might be short of address space.  So return
		       all unused objects to malloc and try again. */
		    R_gc_full(alloc_size);
		    mem = allocator ?
			custom_node_alloc(allocator, hdrsize + size * sizeof(VECREC)) :
			malloc(hdrsize + size * sizeof(VECREC));
		}
		if (mem != NULL) {
#ifdef LONG_VECTOR_SUPPORT
		    if (length > R_SHORT_LEN_MAX) {
			s = (SEXP) (((char *) mem) + sizeof(R_long_vec_hdr_t));
			SET_SHORT_VEC_LENGTH(s, R_LONG_VEC_TOKEN);
			SET_LONG_VEC_LENGTH(s, length);
			SET_LONG_VEC_TRUELENGTH(s, 0);
		    }
		    else {
			s = mem;
			SET_SHORT_VEC_LENGTH(s, (R_len_t) length);
		    }
#else
		    s = mem;
		    SETLENGTH(s, length);
#endif
		    success = TRUE;
		}
		else s = NULL;
#ifdef R_MEMORY_PROFILING
		R_ReportAllocation(hdrsize + size * sizeof(VECREC));
#endif
	    } else s = NULL; /* suppress warning */
	    if (! success) {
		double dsize = (double)size * sizeof(VECREC)/1024.0;
		/* reset the vector heap limit */
		R_VSize = old_R_VSize;
		if(dsize > 1024.0*1024.0)
		    errorcall(R_NilValue,
			      _("cannot allocate vector of size %0.1f Gb"),
			      dsize/1024.0/1024.0);
		if(dsize > 1024.0)
		    errorcall(R_NilValue,
			      _("cannot allocate vector of size %0.1f Mb"),
			      dsize/1024.0);
		else
		    errorcall(R_NilValue,
			      _("cannot allocate vector of size %0.f Kb"),
			      dsize);
	    }
	    s->sxpinfo = UnmarkedNodeTemplate.sxpinfo;
	    INIT_REFCNT(s);
	    SET_NODE_CLASS(s, node_class);
	    if (!allocator) R_LargeVallocSize += size;
	    R_GenHeap[node_class].AllocCount++;
	    R_NodesInUse++;
	    SNAP_NODE(s, R_GenHeap[node_class].New);
	}
	ATTRIB(s) = R_NilValue;
	SET_TYPEOF(s, type);
    }
    else {
	GC_PROT(s = allocSExpNonCons(type));
	SET_SHORT_VEC_LENGTH(s, (R_len_t) length);
    }
    SET_SHORT_VEC_TRUELENGTH(s, 0);
    SET_NAMED(s, 0);
    INIT_REFCNT(s);

    /* The following prevents disaster in the case */
    /* that an uninitialised string vector is marked */
    /* Direct assignment is OK since the node was just allocated and */
    /* so is at least as new as R_NilValue and R_BlankString */
    if (type == EXPRSXP || type == VECSXP) {
	SEXP *data = STRING_PTR(s);
#if VALGRIND_LEVEL > 1
	VALGRIND_MAKE_MEM_DEFINED(STRING_PTR(s), actual_size);
#endif
	for (R_xlen_t i = 0; i < length; i++)
	    data[i] = R_NilValue;
    }
    else if(type == STRSXP) {
	SEXP *data = STRING_PTR(s);
#if VALGRIND_LEVEL > 1
	VALGRIND_MAKE_MEM_DEFINED(STRING_PTR(s), actual_size);
#endif
	for (R_xlen_t i = 0; i < length; i++)
	    data[i] = R_BlankString;
    }
    else if (type == CHARSXP || type == intCHARSXP) {
#if VALGRIND_LEVEL > 0
	VALGRIND_MAKE_MEM_UNDEFINED(CHAR(s), actual_size);
#endif
	CHAR_RW(s)[length] = 0;
    }
#if VALGRIND_LEVEL > 0
    else if (type == REALSXP)
	VALGRIND_MAKE_MEM_UNDEFINED(REAL(s), actual_size);
    else if (type == INTSXP)
	VALGRIND_MAKE_MEM_UNDEFINED(INTEGER(s), actual_size);
    else if (type == LGLSXP)
	VALGRIND_MAKE_MEM_UNDEFINED(LOGICAL(s), actual_size);
    else if (type == CPLXSXP)
	VALGRIND_MAKE_MEM_UNDEFINED(COMPLEX(s), actual_size);
    else if (type == RAWSXP)
	VALGRIND_MAKE_MEM_UNDEFINED(RAW(s), actual_size);
#endif
    return s;
}

/* For future hiding of allocVector(CHARSXP) */
SEXP attribute_hidden allocCharsxp(R_len_t len)
{
    return allocVector(intCHARSXP, len);
}

SEXP allocList(int n)
{
    int i;
    SEXP result;
    result = R_NilValue;
    for (i = 0; i < n; i++)
	result = CONS(R_NilValue, result);
    return result;
}

SEXP allocS4Object(void)
{
   SEXP s;
   GC_PROT(s = allocSExpNonCons(S4SXP));
   SET_S4_OBJECT(s);
   return s;
}

static SEXP allocFormalsList(int nargs, ...)
{
    SEXP res = R_NilValue;
    SEXP n;
    int i;
    va_list(syms);
    va_start(syms, nargs);

    for(i = 0; i < nargs; i++) {
	res = CONS(R_NilValue, res);
    }
    R_PreserveObject(res);

    n = res;
    for(i = 0; i < nargs; i++) {
	SET_TAG(n, (SEXP) va_arg(syms, SEXP));
	MARK_NOT_MUTABLE(n);
	n = CDR(n);
    }
    va_end(syms);

    return res;
}


SEXP allocFormalsList2(SEXP sym1, SEXP sym2)
{
    return allocFormalsList(2, sym1, sym2);
}

SEXP allocFormalsList3(SEXP sym1, SEXP sym2, SEXP sym3)
{
    return allocFormalsList(3, sym1, sym2, sym3);
}

SEXP allocFormalsList4(SEXP sym1, SEXP sym2, SEXP sym3, SEXP sym4)
{
    return allocFormalsList(4, sym1, sym2, sym3, sym4);
}

SEXP allocFormalsList5(SEXP sym1, SEXP sym2, SEXP sym3, SEXP sym4, SEXP sym5)
{
    return allocFormalsList(5, sym1, sym2, sym3, sym4, sym5);
}

SEXP allocFormalsList6(SEXP sym1, SEXP sym2, SEXP sym3, SEXP sym4,
		       SEXP sym5, SEXP sym6)
{
    return allocFormalsList(6, sym1, sym2, sym3, sym4, sym5, sym6);
}

/* "gc" a mark-sweep or in-place generational garbage collector */

void R_gc(void)
{
    R_gc_internal(0);
#ifndef IMMEDIATE_FINALIZERS
    R_RunPendingFinalizers();
#endif
}

static void R_gc_full(R_size_t size_needed)
{
    num_old_gens_to_collect = NUM_OLD_GENERATIONS;
    R_gc_internal(size_needed);
}

static double gctimes[5], gcstarttimes[5];
static Rboolean gctime_enabled = FALSE;

/* this is primitive */
SEXP attribute_hidden do_gctime(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans;

    if (args == R_NilValue)
	gctime_enabled = TRUE;
    else {
	check1arg(args, call, "on");
	gctime_enabled = asLogical(CAR(args));
    }
    ans = allocVector(REALSXP, 5);
    REAL(ans)[0] = gctimes[0];
    REAL(ans)[1] = gctimes[1];
    REAL(ans)[2] = gctimes[2];
    REAL(ans)[3] = gctimes[3];
    REAL(ans)[4] = gctimes[4];
    return ans;
}

static void gc_start_timing(void)
{
    if (gctime_enabled)
	R_getProcTime(gcstarttimes);
}

static void gc_end_timing(void)
{
    if (gctime_enabled) {
	double times[5], delta;
	R_getProcTime(times);

	/* add delta to compensate for timer resolution */
#if 0
	/* this seems to over-compensate too */
	delta = R_getClockIncrement();
#else
	delta = 0;
#endif

	gctimes[0] += times[0] - gcstarttimes[0] + delta;
	gctimes[1] += times[1] - gcstarttimes[1] + delta;
	gctimes[2] += times[2] - gcstarttimes[2];
	gctimes[3] += times[3] - gcstarttimes[3];
	gctimes[4] += times[4] - gcstarttimes[4];
    }
}

#define R_MAX(a,b) (a) < (b) ? (b) : (a)

static void R_gc_internal(R_size_t size_needed)
{
    if (!R_GCEnabled) {
      if (NO_FREE_NODES())
	R_NSize = R_NodesInUse + 1;
      if (size_needed > VHEAP_FREE())
	R_VSize += size_needed - VHEAP_FREE();
      gc_pending = TRUE;
      return;
    }
    gc_pending = FALSE;

    R_size_t onsize = R_NSize /* can change during collection */;
    double ncells, vcells, vfrac, nfrac;
    SEXPTYPE first_bad_sexp_type = 0;
#ifdef PROTECTCHECK
    SEXPTYPE first_bad_sexp_type_old_type = 0;
#endif
    SEXP first_bad_sexp_type_sexp = NULL;
    int first_bad_sexp_type_line = 0;

#ifdef IMMEDIATE_FINALIZERS
    Rboolean first = TRUE;
 again:
#endif

    gc_count++;

    R_N_maxused = R_MAX(R_N_maxused, R_NodesInUse);
    R_V_maxused = R_MAX(R_V_maxused, R_VSize - VHEAP_FREE());

    BEGIN_SUSPEND_INTERRUPTS {
	R_in_gc = TRUE;
	gc_start_timing();
	RunGenCollect(size_needed);
	gc_end_timing();
	R_in_gc = FALSE;
    } END_SUSPEND_INTERRUPTS;

    if (bad_sexp_type_seen != 0 && first_bad_sexp_type == 0) {
	first_bad_sexp_type = bad_sexp_type_seen;
#ifdef PROTECTCHECK
	first_bad_sexp_type_old_type = bad_sexp_type_old_type;
#endif
	first_bad_sexp_type_sexp = bad_sexp_type_sexp;
	first_bad_sexp_type_line = bad_sexp_type_line;
    }

    if (gc_reporting) {
	ncells = onsize - R_Collected;
	nfrac = (100.0 * ncells) / R_NSize;
	/* We try to make this consistent with the results returned by gc */
	ncells = 0.1*ceil(10*ncells * sizeof(SEXPREC)/Mega);
	REprintf("\n%.1f Mbytes of cons cells used (%d%%)\n",
		 ncells, (int) (nfrac + 0.5));
	vcells = R_VSize - VHEAP_FREE();
	vfrac = (100.0 * vcells) / R_VSize;
	vcells = 0.1*ceil(10*vcells * vsfac/Mega);
	REprintf("%.1f Mbytes of vectors used (%d%%)\n",
		 vcells, (int) (vfrac + 0.5));
    }

#ifdef IMMEDIATE_FINALIZERS
    if (first) {
	first = FALSE;
	/* Run any eligible finalizers.  The return result of
	   RunFinalizers is TRUE if any finalizers are actually run.
	   There is a small chance that running finalizers here may
	   chew up enough memory to make another immediate collection
	   necessary.  If so, we jump back to the beginning and run
	   the collection, but on this second pass we do not run
	   finalizers. */
	if (RunFinalizers() &&
	    (NO_FREE_NODES() || size_needed > VHEAP_FREE()))
	    goto again;
    }
#endif

    if (first_bad_sexp_type != 0) {
#ifdef PROTECTCHECK
	if (first_bad_sexp_type == FREESXP)
	    error("GC encountered a node (%p) with type FREESXP (was %s)"
		  " at memory.c:%d",
		  first_bad_sexp_type_sexp,
		  sexptype2char(first_bad_sexp_type_old_type),
		  first_bad_sexp_type_line);
	else
	    error("GC encountered a node (%p) with an unknown SEXP type: %s"
		  " at memory.c:%d",
		  first_bad_sexp_type_sexp,
		  sexptype2char(first_bad_sexp_type),
		  first_bad_sexp_type_line);
#else
	error("GC encountered a node (%p) with an unknown SEXP type: %s"
	      " at memory.c:%d",
	      first_bad_sexp_type_sexp,
	      sexptype2char(first_bad_sexp_type),
	      first_bad_sexp_type_line);
#endif
    }

    /* sanity check on logical scalar values */
    if (R_TrueValue != NULL && LOGICAL(R_TrueValue)[0] != TRUE) {
	LOGICAL(R_TrueValue)[0] = TRUE;
	error("internal TRUE value has been modified");
    }
    if (R_FalseValue != NULL && LOGICAL(R_FalseValue)[0] != FALSE) {
	LOGICAL(R_FalseValue)[0] = FALSE;
	error("internal FALSE value has been modified");
    }
    if (R_LogicalNAValue != NULL &&
	LOGICAL(R_LogicalNAValue)[0] != NA_LOGICAL) {
	LOGICAL(R_LogicalNAValue)[0] = NA_LOGICAL;
	error("internal logical NA value has been modified");
    }
    /* compiler constants are checked in RunGenCollect */
}


SEXP attribute_hidden do_memoryprofile(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, nms;
    int i, tmp;

    checkArity(op, args);
    PROTECT(ans = allocVector(INTSXP, 24));
    PROTECT(nms = allocVector(STRSXP, 24));
    for (i = 0; i < 24; i++) {
	INTEGER(ans)[i] = 0;
	SET_STRING_ELT(nms, i, type2str(i > LGLSXP? i+2 : i));
    }
    setAttrib(ans, R_NamesSymbol, nms);

    BEGIN_SUSPEND_INTERRUPTS {
      int gen;

      /* run a full GC to make sure that all stuff in use is in Old space */
      num_old_gens_to_collect = NUM_OLD_GENERATIONS;
      R_gc();
      for (gen = 0; gen < NUM_OLD_GENERATIONS; gen++) {
	for (i = 0; i < NUM_NODE_CLASSES; i++) {
	  SEXP s;
	  for (s = NEXT_NODE(R_GenHeap[i].Old[gen]);
	       s != R_GenHeap[i].Old[gen];
	       s = NEXT_NODE(s)) {
	      tmp = TYPEOF(s);
	      if(tmp > LGLSXP) tmp -= 2;
	      INTEGER(ans)[tmp]++;
	  }
	}
      }
    } END_SUSPEND_INTERRUPTS;
    UNPROTECT(2);
    return ans;
}

/* "protect" push a single argument onto R_PPStack */

/* In handling a stack overflow we have to be careful not to use
   PROTECT. error("protect(): stack overflow") would call deparse1,
   which uses PROTECT and segfaults.*/

/* However, the traceback creation in the normal error handler also
   does a PROTECT, as does the jumping code, at least if there are
   cleanup expressions to handle on the way out.  So for the moment
   we'll allocate a slightly larger PP stack and only enable the added
   red zone during handling of a stack overflow error.  LT */

static void reset_pp_stack(void *data)
{
    int *poldpps = data;
    R_PPStackSize =  *poldpps;
}

void NORET R_signal_protect_error(void)
{
    RCNTXT cntxt;
    int oldpps = R_PPStackSize;

    begincontext(&cntxt, CTXT_CCODE, R_NilValue, R_BaseEnv, R_BaseEnv,
		 R_NilValue, R_NilValue);
    cntxt.cend = &reset_pp_stack;
    cntxt.cenddata = &oldpps;

    if (R_PPStackSize < R_RealPPStackSize)
	R_PPStackSize = R_RealPPStackSize;
    errorcall(R_NilValue, _("protect(): protection stack overflow"));

    endcontext(&cntxt); /* not reached */
}

void NORET R_signal_unprotect_error(void)
{
    error(ngettext("unprotect(): only %d protected item",
		   "unprotect(): only %d protected items", R_PPStackTop),
	  R_PPStackTop);
}

#ifndef INLINE_PROTECT
SEXP protect(SEXP s)
{
    if (R_PPStackTop >= R_PPStackSize)
	R_signal_protect_error();
    R_PPStack[R_PPStackTop++] = CHK(s);
    return s;
}


/* "unprotect" pop argument list from top of R_PPStack */

void unprotect(int l)
{
    if (R_PPStackTop >=  l)
	R_PPStackTop -= l;
    else R_signal_unprotect_error();
}
#endif

/* "unprotect_ptr" remove pointer from somewhere in R_PPStack */

void unprotect_ptr(SEXP s)
{
    int i = R_PPStackTop;

    /* go look for  s  in  R_PPStack */
    /* (should be among the top few items) */
    do {
	if (i == 0)
	    error(_("unprotect_ptr: pointer not found"));
    } while ( R_PPStack[--i] != s );

    /* OK, got it, and  i  is indexing its location */
    /* Now drop stack above it, if any */

    while (++i < R_PPStackTop) R_PPStack[i - 1] = R_PPStack[i];

    R_PPStackTop--;
}

/* Debugging function:  is s protected? */

int Rf_isProtected(SEXP s)
{
    int i = R_PPStackTop;

    /* go look for  s  in  R_PPStack */
    do {
	if (i == 0)
	    return(i);
    } while ( R_PPStack[--i] != s );

    /* OK, got it, and  i  is indexing its location */
    return(i);
}


#ifndef INLINE_PROTECT
void R_ProtectWithIndex(SEXP s, PROTECT_INDEX *pi)
{
    protect(s);
    *pi = R_PPStackTop - 1;
}
#endif

void NORET R_signal_reprotect_error(PROTECT_INDEX i)
{
    error(ngettext("R_Reprotect: only %d protected item, can't reprotect index %d",
		   "R_Reprotect: only %d protected items, can't reprotect index %d",
		   R_PPStackTop),
	  R_PPStackTop, i);
}

#ifndef INLINE_PROTECT
void R_Reprotect(SEXP s, PROTECT_INDEX i)
{
    if (i >= R_PPStackTop || i < 0)
	R_signal_reprotect_error(i);
    R_PPStack[i] = s;
}
#endif

#ifdef UNUSED
/* remove all objects from the protection stack from index i upwards
   and return them in a vector. The order in the vector is from new
   to old. */
SEXP R_CollectFromIndex(PROTECT_INDEX i)
{
    SEXP res;
    int top = R_PPStackTop, j = 0;
    if (i > top) i = top;
    res = protect(allocVector(VECSXP, top - i));
    while (i < top)
	SET_VECTOR_ELT(res, j++, R_PPStack[--top]);
    R_PPStackTop = top; /* this includes the protect we used above */
    return res;
}
#endif

/* "initStack" initialize environment stack */
attribute_hidden
void initStack(void)
{
    R_PPStackTop = 0;
}


/* S-like wrappers for calloc, realloc and free that check for error
   conditions */

void *R_chk_calloc(size_t nelem, size_t elsize)
{
    void *p;
#ifndef HAVE_WORKING_CALLOC
    if(nelem == 0)
	return(NULL);
#endif
    p = calloc(nelem, elsize);
    if(!p) /* problem here is that we don't have a format for size_t. */
	error(_("'Calloc' could not allocate memory (%.0f of %u bytes)"),
	      (double) nelem, elsize);
    return(p);
}

void *R_chk_realloc(void *ptr, size_t size)
{
    void *p;
    /* Protect against broken realloc */
    if(ptr) p = realloc(ptr, size); else p = malloc(size);
    if(!p)
	error(_("'Realloc' could not re-allocate memory (%.0f bytes)"),
	      (double) size);
    return(p);
}

void R_chk_free(void *ptr)
{
    /* S-PLUS warns here, but there seems no reason to do so */
    /* if(!ptr) warning("attempt to free NULL pointer by Free"); */
    if(ptr) free(ptr); /* ANSI C says free has no effect on NULL, but
			  better to be safe here */
}

/* This code keeps a list of objects which are not assigned to variables
   but which are required to persist across garbage collections.  The
   objects are registered with R_PreserveObject and deregistered with
   R_ReleaseObject. */

void R_PreserveObject(SEXP object)
{
    R_PreciousList = CONS(object, R_PreciousList);
}

static SEXP RecursiveRelease(SEXP object, SEXP list)
{
    if (!isNull(list)) {
	if (object == CAR(list))
	    return CDR(list);
	else
	    CDR(list) = RecursiveRelease(object, CDR(list));
    }
    return list;
}

void R_ReleaseObject(SEXP object)
{
    R_PreciousList =  RecursiveRelease(object, R_PreciousList);
}


/* External Pointer Objects */
SEXP R_MakeExternalPtr(void *p, SEXP tag, SEXP prot)
{
    SEXP s = allocSExp(EXTPTRSXP);
    EXTPTR_PTR(s) = p;
    EXTPTR_PROT(s) = CHK(prot);
    EXTPTR_TAG(s) = CHK(tag);
    return s;
}

void *R_ExternalPtrAddr(SEXP s)
{
    return EXTPTR_PTR(CHK(s));
}

SEXP R_ExternalPtrTag(SEXP s)
{
    return CHK(EXTPTR_TAG(CHK(s)));
}

SEXP R_ExternalPtrProtected(SEXP s)
{
    return CHK(EXTPTR_PROT(CHK(s)));
}

void R_ClearExternalPtr(SEXP s)
{
    EXTPTR_PTR(s) = NULL;
}

void R_SetExternalPtrAddr(SEXP s, void *p)
{
    EXTPTR_PTR(s) = p;
}

void R_SetExternalPtrTag(SEXP s, SEXP tag)
{
    FIX_REFCNT(s, EXTPTR_TAG(s), tag);
    CHECK_OLD_TO_NEW(s, tag);
    EXTPTR_TAG(s) = tag;
}

void R_SetExternalPtrProtected(SEXP s, SEXP p)
{
    FIX_REFCNT(s, EXTPTR_PROT(s), p);
    CHECK_OLD_TO_NEW(s, p);
    EXTPTR_PROT(s) = p;
}

/* 
   Added to API in R 3.4.0.
   Work around casting issues: works where it is needed.
 */
typedef union {void *p; DL_FUNC fn;} fn_ptr;

SEXP R_MakeExternalPtrFn(DL_FUNC p, SEXP tag, SEXP prot)
{
    fn_ptr tmp;
    SEXP s = allocSExp(EXTPTRSXP);
    tmp.fn = p;
    EXTPTR_PTR(s) = tmp.p;
    EXTPTR_PROT(s) = CHK(prot);
    EXTPTR_TAG(s) = CHK(tag);
    return s;
}

DL_FUNC R_ExternalPtrAddrFn(SEXP s)
{
    fn_ptr tmp;
    tmp.p =  EXTPTR_PTR(CHK(s));
    return tmp.fn;
}



/* The following functions are replacements for the accessor macros.
   They are used by code that does not have direct access to the
   internal representation of objects.  The replacement functions
   implement the write barrier. */

/* General Cons Cell Attributes */
SEXP (ATTRIB)(SEXP x) { return CHK(ATTRIB(CHK(x))); }
int (OBJECT)(SEXP x) { return OBJECT(CHK(x)); }
int (MARK)(SEXP x) { return MARK(CHK(x)); }
int (TYPEOF)(SEXP x) { return TYPEOF(CHK(x)); }
int (NAMED)(SEXP x) { return NAMED(CHK(x)); }
int (RTRACE)(SEXP x) { return RTRACE(CHK(x)); }
int (LEVELS)(SEXP x) { return LEVELS(CHK(x)); }
int (REFCNT)(SEXP x) { return REFCNT(x); }

void (SET_ATTRIB)(SEXP x, SEXP v) {
    if(TYPEOF(v) != LISTSXP && TYPEOF(v) != NILSXP)
	error("value of 'SET_ATTRIB' must be a pairlist or NULL, not a '%s'",
	      type2char(TYPEOF(x)));
    FIX_REFCNT(x, ATTRIB(x), v);
    CHECK_OLD_TO_NEW(x, v);
    ATTRIB(x) = v;
}
void (SET_OBJECT)(SEXP x, int v) { SET_OBJECT(CHK(x), v); }
void (SET_TYPEOF)(SEXP x, int v) { SET_TYPEOF(CHK(x), v); }
void (SET_NAMED)(SEXP x, int v) { SET_NAMED(CHK(x), v); }
void (SET_RTRACE)(SEXP x, int v) { SET_RTRACE(CHK(x), v); }
int (SETLEVELS)(SEXP x, int v) { return SETLEVELS(CHK(x), v); }
void DUPLICATE_ATTRIB(SEXP to, SEXP from) {
    SET_ATTRIB(CHK(to), duplicate(CHK(ATTRIB(CHK(from)))));
    SET_OBJECT(CHK(to), OBJECT(from));
    IS_S4_OBJECT(from) ?  SET_S4_OBJECT(to) : UNSET_S4_OBJECT(to);
}
void SHALLOW_DUPLICATE_ATTRIB(SEXP to, SEXP from) {
    SET_ATTRIB(CHK(to), shallow_duplicate(CHK(ATTRIB(CHK(from)))));
    SET_OBJECT(CHK(to), OBJECT(from));
    IS_S4_OBJECT(from) ?  SET_S4_OBJECT(to) : UNSET_S4_OBJECT(to);
}

/* S4 object testing */
int (IS_S4_OBJECT)(SEXP x){ return IS_S4_OBJECT(CHK(x)); }
void (SET_S4_OBJECT)(SEXP x){ SET_S4_OBJECT(CHK(x)); }
void (UNSET_S4_OBJECT)(SEXP x){ UNSET_S4_OBJECT(CHK(x)); }

/* JIT optimization support */
int (NOJIT)(SEXP x) { return NOJIT(CHK(x)); }
int (MAYBEJIT)(SEXP x) { return MAYBEJIT(CHK(x)); }
void (SET_NOJIT)(SEXP x) { SET_NOJIT(CHK(x)); }
void (SET_MAYBEJIT)(SEXP x) { SET_MAYBEJIT(CHK(x)); }
void (UNSET_MAYBEJIT)(SEXP x) { UNSET_MAYBEJIT(CHK(x)); }

/* Growable vector support */
int (IS_GROWABLE)(SEXP x) { return IS_GROWABLE(CHK(x)); }
void (SET_GROWABLE_BIT)(SEXP x) { SET_GROWABLE_BIT(CHK(x)); }

static int nvec[32] = {
    0,1,1,1,1,1,1,1,  // does NILSXP really count?
    1,0,0,1,1,0,0,0,
    0,1,1,0,0,1,1,0,
    0,1,1,1,1,1,1,1
};

static R_INLINE SEXP CHK2(SEXP x)
{
    x = CHK(x);
    if(nvec[TYPEOF(x)])
	error("LENGTH or similar applied to %s object", type2char(TYPEOF(x)));
    return x;
}

/* Vector Accessors */
int (LENGTH)(SEXP x) { return LENGTH(CHK2(x)); }
int (TRUELENGTH)(SEXP x) { return TRUELENGTH(CHK2(x)); }
void (SETLENGTH)(SEXP x, int v) { SETLENGTH(CHK2(x), v); }
void (SET_TRUELENGTH)(SEXP x, int v) { SET_TRUELENGTH(CHK2(x), v); }
R_xlen_t (XLENGTH)(SEXP x) { return XLENGTH(CHK2(x)); }
R_xlen_t (XTRUELENGTH)(SEXP x) { return XTRUELENGTH(CHK2(x)); }
int  (IS_LONG_VEC)(SEXP x) { return IS_LONG_VEC(CHK2(x)); }

const char *(R_CHAR)(SEXP x) {
    if(TYPEOF(x) != CHARSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "CHAR", "CHARSXP", type2char(TYPEOF(x)));
    return (const char *)CHAR(x);
}

SEXP (STRING_ELT)(SEXP x, R_xlen_t i) {
    if(TYPEOF(x) != STRSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "STRING_ELT", "character vector", type2char(TYPEOF(x)));
    return CHK(STRING_ELT(x, i));
}

SEXP (VECTOR_ELT)(SEXP x, R_xlen_t i) {
    /* We need to allow vector-like types here */
    if(TYPEOF(x) != VECSXP &&
       TYPEOF(x) != EXPRSXP &&
       TYPEOF(x) != WEAKREFSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "VECTOR_ELT", "list", type2char(TYPEOF(x)));
    return CHK(VECTOR_ELT(x, i));
}

int *(LOGICAL)(SEXP x) {
    if(TYPEOF(x) != LGLSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "LOGICAL",  "logical", type2char(TYPEOF(x)));
  return LOGICAL(x);
}

/* Maybe this should exclude logicals, but it is widely used */
int *(INTEGER)(SEXP x) {
    if(TYPEOF(x) != INTSXP && TYPEOF(x) != LGLSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "INTEGER", "integer", type2char(TYPEOF(x)));
    return INTEGER(x);
}

Rbyte *(RAW)(SEXP x) {
    if(TYPEOF(x) != RAWSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "RAW", "raw", type2char(TYPEOF(x)));
    return RAW(x);
}

double *(REAL)(SEXP x) {
    if(TYPEOF(x) != REALSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "REAL", "numeric", type2char(TYPEOF(x)));
    return REAL(x);
}

Rcomplex *(COMPLEX)(SEXP x) {
    if(TYPEOF(x) != CPLXSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "COMPLEX", "complex", type2char(TYPEOF(x)));
    return COMPLEX(x);
}

SEXP *(STRING_PTR)(SEXP x) { return STRING_PTR(CHK(x)); }

SEXP * NORET (VECTOR_PTR)(SEXP x)
{
  error(_("not safe to return vector pointer"));
}

void (SET_STRING_ELT)(SEXP x, R_xlen_t i, SEXP v) {
    if(TYPEOF(x) != STRSXP)
	error("%s() can only be applied to a '%s', not a '%s'",
	      "SET_STRING_ELT", "character vector", type2char(TYPEOF(x)));
    if(TYPEOF(v) != CHARSXP)
       error("Value of SET_STRING_ELT() must be a 'CHARSXP' not a '%s'",
	     type2char(TYPEOF(v)));
    if (i < 0 || i >= XLENGTH(x))
	error(_("attempt to set index %lu/%lu in SET_STRING_ELT"),
	      i, XLENGTH(x));
    FIX_REFCNT(x, STRING_ELT(x, i), v);
    CHECK_OLD_TO_NEW(x, v);
    STRING_ELT(x, i) = v;
}

SEXP (SET_VECTOR_ELT)(SEXP x, R_xlen_t i, SEXP v) {
    /*  we need to allow vector-like types here */
    if(TYPEOF(x) != VECSXP &&
       TYPEOF(x) != EXPRSXP &&
       TYPEOF(x) != WEAKREFSXP) {
	error("%s() can only be applied to a '%s', not a '%s'",
	      "SET_VECTOR_ELT", "list", type2char(TYPEOF(x)));
    }
    if (i < 0 || i >= XLENGTH(x))
	error(_("attempt to set index %lu/%lu in SET_VECTOR_ELT"),
	      i, XLENGTH(x));
    FIX_REFCNT(x, VECTOR_ELT(x, i), v);
    CHECK_OLD_TO_NEW(x, v);
    return VECTOR_ELT(x, i) = v;
}


/* List Accessors */
SEXP (TAG)(SEXP e) { return CHK(TAG(CHK(e))); }
SEXP (CAR)(SEXP e) { return CHK(CAR(CHK(e))); }
SEXP (CDR)(SEXP e) { return CHK(CDR(CHK(e))); }
SEXP (CAAR)(SEXP e) { return CHK(CAAR(CHK(e))); }
SEXP (CDAR)(SEXP e) { return CHK(CDAR(CHK(e))); }
SEXP (CADR)(SEXP e) { return CHK(CADR(CHK(e))); }
SEXP (CDDR)(SEXP e) { return CHK(CDDR(CHK(e))); }
SEXP (CDDDR)(SEXP e) { return CHK(CDDDR(CHK(e))); }
SEXP (CADDR)(SEXP e) { return CHK(CADDR(CHK(e))); }
SEXP (CADDDR)(SEXP e) { return CHK(CADDDR(CHK(e))); }
SEXP (CAD4R)(SEXP e) { return CHK(CAD4R(CHK(e))); }
int (MISSING)(SEXP x) { return MISSING(CHK(x)); }

void (SET_TAG)(SEXP x, SEXP v) { FIX_REFCNT(x, TAG(x), v); CHECK_OLD_TO_NEW(x, v); TAG(x) = v; }

SEXP (SETCAR)(SEXP x, SEXP y)
{
    if (x == NULL || x == R_NilValue)
	error(_("bad value"));
    FIX_REFCNT(x, CAR(x), y);
    CHECK_OLD_TO_NEW(x, y);
    CAR(x) = y;
    return y;
}

SEXP (SETCDR)(SEXP x, SEXP y)
{
    if (x == NULL || x == R_NilValue)
	error(_("bad value"));
    FIX_REFCNT(x, CDR(x), y);
    CHECK_OLD_TO_NEW(x, y);
    CDR(x) = y;
    return y;
}

SEXP (SETCADR)(SEXP x, SEXP y)
{
    SEXP cell;
    if (x == NULL || x == R_NilValue ||
	CDR(x) == NULL || CDR(x) == R_NilValue)
	error(_("bad value"));
    cell = CDR(x);
    FIX_REFCNT(cell, CAR(cell), y);
    CHECK_OLD_TO_NEW(cell, y);
    CAR(cell) = y;
    return y;
}

SEXP (SETCADDR)(SEXP x, SEXP y)
{
    SEXP cell;
    if (x == NULL || x == R_NilValue ||
	CDR(x) == NULL || CDR(x) == R_NilValue ||
	CDDR(x) == NULL || CDDR(x) == R_NilValue)
	error(_("bad value"));
    cell = CDDR(x);
    FIX_REFCNT(cell, CAR(cell), y);
    CHECK_OLD_TO_NEW(cell, y);
    CAR(cell) = y;
    return y;
}

SEXP (SETCADDDR)(SEXP x, SEXP y)
{
    SEXP cell;
    if (CHK(x) == NULL || x == R_NilValue ||
	CHK(CDR(x)) == NULL || CDR(x) == R_NilValue ||
	CHK(CDDR(x)) == NULL || CDDR(x) == R_NilValue ||
	CHK(CDDDR(x)) == NULL || CDDDR(x) == R_NilValue)
	error(_("bad value"));
    cell = CDDDR(x);
    FIX_REFCNT(cell, CAR(cell), y);
    CHECK_OLD_TO_NEW(cell, y);
    CAR(cell) = y;
    return y;
}

#define CD4R(x) CDR(CDR(CDR(CDR(x))))

SEXP (SETCAD4R)(SEXP x, SEXP y)
{
    SEXP cell;
    if (CHK(x) == NULL || x == R_NilValue ||
	CHK(CDR(x)) == NULL || CDR(x) == R_NilValue ||
	CHK(CDDR(x)) == NULL || CDDR(x) == R_NilValue ||
	CHK(CDDDR(x)) == NULL || CDDDR(x) == R_NilValue ||
	CHK(CD4R(x)) == NULL || CD4R(x) == R_NilValue)
	error(_("bad value"));
    cell = CD4R(x);
    FIX_REFCNT(cell, CAR(cell), y);
    CHECK_OLD_TO_NEW(cell, y);
    CAR(cell) = y;
    return y;
}

void (SET_MISSING)(SEXP x, int v) { SET_MISSING(CHK(x), v); }

/* Closure Accessors */
SEXP (FORMALS)(SEXP x) { return CHK(FORMALS(CHK(x))); }
SEXP (BODY)(SEXP x) { return CHK(BODY(CHK(x))); }
SEXP (CLOENV)(SEXP x) { return CHK(CLOENV(CHK(x))); }
int (RDEBUG)(SEXP x) { return RDEBUG(CHK(x)); }
int (RSTEP)(SEXP x) { return RSTEP(CHK(x)); }

void (SET_FORMALS)(SEXP x, SEXP v) { FIX_REFCNT(x, FORMALS(x), v); CHECK_OLD_TO_NEW(x, v); FORMALS(x) = v; }
void (SET_BODY)(SEXP x, SEXP v) { FIX_REFCNT(x, BODY(x), v); CHECK_OLD_TO_NEW(x, v); BODY(x) = v; }
void (SET_CLOENV)(SEXP x, SEXP v) { FIX_REFCNT(x, CLOENV(x), v); CHECK_OLD_TO_NEW(x, v); CLOENV(x) = v; }
void (SET_RDEBUG)(SEXP x, int v) { SET_RDEBUG(CHK(x), v); }
void (SET_RSTEP)(SEXP x, int v) { SET_RSTEP(CHK(x), v); }

/* These are only needed with the write barrier on */
#ifdef TESTING_WRITE_BARRIER
/* Primitive Accessors */
/* not hidden since needed in some base packages */
int (PRIMOFFSET)(SEXP x) { return PRIMOFFSET(x); }
attribute_hidden
void (SET_PRIMOFFSET)(SEXP x, int v) { SET_PRIMOFFSET(x, v); }
#endif

/* Symbol Accessors */
SEXP (PRINTNAME)(SEXP x) { return CHK(PRINTNAME(CHK(x))); }
SEXP (SYMVALUE)(SEXP x) { return CHK(SYMVALUE(CHK(x))); }
SEXP (INTERNAL)(SEXP x) { return CHK(INTERNAL(CHK(x))); }
int (DDVAL)(SEXP x) { return DDVAL(CHK(x)); }

void (SET_PRINTNAME)(SEXP x, SEXP v) { FIX_REFCNT(x, PRINTNAME(x), v); CHECK_OLD_TO_NEW(x, v); PRINTNAME(x) = v; }
void (SET_SYMVALUE)(SEXP x, SEXP v) { FIX_REFCNT(x, SYMVALUE(x), v); CHECK_OLD_TO_NEW(x, v); SYMVALUE(x) = v; }
void (SET_INTERNAL)(SEXP x, SEXP v) { FIX_REFCNT(x, INTERNAL(x), v); CHECK_OLD_TO_NEW(x, v); INTERNAL(x) = v; }
void (SET_DDVAL)(SEXP x, int v) { SET_DDVAL(CHK(x), v); }

/* Environment Accessors */
SEXP (FRAME)(SEXP x) { return CHK(FRAME(CHK(x))); }
SEXP (ENCLOS)(SEXP x) { return CHK(ENCLOS(CHK(x))); }
SEXP (HASHTAB)(SEXP x) { return CHK(HASHTAB(CHK(x))); }
int (ENVFLAGS)(SEXP x) { return ENVFLAGS(CHK(x)); }

void (SET_FRAME)(SEXP x, SEXP v) { FIX_REFCNT(x, FRAME(x), v); CHECK_OLD_TO_NEW(x, v); FRAME(x) = v; }
void (SET_ENCLOS)(SEXP x, SEXP v) { FIX_REFCNT(x, ENCLOS(x), v); CHECK_OLD_TO_NEW(x, v); ENCLOS(x) = v; }
void (SET_HASHTAB)(SEXP x, SEXP v) { FIX_REFCNT(x, HASHTAB(x), v); CHECK_OLD_TO_NEW(x, v); HASHTAB(x) = v; }
void (SET_ENVFLAGS)(SEXP x, int v) { SET_ENVFLAGS(x, v); }

/* Promise Accessors */
SEXP (PRCODE)(SEXP x) { return CHK(PRCODE(CHK(x))); }
SEXP (PRENV)(SEXP x) { return CHK(PRENV(CHK(x))); }
SEXP (PRVALUE)(SEXP x) { return CHK(PRVALUE(CHK(x))); }
int (PRSEEN)(SEXP x) { return PRSEEN(CHK(x)); }

void (SET_PRENV)(SEXP x, SEXP v){ FIX_REFCNT(x, PRENV(x), v); CHECK_OLD_TO_NEW(x, v); PRENV(x) = v; }
void (SET_PRVALUE)(SEXP x, SEXP v) { FIX_REFCNT(x, PRVALUE(x), v); CHECK_OLD_TO_NEW(x, v); PRVALUE(x) = v; }
void (SET_PRCODE)(SEXP x, SEXP v) { FIX_REFCNT(x, PRCODE(x), v); CHECK_OLD_TO_NEW(x, v); PRCODE(x) = v; }
void (SET_PRSEEN)(SEXP x, int v) { SET_PRSEEN(CHK(x), v); }

/* Hashing Accessors */
#ifdef TESTING_WRITE_BARRIER
attribute_hidden
int (HASHASH)(SEXP x) { return HASHASH(CHK(x)); }
attribute_hidden
int (HASHVALUE)(SEXP x) { return HASHVALUE(CHK(x)); }

attribute_hidden
void (SET_HASHASH)(SEXP x, int v) { SET_HASHASH(CHK(x), v); }
attribute_hidden
void (SET_HASHVALUE)(SEXP x, int v) { SET_HASHVALUE(CHK(x), v); }
#endif

attribute_hidden
SEXP (SET_CXTAIL)(SEXP x, SEXP v) {
#ifdef USE_TYPE_CHECKING
    if(TYPEOF(v) != CHARSXP && TYPEOF(v) != NILSXP)
	error("value of 'SET_CXTAIL' must be a char or NULL, not a '%s'",
	      type2char(TYPEOF(v)));
#endif
    /*CHECK_OLD_TO_NEW(x, v); *//* not needed since not properly traced */
    ATTRIB(x) = v;
    return x;
}

/* Test functions */
Rboolean Rf_isNull(SEXP s) { return isNull(s); }
Rboolean Rf_isSymbol(SEXP s) { return isSymbol(s); }
Rboolean Rf_isLogical(SEXP s) { return isLogical(s); }
Rboolean Rf_isReal(SEXP s) { return isReal(s); }
Rboolean Rf_isComplex(SEXP s) { return isComplex(s); }
Rboolean Rf_isExpression(SEXP s) { return isExpression(s); }
Rboolean Rf_isEnvironment(SEXP s) { return isEnvironment(s); }
Rboolean Rf_isString(SEXP s) { return isString(s); }
Rboolean Rf_isObject(SEXP s) { return isObject(s); }

/* Bindings accessors */
Rboolean attribute_hidden
(IS_ACTIVE_BINDING)(SEXP b) {return IS_ACTIVE_BINDING(b);}
Rboolean attribute_hidden
(BINDING_IS_LOCKED)(SEXP b) {return BINDING_IS_LOCKED(b);}
void attribute_hidden
(SET_ACTIVE_BINDING_BIT)(SEXP b) {SET_ACTIVE_BINDING_BIT(b);}
void attribute_hidden (LOCK_BINDING)(SEXP b) {LOCK_BINDING(b);}
void attribute_hidden (UNLOCK_BINDING)(SEXP b) {UNLOCK_BINDING(b);}

attribute_hidden
void (SET_BASE_SYM_CACHED)(SEXP b) { SET_BASE_SYM_CACHED(b); }
attribute_hidden
void (UNSET_BASE_SYM_CACHED)(SEXP b) { UNSET_BASE_SYM_CACHED(b); }
attribute_hidden
Rboolean (BASE_SYM_CACHED)(SEXP b) { return BASE_SYM_CACHED(b); }

attribute_hidden
void (SET_SPECIAL_SYMBOL)(SEXP b) { SET_SPECIAL_SYMBOL(b); }
attribute_hidden
void (UNSET_SPECIAL_SYMBOL)(SEXP b) { UNSET_SPECIAL_SYMBOL(b); }
attribute_hidden
Rboolean (IS_SPECIAL_SYMBOL)(SEXP b) { return IS_SPECIAL_SYMBOL(b); }
attribute_hidden
void (SET_NO_SPECIAL_SYMBOLS)(SEXP b) { SET_NO_SPECIAL_SYMBOLS(b); }
attribute_hidden
void (UNSET_NO_SPECIAL_SYMBOLS)(SEXP b) { UNSET_NO_SPECIAL_SYMBOLS(b); }
attribute_hidden
Rboolean (NO_SPECIAL_SYMBOLS)(SEXP b) { return NO_SPECIAL_SYMBOLS(b); }

/* R_FunTab accessors, only needed when write barrier is on */
/* Not hidden to allow experimentaiton without rebuilding R - LT */
/* attribute_hidden */
int (PRIMVAL)(SEXP x) { return PRIMVAL(x); }
/* attribute_hidden */
CCODE (PRIMFUN)(SEXP x) { return PRIMFUN(x); }
/* attribute_hidden */
void (SET_PRIMFUN)(SEXP x, CCODE f) { PRIMFUN(x) = f; }

/* for use when testing the write barrier */
int  attribute_hidden (IS_BYTES)(SEXP x) { return IS_BYTES(x); }
int  attribute_hidden (IS_LATIN1)(SEXP x) { return IS_LATIN1(x); }
int  attribute_hidden (IS_ASCII)(SEXP x) { return IS_ASCII(x); }
int  attribute_hidden (IS_UTF8)(SEXP x) { return IS_UTF8(x); }
void attribute_hidden (SET_BYTES)(SEXP x) { SET_BYTES(x); }
void attribute_hidden (SET_LATIN1)(SEXP x) { SET_LATIN1(x); }
void attribute_hidden (SET_UTF8)(SEXP x) { SET_UTF8(x); }
void attribute_hidden (SET_ASCII)(SEXP x) { SET_ASCII(x); }
int  (ENC_KNOWN)(SEXP x) { return ENC_KNOWN(x); }
void attribute_hidden (SET_CACHED)(SEXP x) { SET_CACHED(x); }
int  (IS_CACHED)(SEXP x) { return IS_CACHED(x); }

/*******************************************/
/* Non-sampling memory use profiler
   reports all large vector heap
   allocations and all calls to GetNewPage */
/*******************************************/

#ifndef R_MEMORY_PROFILING

SEXP NORET do_Rprofmem(SEXP args)
{
    error(_("memory profiling is not available on this system"));
}

#else
static int R_IsMemReporting;  /* Rboolean more appropriate? */
static FILE *R_MemReportingOutfile;
static R_size_t R_MemReportingThreshold;

static void R_OutputStackTrace(FILE *file)
{
    int newline = 0;
    RCNTXT *cptr;

    for (cptr = R_GlobalContext; cptr; cptr = cptr->nextcontext) {
	if ((cptr->callflag & (CTXT_FUNCTION | CTXT_BUILTIN))
	    && TYPEOF(cptr->call) == LANGSXP) {
	    SEXP fun = CAR(cptr->call);
	    if (!newline) newline = 1;
	    fprintf(file, "\"%s\" ",
		    TYPEOF(fun) == SYMSXP ? CHAR(PRINTNAME(fun)) :
		    "<Anonymous>");
	}
    }
    if (newline) fprintf(file, "\n");
}

static void R_ReportAllocation(R_size_t size)
{
    if (R_IsMemReporting) {
	if(size > R_MemReportingThreshold) {
	    fprintf(R_MemReportingOutfile, "%lu :", (unsigned long) size);
	    R_OutputStackTrace(R_MemReportingOutfile);
	}
    }
    return;
}

static void R_ReportNewPage(void)
{
    if (R_IsMemReporting) {
	fprintf(R_MemReportingOutfile, "new page:");
	R_OutputStackTrace(R_MemReportingOutfile);
    }
    return;
}

static void R_EndMemReporting()
{
    if(R_MemReportingOutfile != NULL) {
	/* does not fclose always flush? */
	fflush(R_MemReportingOutfile);
	fclose(R_MemReportingOutfile);
	R_MemReportingOutfile=NULL;
    }
    R_IsMemReporting = 0;
    return;
}

static void R_InitMemReporting(SEXP filename, int append,
			       R_size_t threshold)
{
    if(R_MemReportingOutfile != NULL) R_EndMemReporting();
    R_MemReportingOutfile = RC_fopen(filename, append ? "a" : "w", TRUE);
    if (R_MemReportingOutfile == NULL)
	error(_("Rprofmem: cannot open output file '%s'"), filename);
    R_MemReportingThreshold = threshold;
    R_IsMemReporting = 1;
    return;
}

SEXP do_Rprofmem(SEXP args)
{
    SEXP filename;
    R_size_t threshold;
    int append_mode;

    if (!isString(CAR(args)) || (LENGTH(CAR(args))) != 1)
	error(_("invalid '%s' argument"), "filename");
    append_mode = asLogical(CADR(args));
    filename = STRING_ELT(CAR(args), 0);
    threshold = (R_size_t) REAL(CADDR(args))[0];
    if (strlen(CHAR(filename)))
	R_InitMemReporting(filename, append_mode, threshold);
    else
	R_EndMemReporting();
    return R_NilValue;
}

#endif /* R_MEMORY_PROFILING */

/* RBufferUtils, moved from deparse.c */

#include "RBufferUtils.h"

void *R_AllocStringBuffer(size_t blen, R_StringBuffer *buf)
{
    size_t blen1, bsize = buf->defaultSize;

    /* for backwards compatibility, this used to free the buffer */
    if(blen == (size_t)-1)
	error("R_AllocStringBuffer( (size_t)-1 ) is no longer allowed");

    if(blen * sizeof(char) < buf->bufsize) return buf->data;
    blen1 = blen = (blen + 1) * sizeof(char);
    blen = (blen / bsize) * bsize;
    if(blen < blen1) blen += bsize;

    if(buf->data == NULL) {
	buf->data = (char *) malloc(blen);
	if(buf->data)
	    buf->data[0] = '\0';
    } else
	buf->data = (char *) realloc(buf->data, blen);
    buf->bufsize = blen;
    if(!buf->data) {
	buf->bufsize = 0;
	/* don't translate internal error message */
	error("could not allocate memory (%u Mb) in C function 'R_AllocStringBuffer'",
	      (unsigned int) blen/1024/1024);
    }
    return buf->data;
}

void
R_FreeStringBuffer(R_StringBuffer *buf)
{
    if (buf->data != NULL) {
	free(buf->data);
	buf->bufsize = 0;
	buf->data = NULL;
    }
}

void attribute_hidden
R_FreeStringBufferL(R_StringBuffer *buf)
{
    if (buf->bufsize > buf->defaultSize) {
	free(buf->data);
	buf->bufsize = 0;
	buf->data = NULL;
    }
}

/* ======== This needs direct access to gp field for efficiency ======== */

/* this has NA_STRING = NA_STRING */
attribute_hidden
int Seql(SEXP a, SEXP b)
{
    /* The only case where pointer comparisons do not suffice is where
      we have two strings in different encodings (which must be
      non-ASCII strings). Note that one of the strings could be marked
      as unknown. */
    if (a == b) return 1;
    /* Leave this to compiler to optimize */
    if (IS_CACHED(a) && IS_CACHED(b) && ENC_KNOWN(a) == ENC_KNOWN(b))
	return 0;
    else {
	SEXP vmax = R_VStack;
	int result = !strcmp(translateCharUTF8(a), translateCharUTF8(b));
	R_VStack = vmax; /* discard any memory used by translateCharUTF8 */
	return result;
    }
}


#ifdef LONG_VECTOR_SUPPORT
R_len_t NORET R_BadLongVector(SEXP x, const char *file, int line)
{
    error(_("long vectors not supported yet: %s:%d"), file, line);
}
#endif
/*
 * Source code from Xfig 3.2.4 modified to work with arrays of doubles
 * instead linked lists of F_points and to remove some globals(!)
 * See copyright etc below.
 *
 * #included from engine.c
 * That manages the R_alloc stack.
 */

/*
 * From w_drawprim.h
 */

#define         MAXNUMPTS       25000

/*
 * From u_draw.c
 */

/*
 * FIG : Facility for Interactive Generation of figures
 * Copyright (c) 1985-1988 by Supoj Sutanthavibul
 * Parts Copyright (c) 1989-2002 by Brian V. Smith
 * Parts Copyright (c) 1991 by Paul King
 * Parts Copyright (c) 1992 by James Tough
 * Parts Copyright (c) 1998 by Georg Stemmer
 * Parts Copyright (c) 1995 by C. Blanc and C. Schlick
 *
 * Any party obtaining a copy of these files is granted, free of charge, a
 * full and unrestricted irrevocable, world-wide, paid up, royalty-free,
 * nonexclusive right and license to deal in this software and
 * documentation files (the "Software"), including without limitation the
 * rights to use, copy, modify, merge, publish and/or distribute copies of
 * the Software, and to permit persons who receive copies from any such
 * party to do so, with the only requirement being that this copyright
 * notice remain intact.
 *
 */

/************** POLYGON/CURVE DRAWING FACILITIES ****************/

static int npoints;
static int max_points;
static double *xpoints;
static double *ypoints;

/************* Code begins here *************/

/* R_allocs or mallocs global arrays */
static Rboolean
add_point(double x, double y, pGEDevDesc dd)
{
    if (npoints >= max_points) {
	int tmp_n;
	double *tmp_px;
	double *tmp_py;
	tmp_n = max_points + 200;
	/* too many points, return false */
	if (tmp_n > MAXNUMPTS) {
	    error(_("add_point - reached MAXNUMPTS (%d)"),tmp_n);
	}
	if (max_points == 0) {
	    tmp_px = (double *) R_alloc(tmp_n, sizeof(double));
	    tmp_py = (double *) R_alloc(tmp_n, sizeof(double));
	} else {
	    tmp_px = (double *) S_realloc((char *) xpoints,
					  tmp_n, max_points,
					  sizeof(double));
	    tmp_py = (double *) S_realloc((char *) ypoints,
					  tmp_n, max_points,
					  sizeof(double));
	}
	if (tmp_px == NULL || tmp_py == NULL) {
	    error(_("insufficient memory to allocate point array"));
	}
	xpoints = tmp_px;
	ypoints = tmp_py;
	max_points = tmp_n;
    }
    /* ignore identical points */
    if (npoints > 0 && xpoints[npoints-1] == x && ypoints[npoints-1] == y)
	return TRUE;
    /*
     * Convert back from 1200ppi to DEVICE coordinates
     */
    xpoints[npoints] = toDeviceX(x / 1200, GE_INCHES, dd);
    ypoints[npoints] = toDeviceY(y / 1200, GE_INCHES, dd);
    npoints = npoints + 1;
    return TRUE;
}

/*
 * From u_draw_spline.c
 */

/*
 * FIG : Facility for Interactive Generation of figures
 * Copyright (c) 1985-1988 by Supoj Sutanthavibul
 * Parts Copyright (c) 1989-2002 by Brian V. Smith
 * Parts Copyright (c) 1991 by Paul King
 *
 * Any party obtaining a copy of these files is granted, free of charge, a
 * full and unrestricted irrevocable, world-wide, paid up, royalty-free,
 * nonexclusive right and license to deal in this software and
 * documentation files (the "Software"), including without limitation the
 * rights to use, copy, modify, merge, publish and/or distribute copies of
 * the Software, and to permit persons who receive copies from any such
 * party to do so, with the only requirement being that this copyright
 * notice remain intact.
 *
 */

/* THIS FILE IS #included FROM u_draw.c and u_geom.c */

/********************* CURVES FOR SPLINES *****************************

 The following spline drawing routines are from

    "X-splines : A Spline Model Designed for the End User"

    by Carole BLANC and Christophe SCHLICK,
    in Proceedings of SIGGRAPH ' 95

***********************************************************************/

#define         HIGH_PRECISION    0.5
#define         LOW_PRECISION     1.0
#define         ZOOM_PRECISION    5.0
#define         ARROW_START       4
#define         MAX_SPLINE_STEP   0.2

/***********************************************************************/

#define Q(s)  (-(s))
#define EQN_NUMERATOR(dim) \
  (A_blend[0]*dim[0]+A_blend[1]*dim[1]+A_blend[2]*dim[2]+A_blend[3]*dim[3])

static double
f_blend(double numerator, double denominator)
{
  double p = 2 * denominator * denominator;
  double u = numerator / denominator;
  double u2 = u * u;

  return (u * u2 * (10 - p + (2*p - 15)*u + (6 - p)*u2));
}

static double
g_blend(double u, double q)             /* p equals 2 */
{
  return(u*(q + u*(2*q + u*(8 - 12*q + u*(14*q - 11 + u*(4 - 5*q))))));
}

static double
h_blend(double u, double q)
{
    double u2=u*u;
    return (u * (q + u * (2 * q + u2 * (-2*q - u*q))));
}

static void
negative_s1_influence(double t, double s1, double *A0, double *A2)
{
  *A0 = h_blend(-t, Q(s1));
  *A2 = g_blend(t, Q(s1));
}

static void
negative_s2_influence(double t, double s2, double *A1, double *A3)
{
  *A1 = g_blend(1-t, Q(s2));
  *A3 = h_blend(t-1, Q(s2));
}

static void
positive_s1_influence(double k, double t, double s1, double *A0, double *A2)
{
  double Tk;

  Tk = k+1+s1;
  *A0 = (t+k+1<Tk) ? f_blend(t+k+1-Tk, k-Tk) : 0.0;

  Tk = k+1-s1;
  *A2 = f_blend(t+k+1-Tk, k+2-Tk);
}

static void
positive_s2_influence(double k, double t, double s2, double *A1, double *A3)
{
  double Tk;

  Tk = k+2+s2;
  *A1 = f_blend(t+k+1-Tk, k+1-Tk);

  Tk = k+2-s2;
  *A3 = (t+k+1>Tk) ? f_blend(t+k+1-Tk, k+3-Tk) : 0.0;
}

static void
point_adding(double *A_blend, double *px, double *py,
	     pGEDevDesc dd)
{
  double weights_sum;

  weights_sum = A_blend[0] + A_blend[1] + A_blend[2] + A_blend[3];
  add_point(EQN_NUMERATOR(px) / (weights_sum),
	    EQN_NUMERATOR(py) / (weights_sum),
	    dd);
}

static void
point_computing(double *A_blend,
		double *px, double *py,
		double *x, double *y)
{
  double weights_sum;

  weights_sum = A_blend[0] + A_blend[1] + A_blend[2] + A_blend[3];

  *x = EQN_NUMERATOR(px) / (weights_sum);
  *y = EQN_NUMERATOR(py) / (weights_sum);
}

static double
step_computing(int k,
	       double *px, double *py,
	       double s1, double s2,
	       double precision,
               pGEDevDesc dd)
{
  double A_blend[4];
  double xstart, ystart, xend, yend, xmid, ymid, xlength, ylength;
  double start_to_end_dist, devWidth, devHeight, devDiag, number_of_steps;
  double  step, angle_cos, scal_prod, xv1, xv2, yv1, yv2, sides_length_prod;

  /* This function computes the step used to draw the segment (p1, p2)
     (xv1, yv1) : coordinates of the vector from middle to origin
     (xv2, yv2) : coordinates of the vector from middle to extremity */

  if ((s1 == 0) && (s2 == 0))
    return(1.0);              /* only one step in case of linear segment */

  /* compute coordinates of the origin */
  if (s1>0) {
      if (s2<0) {
	  positive_s1_influence(k, 0.0, s1, &A_blend[0], &A_blend[2]);
	  negative_s2_influence(0.0, s2, &A_blend[1], &A_blend[3]);
      } else {
	  positive_s1_influence(k, 0.0, s1, &A_blend[0], &A_blend[2]);
	  positive_s2_influence(k, 0.0, s2, &A_blend[1], &A_blend[3]);
      }
      point_computing(A_blend, px, py, &xstart, &ystart);
  } else {
      xstart = px[1];
      ystart = py[1];
  }

  /* compute coordinates  of the extremity */
  if (s2>0) {
      if (s1<0) {
	  negative_s1_influence(1.0, s1, &A_blend[0], &A_blend[2]);
	  positive_s2_influence(k, 1.0, s2, &A_blend[1], &A_blend[3]);
      } else {
	  positive_s1_influence(k, 1.0, s1, &A_blend[0], &A_blend[2]);
	  positive_s2_influence(k, 1.0, s2, &A_blend[1], &A_blend[3]);
      }
      point_computing(A_blend, px, py, &xend, &yend);
  } else {
      xend = px[2];
      yend = py[2];
  }

  /* compute coordinates  of the middle */
  if (s2>0) {
      if (s1<0) {
	  negative_s1_influence(0.5, s1, &A_blend[0], &A_blend[2]);
	  positive_s2_influence(k, 0.5, s2, &A_blend[1], &A_blend[3]);
      } else {
	  positive_s1_influence(k, 0.5, s1, &A_blend[0], &A_blend[2]);
	  positive_s2_influence(k, 0.5, s2, &A_blend[1], &A_blend[3]);
	}
  } else if (s1<0) {
      negative_s1_influence(0.5, s1, &A_blend[0], &A_blend[2]);
      negative_s2_influence(0.5, s2, &A_blend[1], &A_blend[3]);
  } else {
      positive_s1_influence(k, 0.5, s1, &A_blend[0], &A_blend[2]);
      negative_s2_influence(0.5, s2, &A_blend[1], &A_blend[3]);
  }
  point_computing(A_blend, px, py, &xmid, &ymid);

  xv1 = xstart - xmid;
  yv1 = ystart - ymid;
  xv2 = xend - xmid;
  yv2 = yend - ymid;

  scal_prod = xv1*xv2 + yv1*yv2;

  sides_length_prod = sqrt((xv1*xv1 + yv1*yv1)*(xv2*xv2 + yv2*yv2));

  /* compute cosinus of origin-middle-extremity angle, which approximates the
     curve of the spline segment */
  if (sides_length_prod == 0.0)
    angle_cos = 0.0;
  else
    angle_cos = scal_prod/sides_length_prod;

  xlength = xend - xstart;
  ylength = yend - ystart;

  start_to_end_dist = sqrt(xlength*xlength + ylength*ylength);

  /* Paul 2009-01-25
   * It is possible for origin and extremity to be very remote
   * indeed (if the control points are located WAY off the device).
   * In order to avoid having ridiculously many steps, limit
   * the start_to_end_dist to being the length of the diagonal of the 
   * device.
   */
  devWidth = fromDeviceWidth(toDeviceWidth(1, GE_NDC, dd),
                             GE_INCHES, dd)*1200;
  devHeight = fromDeviceHeight(toDeviceHeight(1, GE_NDC, dd),
                               GE_INCHES, dd)*1200;
  devDiag = sqrt(devWidth* devWidth + devHeight*devHeight);
  if (start_to_end_dist > devDiag)
      start_to_end_dist = devDiag;

  /* more steps if segment's origin and extremity are remote */
  number_of_steps = sqrt(start_to_end_dist)/2;

  /* more steps if the curve is high */
  number_of_steps += (int)((1 + angle_cos)*10);

  if (number_of_steps == 0)
    step = 1;
  else
    step = precision/number_of_steps;

  if ((step > MAX_SPLINE_STEP) || (step == 0))
    step = MAX_SPLINE_STEP;

  return (step);
}

static void
spline_segment_computing(double step, int k,
			 double *px, double *py,
			 double s1, double s2,
			 pGEDevDesc dd)
{
  double A_blend[4];
  double t;

  if (s1<0) {
     if (s2<0) {
	 for (t=0.0 ; t<1 ; t+=step) {
	     negative_s1_influence(t, s1, &A_blend[0], &A_blend[2]);
	     negative_s2_influence(t, s2, &A_blend[1], &A_blend[3]);

	     point_adding(A_blend, px, py, dd);
	 }
     } else {
	 for (t=0.0 ; t<1 ; t+=step) {
	     negative_s1_influence(t, s1, &A_blend[0], &A_blend[2]);
	     positive_s2_influence(k, t, s2, &A_blend[1], &A_blend[3]);

	     point_adding(A_blend, px, py, dd);
	 }
     }
  } else if (s2<0) {
      for (t=0.0 ; t<1 ; t+=step) {
	     positive_s1_influence(k, t, s1, &A_blend[0], &A_blend[2]);
	     negative_s2_influence(t, s2, &A_blend[1], &A_blend[3]);

	     point_adding(A_blend, px, py, dd);
      }
  } else {
      for (t=0.0 ; t<1 ; t+=step) {
	     positive_s1_influence(k, t, s1, &A_blend[0], &A_blend[2]);
	     positive_s2_influence(k, t, s2, &A_blend[1], &A_blend[3]);

	     point_adding(A_blend, px, py, dd);
      }
  }
}

/*
 * For adding last line segment when computing open spline
 * WITHOUT end control points repeated
 * (i.e., can't just connect to last control point)
 */
static void
spline_last_segment_computing(double step, int k,
			      double *px, double *py,
			      double s1, double s2,
			      pGEDevDesc dd)
{
  double A_blend[4];
  double t = 1;

  if (s1<0) {
      if (s2<0) {
	  negative_s1_influence(t, s1, &A_blend[0], &A_blend[2]);
	  negative_s2_influence(t, s2, &A_blend[1], &A_blend[3]);

	  point_adding(A_blend, px, py, dd);
      } else {
	  negative_s1_influence(t, s1, &A_blend[0], &A_blend[2]);
	  positive_s2_influence(k, t, s2, &A_blend[1], &A_blend[3]);

	  point_adding(A_blend, px, py, dd);
      }
  } else if (s2<0) {
      positive_s1_influence(k, t, s1, &A_blend[0], &A_blend[2]);
      negative_s2_influence(t, s2, &A_blend[1], &A_blend[3]);

      point_adding(A_blend, px, py, dd);
  } else {
      positive_s1_influence(k, t, s1, &A_blend[0], &A_blend[2]);
      positive_s2_influence(k, t, s2, &A_blend[1], &A_blend[3]);

      point_adding(A_blend, px, py, dd);
  }
}

/********************* MAIN METHODS *************************************/

/*
 * x and y are in DEVICE coordinates
 * xfig works in 1200ppi
 *   (http://www.csit.fsu.edu/~burkardt/data/fig/fig_format.html)
 * so convert to 1200ppi so that step calculations are correct
 */
#define COPY_CONTROL_POINT(PI, I, N) \
      px[PI] = fromDeviceX(x[(I) % N], GE_INCHES, dd) * 1200; \
      py[PI] = fromDeviceY(y[(I) % N], GE_INCHES, dd) * 1200; \
      ps[PI] = s[(I) % N]

#define NEXT_CONTROL_POINTS(K, N) \
      COPY_CONTROL_POINT(0, K, N); \
      COPY_CONTROL_POINT(1, K + 1, N); \
      COPY_CONTROL_POINT(2, K + 2, N); \
      COPY_CONTROL_POINT(3, K + 3, N)

#define INIT_CONTROL_POINTS(N) \
      COPY_CONTROL_POINT(0, N - 1, N); \
      COPY_CONTROL_POINT(1, 0, N); \
      COPY_CONTROL_POINT(2, 1, N); \
      COPY_CONTROL_POINT(3, 2, N)

#define SPLINE_SEGMENT_LOOP(K, PX, PY, S1, S2, PREC) \
      step = step_computing(K, PX, PY, S1, S2, PREC, dd);    \
      spline_segment_computing(step, K, PX, PY, S1, S2, dd)

static Rboolean
compute_open_spline(int n, double *x, double *y, double *s,
		    Rboolean repEnds,
		    double precision,
		    pGEDevDesc dd)
{
  int       k;
  double     step = 0.0 /* -Wall */;
  double px[4];
  double py[4];
  double ps[4]={0.,0.,0.,0.};

  max_points = 0;
  npoints = 0;
  xpoints = NULL;
  ypoints = NULL;

  if (repEnds && n < 2)
      error(_("there must be at least two control points"));
  if (!repEnds && n < 4)
      error(_("there must be at least four control points"));

  if (repEnds) {
      /* first control point is needed twice for the first segment */
      COPY_CONTROL_POINT(0, 0, n);
      COPY_CONTROL_POINT(1, 0, n);
      COPY_CONTROL_POINT(2, 1, n);

      if (n == 2) {
	COPY_CONTROL_POINT(3, 1, n);
      } else {
	COPY_CONTROL_POINT(3, 2, n);
      }

      for (k = 0 ; ; k++) {
	  SPLINE_SEGMENT_LOOP(k, px, py, ps[1], ps[2], precision);
          /* Paul 2008-12-05
           * >= rather than == to handle special case of n == 2
           */
	  if (k + 3 >= n)
	      break;
	  NEXT_CONTROL_POINTS(k, n);
      }

      /* last control point is needed twice for the last segment */
      COPY_CONTROL_POINT(0, n - 3, n);
      COPY_CONTROL_POINT(1, n - 2, n);
      COPY_CONTROL_POINT(2, n - 1, n);
      COPY_CONTROL_POINT(3, n - 1, n);
      SPLINE_SEGMENT_LOOP(k, px, py, ps[1], ps[2], precision);

      add_point(px[3], py[3], dd);
  } else {
      for (k = 0 ; k + 3 < n ; k++) {
	  NEXT_CONTROL_POINTS(k, n);
	  SPLINE_SEGMENT_LOOP(k, px, py, ps[1], ps[2], precision);
      }
      spline_last_segment_computing(step, n - 4, px, py, ps[1], ps[2], dd);
  }

  return TRUE;
}

static Rboolean
compute_closed_spline(int n, double *x, double *y, double *s,
		      double precision,
		      pGEDevDesc dd)
{
  int k;
  double step;
  double px[4];
  double py[4];
  double ps[4];

  max_points = 0;
  npoints = 0;
  xpoints = NULL;
  ypoints = NULL;

  if (n < 3)
      error(_("There must be at least three control points"));

  INIT_CONTROL_POINTS(n);

  for (k = 0 ; k < n ; k++) {
      SPLINE_SEGMENT_LOOP(k, px, py, ps[1], ps[2], precision);
      NEXT_CONTROL_POINTS(k, n);
  }

  return TRUE;
}
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 1997--2017  The R Core Team
 *  Copyright (C) 1995, 1996  Robert Gentleman and Ross Ihaka
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 *
 * EXPORTS:
 *
 *  OneIndex()        -- used for "[[<-" in ./subassign.c
 *  get1index()       -- used for "[["   in ./subassign.c & subset.c
 *  vectorIndex()     -- used for "[[" and "[[<-" with a vector arg

 *  mat2indsub()      -- for "mat[i]"     "    "            "

 *  makeSubscript()   -- for "[" and "[<-" in ./subset.c and ./subassign.c,
 *			 and "[[<-" with a scalar in ./subassign.c
 *  arraySubscript()  -- for "[i,j,..." and "[<-..." in ./subset.c, ./subassign.c
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <Defn.h>

#include <R_ext/Itermacros.h>

/* interval at which to check interrupts, a guess (~subsecond on current hw) */
#define NINTERRUPT 10000000

/* We might get a call with R_NilValue from subassignment code */
#define ECALL(call, yy)     if(call == R_NilValue) error(yy);    else errorcall(call, yy);
#define ECALL3(call, yy, A) if(call == R_NilValue) error(yy, A); else errorcall(call, yy, A);

/* This allows for the unusual case where x is of length 2,
   and x[[-m]] selects one element for m = 1, 2.
   So 'len' is only used if it is 2 and i is negative.
*/
static R_INLINE int integerOneIndex(int i, R_xlen_t len, SEXP call)
{
    int indx = -1;

    if (i > 0) /* a regular 1-based index from R */
	indx = i - 1;
    else if (i == 0 || len < 2) {
	ECALL3(call, _("attempt to select less than one element in %s"), "integerOneIndex");
    } else if (len == 2 && i > -3)
	indx = 2 + i;
    else {
	ECALL3(call, _("attempt to select more than one element in %s"), "integerOneIndex");
    }
    return indx;
}

/* Utility used (only in) do_subassign2_dflt(), i.e. "[[<-" in ./subassign.c : */
R_xlen_t attribute_hidden
OneIndex(SEXP x, SEXP s, R_xlen_t len, int partial, SEXP *newname,
	 int pos, SEXP call)
{
    SEXP names;
    R_xlen_t i, indx, nx;
    const void *vmax;

    if (pos < 0 && length(s) > 1) {
	ECALL3(call, _("attempt to select more than one element in %s"), "OneIndex");
    }
    if (pos < 0 && length(s) < 1) {
	ECALL3(call, _("attempt to select less than one element in %s"), "OneIndex");
    }

    if(pos < 0) pos = 0;

    indx = -1;
    *newname = R_NilValue;
    switch(TYPEOF(s)) {
    case LGLSXP:
    case INTSXP:
	indx = integerOneIndex(INTEGER(s)[pos], len, call);
	break;
    case REALSXP:
	indx = integerOneIndex((int)REAL(s)[pos], len, call);
	break;
    case STRSXP:
	vmax = vmaxget();
	nx = xlength(x);
	names = PROTECT(getAttrib(x, R_NamesSymbol));
	if (names != R_NilValue) {
	    /* Try for exact match */
	    for (i = 0; i < nx; i++) {
		const char *tmp = translateChar(STRING_ELT(names, i));
		if (!tmp[0]) continue;
		if (streql(tmp, translateChar(STRING_ELT(s, pos)))) {
		    indx = i;
		    break;
		}
	    }
	    // Try for partial match -- not ever used in current R (partial is 0)
	    if (partial && indx < 0) {
		size_t l = strlen(translateChar(STRING_ELT(s, pos)));
		for(i = 0; i < nx; i++) {
		    const char *tmp = translateChar(STRING_ELT(names, i));
		    if (!tmp[0]) continue;
		    if(!strncmp(tmp, translateChar(STRING_ELT(s, pos)), l)) {
			if(indx == -1 )
			    indx = i;
			else
			    indx = -2;
		    }
		}
	    }
	}
	UNPROTECT(1); /* names */
	if (indx == -1)
	    indx = nx;
	*newname = STRING_ELT(s, pos);
	vmaxset(vmax);
	break;
    case SYMSXP:
	vmax = vmaxget();
	nx = xlength(x);
	names = getAttrib(x, R_NamesSymbol);
	if (names != R_NilValue) {
	    PROTECT(names);
	    for (i = 0; i < nx; i++)
		if (streql(translateChar(STRING_ELT(names, i)),
			   translateChar(PRINTNAME(s)))) {
		    indx = i;
		    break;
		}
	    UNPROTECT(1); /* names */
	}
	if (indx == -1)
	    indx = nx;
	*newname = STRING_ELT(s, pos);
	vmaxset(vmax);
	break;
    default:
	ECALL3(call, _("invalid subscript type '%s'"), type2char(TYPEOF(s)));
    }
    return indx;
}

/* used here and in subset.c and subassign.c */
R_xlen_t attribute_hidden
get1index(SEXP s, SEXP names, R_xlen_t len, int pok, int pos, SEXP call)
{
/* Get a single index for the [[ and [[<- operators.
   Checks that only one index is being selected.
   Returns -1 for no match.

   s is the subscript
   len is the length of the object or dimension, with names its (dim)names.
   pos is len-1 or -1 for [[, -1 for [[<-
     -1 means use the only element of length-1 s.
   pok : is "partial ok" ?
	 if pok is -1, warn if partial matching occurs, but allow.
*/
    int  warn_pok = 0;
    const char *ss, *cur_name;
    R_xlen_t indx;
    const void *vmax;

    if (pok == -1) {
	pok = 1;
	warn_pok = 1;
    }

    if (pos < 0 && length(s) != 1) {
	if (length(s) > 1) {
	    ECALL3(call, _("attempt to select more than one element in %s"), "get1index");
	} else {
	    ECALL3(call, _("attempt to select less than one element in %s"), "get1index");
	}
    } else
	if(pos >= length(s)) {
	    ECALL(call, _("internal error in use of recursive indexing"));
	}
    if(pos < 0) pos = 0;
    indx = -1;
    switch (TYPEOF(s)) {
    case LGLSXP:
    case INTSXP:
    {
	int i = INTEGER(s)[pos];
	if (i != NA_INTEGER)
	    indx = integerOneIndex(i, len, call);
	break;
    }
    case REALSXP:
    {
	double dblind = REAL(s)[pos];
	if(!ISNAN(dblind)) {
	    /* see comment above integerOneIndex */
	    if (dblind > 0) indx = (R_xlen_t)(dblind - 1);
	    else if (dblind == 0 || len < 2) {
		ECALL3(call, _("attempt to select less than one element in %s"), "get1index <real>");
	    } else if (len == 2 && dblind > -3)
		indx = (R_xlen_t)(2 + dblind);
	    else {
		ECALL3(call, _("attempt to select more than one element in %s"), "get1index <real>");
	    }
	}
	break;
    }
    case STRSXP:
	/* NA matches nothing */
	if(STRING_ELT(s, pos) == NA_STRING) break;
	/* "" matches nothing: see names.Rd */
	if(!CHAR(STRING_ELT(s, pos))[0]) break;

	/* Try for exact match */
	vmax = vmaxget();
	ss = translateChar(STRING_ELT(s, pos));
	for (R_xlen_t i = 0; i < xlength(names); i++)
	    if (STRING_ELT(names, i) != NA_STRING) {
		if (streql(translateChar(STRING_ELT(names, i)), ss)) {
		    indx = i;
		    break;
		}
	    }
	/* Try for partial match */
	if (pok && indx < 0) {
	    size_t len = strlen(ss);
	    for(R_xlen_t i = 0; i < xlength(names); i++) {
		if (STRING_ELT(names, i) != NA_STRING) {
		    cur_name = translateChar(STRING_ELT(names, i));
		    if(!strncmp(cur_name, ss, len)) {
			if(indx == -1) {/* first one */
			    indx = i;
			    if (warn_pok) {
				if (call == R_NilValue)
				    warning(_("partial match of '%s' to '%s'"),
					    ss, cur_name);
				else
				    warningcall(call,
						_("partial match of '%s' to '%s'"),
						ss, cur_name);
			    }
			}
			else {
			    indx = -2;/* more than one partial match */
			    if (warn_pok) /* already given context */
				warningcall(R_NilValue,
					    _("further partial match of '%s' to '%s'"),
					    ss, cur_name);
			    break;
			}
		    }
		}
	    }
	}
	vmaxset(vmax);
	break;
    case SYMSXP:
	vmax = vmaxget();
	for (R_xlen_t i = 0; i < xlength(names); i++)
	    if (STRING_ELT(names, i) != NA_STRING &&
		streql(translateChar(STRING_ELT(names, i)),
		       CHAR(PRINTNAME(s)))) {
		indx = i;
		vmaxset(vmax);
		break;
	    }
	break;
    default:
	ECALL3(call, _("invalid subscript type '%s'"), type2char(TYPEOF(s)));
    }
    return indx;
}

/* This is used for [[ and [[<- with a vector of indices of length > 1 .
   x is a list or pairlist, and it is indexed recusively from
   level start to level stop-1.  ( 0...len-1 or 0..len-2 then len-1).
   For [[<- it needs to duplicate if substructure might be shared.
 */
SEXP attribute_hidden
vectorIndex(SEXP x, SEXP thesub, int start, int stop, int pok, SEXP call,
	    Rboolean dup)
{
    int i;
    R_xlen_t offset;
    SEXP cx;

    /* sanity check */
    if (dup && MAYBE_SHARED(x))
	error("should only be called in an assignment context.");

    for(i = start; i < stop; i++) {
	if(!isVectorList(x) && !isPairList(x)) {
	    if (i)
		errorcall(call, _("recursive indexing failed at level %d\n"), i+1);
	    else
		errorcall(call, _("attempt to select more than one element in %s"), "vectorIndex");
	}
	PROTECT(x);
	SEXP names = PROTECT(getAttrib(x, R_NamesSymbol));
	offset = get1index(thesub, names,
			   xlength(x), pok, i, call);
	UNPROTECT(2); /* x, names */
	if(offset < 0 || offset >= xlength(x))
	    errorcall(call, _("no such index at level %d\n"), i+1);
	if(isPairList(x)) {
#ifdef LONG_VECTOR_SUPPORT
	    if (offset > R_SHORT_LEN_MAX)
		error("invalid subscript for pairlist");
#endif
	    cx = nthcdr(x, (int) offset);
	    if (NAMED(x) > NAMED(CAR(cx)))
		SET_NAMED(CAR(x), NAMED(x));
	    x = CAR(cx);
	    if (dup && MAYBE_SHARED(x)) {
		PROTECT(cx);
		x = shallow_duplicate(x);
		SETCAR(cx, x);
		UNPROTECT(1); /* cx */
	    }
	} else {
	    cx = x;
	    x = VECTOR_ELT(x, offset);
	    if (NAMED(cx) > NAMED(x))
		SET_NAMED(x, NAMED(cx));
	    if (dup && MAYBE_SHARED(x)) {
		PROTECT(cx);
		x = shallow_duplicate(x);
		SET_VECTOR_ELT(cx, offset, x);
		UNPROTECT(1); /* cx */
	    }
	}
    }
    return x;
}

/* Special Matrix Subscripting: Handles the case x[i] where
   x is an n-way array and i is a matrix with n columns.
   This code returns a vector containing the subscripts
   to be extracted when x is regarded as unravelled.

   Negative indices are not allowed.

   A zero/NA anywhere in a row will cause a zero/NA in the same
   position in the result.
*/


SEXP attribute_hidden mat2indsub(SEXP dims, SEXP s, SEXP call)
{
    int nrs = nrows(s);
    R_xlen_t NR = nrs;
    SEXP rvec;

    if (ncols(s) != LENGTH(dims)) {
	ECALL(call, _("incorrect number of columns in matrix subscript"));
    }

#ifdef LONG_VECTOR_SUPPORT
    /* Check if it is a long vector we need to index */
    R_xlen_t len = 1;
    for (int j = 0; j < LENGTH(dims); j++)  len *= INTEGER(dims)[j];

    if(len > R_SHORT_LEN_MAX) {
	PROTECT(rvec = allocVector(REALSXP, nrs));
	double *rv = REAL(rvec);
	for (int i = 0; i < nrs; i++) rv[i] = 1.; // 1-based.
	if (TYPEOF(s) == REALSXP) {
	    for (int i = 0; i < nrs; i++) {
		R_xlen_t tdim = 1;
		for (int j = 0; j < LENGTH(dims); j++) {
		    double k = REAL(s)[i + j * NR];
		    if(ISNAN(k)) {rv[i] = NA_REAL; break;}
		    if(k < 0) {
			ECALL(call, _("negative values are not allowed in a matrix subscript"));
		    }
		    if(k == 0.) {rv[i] = 0.; break;}
		    if (k > INTEGER(dims)[j]) {
			ECALL(call, _("subscript out of bounds"));
		    }
		    rv[i] += (k - 1.) * tdim;
		    tdim *= INTEGER(dims)[j];
		}
	    }
	} else {
	    s = coerceVector(s, INTSXP);
	    for (int i = 0; i < nrs; i++) {
		R_xlen_t tdim = 1;
		for (int j = 0; j < LENGTH(dims); j++) {
		    int k = INTEGER(s)[i + j * NR];
		    if(k == NA_INTEGER) {rv[i] = NA_REAL; break;}
		    if(k < 0) {
			ECALL(call, _("negative values are not allowed in a matrix subscript"));
		    }
		    if(k == 0) {rv[i] = 0.; break;}
		    if (k > INTEGER(dims)[j]) {
			ECALL(call, _("subscript out of bounds"));
		    }
		    rv[i] += (double) ((k - 1) * tdim);
		    tdim *= INTEGER(dims)[j];
		}
	    }
	}
    } else
#endif
    {
	PROTECT(rvec = allocVector(INTSXP, nrs));
	int *iv = INTEGER(rvec);
	for (int i = 0; i < nrs; i++) iv[i] = 1; // 1-based.
	s = coerceVector(s, INTSXP);
	for (int i = 0; i < nrs; i++) {
	    int tdim = 1;
	    for (int j = 0; j < LENGTH(dims); j++) {
		int k = INTEGER(s)[i + j * NR];
		if(k == NA_INTEGER) {iv[i] = NA_INTEGER; break;}
		if(k < 0) {
		    ECALL(call, _("negative values are not allowed in a matrix subscript"));
		}
		if(k == 0) {iv[i] = 0; break;}
		if (k > INTEGER(dims)[j]) {
		    ECALL(call, _("subscript out of bounds"));
		}
		iv[i] += (k - 1) * tdim;
		tdim *= INTEGER(dims)[j];
	    }
	}
    }

    UNPROTECT(1);
    return rvec;
}

/*
Special Matrix Subscripting: For the case x[i] where x is an n-way
array and i is a character matrix with n columns, this code converts i
to an integer matrix by matching against the dimnames of x. NA values
in any row of i propagate to the result.  Unmatched entries result in
a subscript out of bounds error.  */

SEXP attribute_hidden strmat2intmat(SEXP s, SEXP dnamelist, SEXP call)
{
    /* XXX: assumes all args are protected */
    int nr = nrows(s), i, j, v;
    R_xlen_t idx, NR = nr;
    SEXP dnames, snames, si, sicol, s_elt;
    PROTECT(snames = allocVector(STRSXP, nr));
    PROTECT(si = allocVector(INTSXP, xlength(s)));
    dimgets(si, getAttrib(s, R_DimSymbol));
    for (i = 0; i < length(dnamelist); i++) {
	dnames = VECTOR_ELT(dnamelist, i);
	for (j = 0; j < nr; j++)
	    SET_STRING_ELT(snames, j, STRING_ELT(s, j + (i * NR)));
	PROTECT(sicol = match(dnames, snames, 0));
	for (j = 0; j < nr; j++) {
	    v = INTEGER(sicol)[j];
	    idx = j + (i * NR);
	    s_elt = STRING_ELT(s, idx);
	    if (s_elt == NA_STRING) v = NA_INTEGER;
	    if (!CHAR(s_elt)[0]) v = 0; /* disallow "" match */
	    if (v == 0) errorcall(call, _("subscript out of bounds"));
	    INTEGER(si)[idx] = v;
	}
	UNPROTECT(1);
    }
    UNPROTECT(2);
    return si;
}

static SEXP nullSubscript(R_xlen_t n)
{
    SEXP indx;
#ifdef LONG_VECTOR_SUPPORT
    if (n > R_SHORT_LEN_MAX) {
	indx = allocVector(REALSXP, n);
	for (R_xlen_t i = 0; i < n; i++)
	    REAL(indx)[i] = (double)(i + 1);
    } else
#endif
    {
	indx = allocVector(INTSXP, n);
	for (int i = 0; i < n; i++)
	    INTEGER(indx)[i] = i + 1;
    }
    return indx;
}


static SEXP
logicalSubscript(SEXP s, R_xlen_t ns, R_xlen_t nx, R_xlen_t *stretch, SEXP call)
{
    R_xlen_t count, i, nmax, i1, i2;
    int canstretch;
    SEXP indx;
    canstretch = *stretch > 0;
    if (!canstretch && ns > nx) {
	ECALL(call, _("(subscript) logical subscript too long"));
    }
    nmax = (ns > nx) ? ns : nx;
    *stretch = (ns > nx) ? ns : 0;
    if (ns == 0) return(allocVector(INTSXP, 0));
#ifdef LONG_VECTOR_SUPPORT
    if (nmax > R_SHORT_LEN_MAX) {
	if (ns == nmax) { /* no recycling - use fast single-index code */
	    const void *vmax = vmaxget();
	    double *buf = (double *) R_alloc(nmax, sizeof(double));
	    count = 0;
	    R_ITERATE_CHECK(NINTERRUPT, nmax, i,                    \
		if (LOGICAL(s)[i]) {                                \
		    if (LOGICAL(s)[i] == NA_LOGICAL)		    \
			buf[count++] = NA_REAL;		    \
		    else					    \
			buf[count++] = (double)(i + 1);	    \
		});
	    PROTECT(indx = allocVector(REALSXP, count));
	    memcpy(REAL(indx), buf, sizeof(double) * count);
	    vmaxset(vmax);
	    UNPROTECT(1);
	    return indx;
	}
	count = 0;
	/* we only need to scan s once even if we recycle,
	   just remember the total count as well as
	   the count for the last incomplete chunk (if any) */
	i1 = (ns < nmax) ? (nmax % ns) : 0;
	if (i1 > 0) { /* last recycling chunk is incomplete -
			 we have to get the truncated count as well */
	    R_xlen_t rem = 0;
	    for (i = 0; i < ns; i++) {
		if (i == i1) rem = count;
		if (LOGICAL(s)[i]) count++;
	    }
	    count = count * (nmax / ns) + rem;
	} else { /* nested recycling, total is sufficient */
	    for (i = 0; i < ns; i++)
		if (LOGICAL(s)[i]) count++;
	    count *= nmax / ns;
	}
	PROTECT(indx = allocVector(REALSXP, count));
	count = 0;
	MOD_ITERATE_CHECK(NINTERRUPT, nmax, ns, nmax, i, i1, i2, \
	    if (LOGICAL(s)[i1]) {				 \
		if (LOGICAL(s)[i1] == NA_LOGICAL)		 \
		    REAL(indx)[count++] = NA_REAL;		 \
		else						 \
		    REAL(indx)[count++] = (double)(i + 1);	 \
	    });

	UNPROTECT(1);
	return indx;
    }
#endif
// else --- the same code for  non-long vectors --------------------------
    if (ns == nmax) {  /* no recycling - use fast single-index code */
	const void *vmax = vmaxget();
	int *buf = (int *) R_alloc(nmax, sizeof(int));
	count = 0;
	R_ITERATE_CHECK(NINTERRUPT, nmax, i,                    \
	    if (LOGICAL(s)[i]) {                                \
		if (LOGICAL(s)[i] == NA_LOGICAL)	        \
		    buf[count++] = NA_INTEGER;		\
		else                                            \
		    buf[count++] = (int)(i + 1);		\
	    });
	PROTECT(indx = allocVector(INTSXP, count));
	memcpy(INTEGER(indx), buf, sizeof(int) * count);
	vmaxset(vmax);
	UNPROTECT(1);
	return indx;
    }

    count = 0;
    /* we only need to scan s once even if we recycle,
       just remember the total count as well as
       the count for the last incomplete chunk (if any) */
    i1 = (ns < nmax) ? (nmax % ns) : 0;
    if (i1 > 0) { /* last recycling chunk is incomplete -
		     we have to get the truncated count as well */
	R_xlen_t rem = 0;
	for (i = 0; i < ns; i++) {
	    if (i == i1) rem = count;
	    if (LOGICAL(s)[i]) count++;
	}
	count = count * (nmax / ns) + rem;
    } else { /* nested recycling, total is sufficient */
	for (i = 0; i < ns; i++)
	    if (LOGICAL(s)[i]) count++;
	count *= nmax / ns;
    }
    PROTECT(indx = allocVector(INTSXP, count));
    count = 0;
    MOD_ITERATE_CHECK(NINTERRUPT, nmax, ns, nmax, i, i1, i2,	\
	if (LOGICAL(s)[i1]) {				\
	    if (LOGICAL(s)[i1] == NA_LOGICAL)			\
		INTEGER(indx)[count++] = NA_INTEGER;		\
	    else						\
		INTEGER(indx)[count++] = (int)(i + 1);		\
	});

    UNPROTECT(1);
    return indx;
}

static SEXP negativeSubscript(SEXP s, R_xlen_t ns, R_xlen_t nx, SEXP call)
{
    SEXP indx;
    R_xlen_t stretch = 0;
    R_xlen_t i;
    PROTECT(indx = allocVector(LGLSXP, nx));
    for (i = 0; i < nx; i++)
	LOGICAL(indx)[i] = 1;
    for (i = 0; i < ns; i++) {
	int ix = INTEGER(s)[i];
	if (ix != 0 && ix != NA_INTEGER && -ix <= nx)
	    LOGICAL(indx)[-ix - 1] = 0;
    }
    s = logicalSubscript(indx, nx, nx, &stretch, call);
    UNPROTECT(1);
    return s;
}

static SEXP positiveSubscript(SEXP s, R_xlen_t ns, R_xlen_t nx)
{
    SEXP indx;
    R_xlen_t i, zct = 0;
    for (i = 0; i < ns; i++) if (INTEGER(s)[i] == 0) zct++;
    if (zct) {
	indx = allocVector(INTSXP, (ns - zct));
	for (i = 0, zct = 0; i < ns; i++)
	    if (INTEGER(s)[i] != 0)
		INTEGER(indx)[zct++] = INTEGER(s)[i];
	return indx;

    } else return s;
}

static SEXP
integerSubscript(SEXP s, R_xlen_t ns, R_xlen_t nx, R_xlen_t *stretch, SEXP call)
{
    R_xlen_t i;
    int ii, min, max, canstretch;
    Rboolean isna = FALSE;
    canstretch = *stretch > 0;
    *stretch = 0;
    min = 0;
    max = 0;
    for (i = 0; i < ns; i++) {
	ii = INTEGER(s)[i];
	if (ii != NA_INTEGER) {
	    if (ii < min)
		min = ii;
	    if (ii > max)
		max = ii;
	} else isna = TRUE;
    }
    if (max > nx) {
	if(canstretch) *stretch = max;
	else {
	    ECALL(call, _("subscript out of bounds"));
	}
    }
    if (min < 0) {
	if (max == 0 && !isna) return negativeSubscript(s, ns, nx, call);
	else {
	    ECALL(call, _("only 0's may be mixed with negative subscripts"));
	}
    }
    else return positiveSubscript(s, ns, nx);
    return R_NilValue;
}

static SEXP
realSubscript(SEXP s, R_xlen_t ns, R_xlen_t nx, R_xlen_t *stretch, SEXP call)
{
    R_xlen_t i;
    int canstretch;
    double ii, min, max;
    Rboolean isna = FALSE;
    canstretch = *stretch > 0;
    *stretch = 0;
    min = 0;
    max = 0;
    for (i = 0; i < ns; i++) {
	ii = REAL(s)[i];
	if (R_FINITE(ii)) {
	    if (ii < min) min = ii;
	    if (ii > max) max = ii;
	} else isna = TRUE;
    }
    if (max > nx) {
#ifndef LONG_VECTOR_SUPPORT
	if (max > INT_MAX) {
	    ECALL(call, _("subscript too large for 32-bit R"));
	}
#endif
	if(canstretch) *stretch = (R_xlen_t) max;
	else {
	    ECALL(call, _("subscript out of bounds"));
	}
    }
    if (min < 0) {
	if (max == 0 && !isna) {
	    SEXP indx;
	    R_xlen_t stretch = 0;
	    double dx;
	    R_xlen_t i, ix;
	    PROTECT(indx = allocVector(LGLSXP, nx));
	    for (i = 0; i < nx; i++) LOGICAL(indx)[i] = 1;
	    for (i = 0; i < ns; i++) {
		dx = REAL(s)[i];
		if (R_FINITE(dx) && dx != 0  && -dx <= nx) {
		    ix = (R_xlen_t)(-dx - 1);
		    LOGICAL(indx)[ix] = 0;
		}
	    }
	    s = logicalSubscript(indx, nx, nx, &stretch, call);
	    UNPROTECT(1);
	    return s;
	} else {
	    ECALL(call, _("only 0's may be mixed with negative subscripts"));
	}
    } else {
	/* Only return a REALSXP index if we need to */
	SEXP indx;
	R_xlen_t i, cnt = 0;
	Rboolean int_ok = TRUE;
	/* NB, indices will be truncated eventually,
	   so need to do that to take '0' into account */
	for (i = 0; i < ns; i++) {
	    double ds = REAL(s)[i];
#ifdef OLDCODE_LONG_VECTOR
	    if (!R_FINITE(ds)) {
		if (ds > INT_MAX) int_ok = FALSE;
		cnt++;
	    } else if ((R_xlen_t) ds != 0) cnt++;
#else
	    if (R_FINITE(ds) && ds > INT_MAX) int_ok = FALSE;
	    if (!R_FINITE(ds) || (R_xlen_t) ds != 0) cnt++;
#endif
	}
	if (int_ok) {
	    indx = allocVector(INTSXP, cnt);
	    for (i = 0, cnt = 0; i < ns; i++) {
		double ds = REAL(s)[i];
		int ia;
		if (!R_FINITE(ds)) ia = NA_INTEGER;
		else ia = (int) ds;
		if (ia != 0) INTEGER(indx)[cnt++] = ia;
	    }
	} else {
	    indx = allocVector(REALSXP, cnt);
	    for (i = 0, cnt = 0; i < ns; i++) {
		double ds = REAL(s)[i];
		if (!R_FINITE(ds) || (R_xlen_t) ds != 0) REAL(indx)[cnt++] = ds;
	    }
	}
	return indx;
    }
    return R_NilValue;
}

/* This uses a couple of horrible hacks in conjunction with
 * VectorAssign (in subassign.c).  If subscripting is used for
 * assignment, it is possible to extend a vector by supplying new
 * names, and we want to give the extended vector those names, so they
 * are returned as the use.names attribute. Also, unset elements of the vector
 * of new names (places where a match was found) are indicated by
 * setting the element of the newnames vector to NULL.
*/

/* The original code (pre 2.0.0) used a ns x nx loop that was too
 * slow.  So now we hash.  Hashing is expensive on memory (up to 32nx
 * bytes) so it is only worth doing if ns * nx is large.  If nx is
 * large, then it will be too slow unless ns is very small.
 */

static SEXP
stringSubscript(SEXP s, R_xlen_t ns, R_xlen_t nx, SEXP names,
		R_xlen_t *stretch, SEXP call)
{
    SEXP indx, indexnames;
    R_xlen_t i, j, nnames, extra, sub;
    int canstretch = *stretch > 0;
    /* product may overflow, so check factors as well. */
    Rboolean usehashing = ( ((ns > 1000 && nx) || (nx > 1000 && ns)) || (ns * nx > 15*nx + ns) );

    PROTECT(s);
    PROTECT(names);
    PROTECT(indexnames = allocVector(VECSXP, ns));
    nnames = nx;
    extra = nnames;

    /* Process each of the subscripts. First we compare with the names
     * on the vector and then (if there is no match) with each of the
     * previous subscripts, since (if assigning) we may have already
     * added an element of that name. (If we are not assigning, any
     * nonmatch will have given an error.)
     */

    if(usehashing) {
	/* must be internal, so names contains a character vector */
	/* NB: this does not behave in the same way with respect to ""
	   and NA names: they will match */
	PROTECT(indx = match(names, s, 0));
	/* second pass to correct this */
	for (i = 0; i < ns; i++)
	    if(STRING_ELT(s, i) == NA_STRING || !CHAR(STRING_ELT(s, i))[0])
		INTEGER(indx)[i] = 0;
	for (i = 0; i < ns; i++) SET_VECTOR_ELT(indexnames, i, R_NilValue);
    } else {
	PROTECT(indx = allocVector(INTSXP, ns));
	for (i = 0; i < ns; i++) {
	    sub = 0;
	    if (names != R_NilValue) {
		for (j = 0; j < nnames; j++) {
		    SEXP names_j = STRING_ELT(names, j);
		    if (NonNullStringMatch(STRING_ELT(s, i), names_j)) {
			sub = j + 1;
			SET_VECTOR_ELT(indexnames, i, R_NilValue);
			break;
		    }
		}
	    }
	    INTEGER(indx)[i] = (int) sub;
	}
    }


    for (i = 0; i < ns; i++) {
	sub = INTEGER(indx)[i];
	if (sub == 0) {
	    for (j = 0 ; j < i ; j++)
		if (NonNullStringMatch(STRING_ELT(s, i), STRING_ELT(s, j))) {
		    sub = INTEGER(indx)[j];
		    SET_VECTOR_ELT(indexnames, i, STRING_ELT(s, j));
		    break;
		}
	}
	if (sub == 0) {
	    if (!canstretch) {
		ECALL(call, _("subscript out of bounds"));
	    }
	    extra += 1;
	    sub = extra;
	    SET_VECTOR_ELT(indexnames, i, STRING_ELT(s, i));
	}
	INTEGER(indx)[i] = (int) sub;
    }
    /* We return the new names as the names attribute of the returned
       subscript vector. */
    if (extra != nnames)
	setAttrib(indx, R_UseNamesSymbol, indexnames);
    if (canstretch)
	*stretch = extra;
    UNPROTECT(4);
    return indx;
}

/* Array Subscripts.
    dim is the dimension (0 to k-1)
    s is the subscript list,
    dims is the dimensions of x
    dng is a function (usually getAttrib) that obtains the dimnames
    x is the array to be subscripted.
*/

attribute_hidden SEXP
int_arraySubscript(int dim, SEXP s, SEXP dims, SEXP x, SEXP call)
{
    int nd, ns;
    R_xlen_t stretch = 0;
    SEXP dnames, tmp;
    ns = length(s);
    nd = INTEGER(dims)[dim];

    switch (TYPEOF(s)) {
    case NILSXP:
	return allocVector(INTSXP, 0);
    case LGLSXP:
	return logicalSubscript(s, ns, nd, &stretch, call);
    case INTSXP:
	return integerSubscript(s, ns, nd, &stretch, call);
    case REALSXP:
	/* We don't yet allow subscripts > R_SHORT_LEN_MAX */
	PROTECT(tmp = coerceVector(s, INTSXP));
	tmp = integerSubscript(tmp, ns, nd, &stretch, call);
	UNPROTECT(1);
	return tmp;
    case STRSXP:
	dnames = getAttrib(x, R_DimNamesSymbol);
	if (dnames == R_NilValue) {
	    ECALL(call, _("no 'dimnames' attribute for array"));
	}
	dnames = VECTOR_ELT(dnames, dim);
	return stringSubscript(s, ns, nd, dnames, &stretch, call);
    case SYMSXP:
	if (s == R_MissingArg)
	    return nullSubscript(nd);
    default:
	ECALL3(call, _("invalid subscript type '%s'"), type2char(TYPEOF(s)));
    }
    return R_NilValue;
}

/* This is used by packages arules, cba, proxy and seriation. */
typedef SEXP AttrGetter(SEXP x, SEXP data);
typedef SEXP (*StringEltGetter)(SEXP x, int i);

SEXP
arraySubscript(int dim, SEXP s, SEXP dims, AttrGetter dng,
	       StringEltGetter strg, SEXP x)
{
    return int_arraySubscript(dim, s, dims, x, R_NilValue);
}

/* Subscript creation.  The first thing we do is check to see */
/* if there are any user supplied NULL's, these result in */
/* returning a vector of length 0. */
/* if stretch is zero on entry then the vector x cannot be
   "stretched",
   otherwise, stretch returns the new required length for x
*/

SEXP attribute_hidden
makeSubscript(SEXP x, SEXP s, R_xlen_t *stretch, SEXP call)
{
    if (! (isVector(x) || isList(x) || isLanguage(x))) {
	ECALL(call, _("subscripting on non-vector"));
    }

    R_xlen_t nx = xlength(x);
    R_xlen_t ns = xlength(s);

    /* special case for simple indices -- does not duplicate */
    if (ns == 1) {
	if (TYPEOF(s) == INTSXP) {
	    int i = INTEGER(s)[0];
	    if (0 < i && i <= nx) {
		*stretch = 0;
		return s;
	    }
	}
	else if (TYPEOF(s) == REALSXP) {
	    double di = REAL(s)[0];
	    if (1 <= di && di <= nx) {
		*stretch = 0;
		/* We could only return a REALSXP if the value is too
		   large for an INTSXP, but, as the calling code can
		   handle REALSXP indices, returning the REALSXP
		   avoids and allocation. */
		return s;
	    }
	}
    }

    SEXP ans = R_NilValue;
    switch (TYPEOF(s)) {
    case NILSXP:
	*stretch = 0;
	ans = allocVector(INTSXP, 0);
	break;
    case LGLSXP:
	ans = logicalSubscript(s, ns, nx, stretch, call);
	break;
    case INTSXP:
	PROTECT(s = duplicate(s));
	SET_ATTRIB(s, R_NilValue);
	SET_OBJECT(s, 0);
	ans = integerSubscript(s, ns, nx, stretch, call);
	UNPROTECT(1);
	break;
    case REALSXP:
	ans = realSubscript(s, ns, nx, stretch, call);
	break;
    case STRSXP:
    {
	PROTECT(s = duplicate(s));
	SET_ATTRIB(s, R_NilValue);
	SET_OBJECT(s, 0);
	SEXP names = getAttrib(x, R_NamesSymbol);
	/* *stretch = 0; */
	ans = stringSubscript(s, ns, nx, names, stretch, call);
	UNPROTECT(1);
	break;
    }
    case SYMSXP:
	*stretch = 0;
	if (s == R_MissingArg) {
	    ans = nullSubscript(nx);
	    break;
	}
    default:
	ECALL3(call, _("invalid subscript type '%s'"), type2char(TYPEOF(s)));
    }
    return ans;
}
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 1995, 1996  Robert Gentleman and Ross Ihaka
 *  Copyright (C) 1997--2016  The R Core Team
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <Defn.h>
#include <Internal.h>
#include <R_ext/Itermacros.h>

#include <float.h> // for DBL_MAX

#include "duplicate.h"

#define R_MSG_type	_("invalid 'type' (%s) of argument")
#define imax2(x, y) ((x < y) ? y : x)

#define R_INT_MIN	(1+INT_MIN)
	/* since INT_MIN is the NA_INTEGER value ! */
#define Int2Real(i)	((i == NA_INTEGER) ? NA_REAL : (double)i)

#ifdef DEBUG_sum
#define DbgP1(s) REprintf(s)
#define DbgP2(s,a) REprintf(s,a)
#define DbgP3(s,a,b) REprintf(s,a,b)
#else
#define DbgP1(s)
#define DbgP2(s,a)
#define DbgP3(s,a,b)
#endif

#ifdef LONG_INT
static Rboolean isum(int *x, R_xlen_t n, int *value, Rboolean narm, SEXP call)
{
    LONG_INT s = 0;  // at least 64-bit
    Rboolean updated = FALSE;
#ifdef LONG_VECTOR_SUPPORT
    int ii = R_INT_MIN; // need > 2^32 entries to overflow.
#endif

    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] != NA_INTEGER) {
	    if(!updated) updated = TRUE;
	    s += x[i];
#ifdef LONG_VECTOR_SUPPORT
	    if (ii++ > 1000) {
		ii = 0;
		if (s > 9000000000000000L || s < -9000000000000000L) {
		    if(!updated) updated = TRUE;
		    *value = NA_INTEGER;
		    warningcall(call, _("integer overflow - use sum(as.numeric(.))"));
		    return updated;
		}
	    }
#endif
	} else if (!narm) {
	    if(!updated) updated = TRUE;
	    *value = NA_INTEGER;
	    return updated;
	}
    }
    if(s > INT_MAX || s < R_INT_MIN){
	warningcall(call, _("integer overflow - use sum(as.numeric(.))"));
	*value = NA_INTEGER;
    }
    else *value = (int) s;

    return updated;
}
#else
/* Version from R 3.0.0: should never be used with a C99/C11 compiler */
static Rboolean isum(int *x, R_xlen_t n, int *value, Rboolean narm, SEXP call)
{
    double s = 0.0;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] != NA_INTEGER) {
	    if(!updated) updated = TRUE;
	    s += x[i];
	} else if (!narm) {
	    if(!updated) updated = TRUE;
	    *value = NA_INTEGER;
	    return updated;
	}
    }
    if(s > INT_MAX || s < R_INT_MIN){
	warningcall(call, _("integer overflow - use sum(as.numeric(.))"));
	*value = NA_INTEGER;
    }
    else *value = (int) s;

    return updated;
}
#endif

static Rboolean rsum(double *x, R_xlen_t n, double *value, Rboolean narm)
{
    LDOUBLE s = 0.0;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (!narm || !ISNAN(x[i])) {
	    if(!updated) updated = TRUE;
	    s += x[i];
	}
    }
    if(s > DBL_MAX) *value = R_PosInf;
    else if (s < -DBL_MAX) *value = R_NegInf;
    else *value = (double) s;

    return updated;
}

static Rboolean csum(Rcomplex *x, R_xlen_t n, Rcomplex *value, Rboolean narm)
{
    LDOUBLE sr = 0.0, si = 0.0;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (!narm || (!ISNAN(x[i].r) && !ISNAN(x[i].i))) {
	    if(!updated) updated = TRUE;
	    sr += x[i].r;
	    si += x[i].i;
	}
    }
    value->r = (double) sr;
    value->i = (double) si;

    return updated;
}

static Rboolean imin(int *x, R_xlen_t n, int *value, Rboolean narm)
{
    int s = 0 /* -Wall */;
    Rboolean updated = FALSE;

    /* Used to set s = INT_MAX, but this ignored INT_MAX in the input */
    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] != NA_INTEGER) {
	    if (!updated || s > x[i]) {
		s = x[i];
		if(!updated) updated = TRUE;
	    }
	}
	else if (!narm) {
	    *value = NA_INTEGER;
	    return(TRUE);
	}
    }
    *value = s;

    return updated;
}

static Rboolean rmin(double *x, R_xlen_t n, double *value, Rboolean narm)
{
    double s = 0.0; /* -Wall */
    Rboolean updated = FALSE;

    /* s = R_PosInf; */
    for (R_xlen_t i = 0; i < n; i++) {
	if (ISNAN(x[i])) {/* Na(N) */
	    if (!narm) {
		if(!ISNA(s)) s = x[i]; /* so any NA trumps all NaNs */
		if(!updated) updated = TRUE;
	    }
	}
	else if (!updated || x[i] < s) {  /* Never true if s is NA/NaN */
	    s = x[i];
	    if(!updated) updated = TRUE;
	}
    }
    *value = s;

    return updated;
}

static Rboolean smin(SEXP x, SEXP *value, Rboolean narm)
{
    SEXP s = NA_STRING; /* -Wall */
    Rboolean updated = FALSE;
    const void *vmax = vmaxget(); // precautionary for Scollate

    for (R_xlen_t i = 0; i < XLENGTH(x); i++) {
	if (STRING_ELT(x, i) != NA_STRING) {
	    if (!updated ||
		(s != STRING_ELT(x, i) && Scollate(s, STRING_ELT(x, i)) > 0)) {
		s = STRING_ELT(x, i);
		if(!updated) updated = TRUE;
	    }
	}
	else if (!narm) {
	    *value = NA_STRING;
	    return(TRUE);
	}
    }
    *value = s;

    vmaxset(vmax);
    return updated;
}

static Rboolean imax(int *x, R_xlen_t n, int *value, Rboolean narm)
{
    int s = 0 /* -Wall */;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] != NA_INTEGER) {
	    if (!updated || s < x[i]) {
		s = x[i];
		if(!updated) updated = TRUE;
	    }
	} else if (!narm) {
	    *value = NA_INTEGER;
	    return(TRUE);
	}
    }
    *value = s;

    return updated;
}

static Rboolean rmax(double *x, R_xlen_t n, double *value, Rboolean narm)
{
    double s = 0.0 /* -Wall */;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (ISNAN(x[i])) {/* Na(N) */
	    if (!narm) {
		if(!ISNA(s)) s = x[i]; /* so any NA trumps all NaNs */
		if(!updated) updated = TRUE;
	    }
	}
	else if (!updated || x[i] > s) {  /* Never true if s is NA/NaN */
	    s = x[i];
	    if(!updated) updated = TRUE;
	}
    }
    *value = s;

    return updated;
}

static Rboolean smax(SEXP x, SEXP *value, Rboolean narm)
{
    SEXP s = NA_STRING; /* -Wall */
    Rboolean updated = FALSE;
    const void *vmax = vmaxget(); // precautionary for Scollate

    for (R_xlen_t i = 0; i < XLENGTH(x); i++) {
	if (STRING_ELT(x, i) != NA_STRING) {
	    if (!updated ||
		(s != STRING_ELT(x, i) && Scollate(s, STRING_ELT(x, i)) < 0)) {
		s = STRING_ELT(x, i);
		if(!updated) updated = TRUE;
	    }
	}
	else if (!narm) {
	    *value = NA_STRING;
	    return(TRUE);
	}
    }
    *value = s;

    vmaxset(vmax);
    return updated;
}

static Rboolean iprod(int *x, R_xlen_t n, double *value, Rboolean narm)
{
    LDOUBLE s = 1.0;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] != NA_INTEGER) {
	    s *= x[i];
	    if(!updated) updated = TRUE;
	}
	else if (!narm) {
	    if(!updated) updated = TRUE;
	    *value = NA_REAL;
	    return updated;
	}

	if(ISNAN(s)) {  /* how can this happen? */
	    *value = NA_REAL;
	    return updated;
	}
    }
    // This could over/underflow (does in package POT)
    if(s > DBL_MAX) *value = R_PosInf;
    else if (s < -DBL_MAX) *value = R_NegInf;
    else *value = (double) s;

    return updated;
}

static Rboolean rprod(double *x, R_xlen_t n, double *value, Rboolean narm)
{
    LDOUBLE s = 1.0;
    Rboolean updated = FALSE;

    for (R_xlen_t i = 0; i < n; i++) {
	if (!narm || !ISNAN(x[i])) {
	    if(!updated) updated = TRUE;
	    s *= x[i];
	}
    }
    if(s > DBL_MAX) *value = R_PosInf;
    else if (s < -DBL_MAX) *value = R_NegInf;
    else *value = (double) s;

    return updated;
}

static Rboolean cprod(Rcomplex *x, R_xlen_t n, Rcomplex *value, Rboolean narm)
{
    LDOUBLE sr = 1.0, si = 0.0;
    Rboolean updated = FALSE;
    for (R_xlen_t i = 0; i < n; i++) {
	if (!narm || (!ISNAN(x[i].r) && !ISNAN(x[i].i))) {
	    if(!updated) updated = TRUE;
	    LDOUBLE tr = sr, ti = si;
	    sr = tr * x[i].r - ti * x[i].i;
	    si = tr * x[i].i + ti * x[i].r;
	}
    }
    value->r = (double) sr;
    value->i = (double) si;

    return updated;
}


attribute_hidden
SEXP fixup_NaRm(SEXP args)
{
    SEXP t, na_value;

    /* Need to make sure na.rm is last and exists */
    na_value = ScalarLogical(FALSE);
    for(SEXP a = args, prev = R_NilValue; a != R_NilValue; a = CDR(a)) {
	if(TAG(a) == R_NaRmSymbol) {
	    if(CDR(a) == R_NilValue) return args;
	    na_value = CAR(a);
	    if(prev == R_NilValue) args = CDR(a);
	    else SETCDR(prev, CDR(a));
	}
	prev = a;
    }

    PROTECT(na_value);
    t = CONS(na_value, R_NilValue);
    UNPROTECT(1);
    PROTECT(t);
    SET_TAG(t, R_NaRmSymbol);
    if (args == R_NilValue)
	args = t;
    else {
	SEXP r = args;
	while (CDR(r) != R_NilValue) r = CDR(r);
	SETCDR(r, t);
    }
    UNPROTECT(1);
    return args;
}

/* do_summary provides a variety of data summaries
	op : 0 = sum, 1 = mean, 2 = min, 3 = max, 4 = prod
 */
/* NOTE: mean() is rather different as only one arg and no na.rm, and
 * dispatch is from an R-level generic, this being a special case of
 * mean.default.
 */

SEXP attribute_hidden do_summary(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, a, stmp = NA_STRING /* -Wall */, scum = NA_STRING, call2;
    double tmp = 0.0, s;
    Rcomplex z, ztmp, zcum={0.0, 0.0} /* -Wall */;
    int itmp = 0, icum = 0, int_a, real_a, empty, warn = 0 /* dummy */;
    SEXPTYPE ans_type;/* only INTEGER, REAL, COMPLEX or STRSXP here */

    Rboolean narm;
    int updated;
	/* updated := 1 , as soon as (i)tmp (do_summary),
	   or *value ([ir]min / max) is assigned */

    checkArity(op, args);
    if(PRIMVAL(op) == 1) { /* mean */
	LDOUBLE s = 0., si = 0., t = 0., ti = 0.;
	R_xlen_t i, n = XLENGTH(CAR(args));
	SEXP x = CAR(args);
	switch(TYPEOF(x)) {
	case LGLSXP:
	case INTSXP:
	    PROTECT(ans = allocVector(REALSXP, 1));
	    for (i = 0; i < n; i++) {
		if(INTEGER(x)[i] == NA_INTEGER) {
		    REAL(ans)[0] = R_NaReal;
		    UNPROTECT(1); /* ans */
		    return ans;
		}
		s += INTEGER(x)[i];
	    }
	    REAL(ans)[0] = (double) (s/n);
	    break;
	case REALSXP:
	    PROTECT(ans = allocVector(REALSXP, 1));
	    for (i = 0; i < n; i++) s += REAL(x)[i];
	    s /= n;
	    if(R_FINITE((double)s)) {
		for (i = 0; i < n; i++) t += (REAL(x)[i] - s);
		s += t/n;
	    }
	    REAL(ans)[0] = (double) s;
	    break;
	case CPLXSXP:
	    PROTECT(ans = allocVector(CPLXSXP, 1));
	    for (i = 0; i < n; i++) {
		s += COMPLEX(x)[i].r;
		si += COMPLEX(x)[i].i;
	    }
	    s /= n; si /= n;
	    if( R_FINITE((double)s) && R_FINITE((double)si) ) {
		for (i = 0; i < n; i++) {
		    t += COMPLEX(x)[i].r - s;
		    ti += COMPLEX(x)[i].i - si;
		}
		s += t/n; si += ti/n;
	    }
	    COMPLEX(ans)[0].r = (double) s;
	    COMPLEX(ans)[0].i = (double) si;
	    break;
	default:
	    error(R_MSG_type, type2char(TYPEOF(x)));
	    ans = R_NilValue; // -Wall on clang 4.2
	}
	UNPROTECT(1); /* ans */
	return ans;
    }

    /* match to foo(..., na.rm=FALSE) */
    PROTECT(args = fixup_NaRm(args));
    PROTECT(call2 = shallow_duplicate(call));
    SETCDR(call2, args);

    if (DispatchGroup("Summary", call2, op, args, env, &ans)) {
	UNPROTECT(2); /* call2, args */
	return(ans);
    }
    UNPROTECT(1); /* call2 */

#ifdef DEBUG_Summary
    REprintf("C do_summary(op%s, *): did NOT dispatch\n", PRIMNAME(op));
#endif

    ans = matchArgExact(R_NaRmSymbol, &args);
    narm = asLogical(ans);
    updated = 0;
    empty = 1;/*- =1: only zero-length arguments, or NA with na.rm=T */

    int iop = PRIMVAL(op);
    switch(iop) {
    case 0:/* sum */
    /* we need to find out if _all_ the arguments are integer or logical
       in advance, as we might overflow before we find out.  NULL is
       documented to be the same as integer(0).
    */
	a = args;
	int_a = 1;
	while (a != R_NilValue) {
	    if(!isInteger(CAR(a)) &&  !isLogical(CAR(a)) && !isNull(CAR(a))) {
		int_a = 0;
		break;
	    }
	    a = CDR(a);
	}
	ans_type = int_a ? INTSXP: REALSXP; /* try to keep if possible.. */
	zcum.r = zcum.i = 0.; icum = 0;
	break;

    case 2:/* min */
	DbgP2("do_summary: min(.. na.rm=%d) ", narm);
	ans_type = INTSXP;
	zcum.r = R_PosInf;
	icum = INT_MAX;
	break;

    case 3:/* max */
	DbgP2("do_summary: max(.. na.rm=%d) ", narm);
	ans_type = INTSXP;
	zcum.r = R_NegInf;;
	icum = R_INT_MIN;
	break;

    case 4:/* prod */
	ans_type = REALSXP;
	zcum.r = 1.;
	zcum.i = 0.;
	break;

    default:
	errorcall(call,
		  _("internal error ('op = %d' in do_summary).\t Call a Guru"),
		  iop);
	return R_NilValue;/*-Wall */
    }

    /*-- now loop over all arguments.  Do the 'op' switch INSIDE : */
    PROTECT(scum);
    while (args != R_NilValue) {
	a = CAR(args);
	int_a = 0;/* int_a = 1	<-->	a is INTEGER */
	real_a = 0;

	if(xlength(a) > 0) {
	    updated = 0;/*- GLOBAL -*/

	    switch(iop) {
	    case 2:/* min */
	    case 3:/* max */

		switch(TYPEOF(a)) {
		case LGLSXP:
		case INTSXP:
		    int_a = 1;
		    if (iop == 2) updated = imin(INTEGER(a), XLENGTH(a), &itmp, narm);
		    else	  updated = imax(INTEGER(a), XLENGTH(a), &itmp, narm);
		    break;
		case REALSXP:
		    real_a = 1;
		    if(ans_type == INTSXP) {/* change to REAL */
			ans_type = REALSXP;
			if(!empty) zcum.r = Int2Real(icum);
		    }
		    if (iop == 2) updated = rmin(REAL(a), XLENGTH(a), &tmp, narm);
		    else	  updated = rmax(REAL(a), XLENGTH(a), &tmp, narm);
		    break;
		case STRSXP:
		    if(!empty && ans_type == INTSXP) {
			scum = StringFromInteger(icum, &warn);
			UNPROTECT(1); /* scum */
			PROTECT(scum);
		    } else if(!empty && ans_type == REALSXP) {
			scum = StringFromReal(zcum.r, &warn);
			UNPROTECT(1); /* scum */
			PROTECT(scum);
		    }
		    ans_type = STRSXP;
		    if (iop == 2) updated = smin(a, &stmp, narm);
		    else updated = smax(a, &stmp, narm);
		    break;
		default:
		    goto invalid_type;
		}

		if(updated) {/* 'a' had non-NA elements; --> "add" tmp or itmp*/
		    DbgP1(" updated:");
		    if(ans_type == INTSXP) {
			DbgP3(" INT: (old)icum= %ld, itmp=%ld\n", icum,itmp);
			if (icum == NA_INTEGER); /* NA trumps anything */
			else if (itmp == NA_INTEGER ||
			    (iop == 2 && itmp < icum) || /* min */
			    (iop == 3 && itmp > icum))   /* max */
			    icum = itmp;
		    } else if(ans_type == REALSXP) {
			if (int_a) tmp = Int2Real(itmp);
			DbgP3(" REAL: (old)cum= %g, tmp=%g\n", zcum.r,tmp);
			if (ISNA(zcum.r)); /* NA trumps anything */
			else if (ISNAN(tmp)) {
			    if (ISNA(tmp)) zcum.r = tmp;
			    else zcum.r += tmp;/* NA or NaN */
			} else if(
			    (iop == 2 && tmp < zcum.r) ||
			    (iop == 3 && tmp > zcum.r))	zcum.r = tmp;
		    } else if(ans_type == STRSXP) {
			if(int_a)
			   stmp = StringFromInteger(itmp, &warn);
			else if(real_a)
			   stmp = StringFromReal(tmp, &warn);

			if(empty)
			    scum = stmp;
			else if (scum != NA_STRING) {
			    PROTECT(stmp);
			    if(stmp == NA_STRING ||
			       (iop == 2 && stmp != scum && Scollate(stmp, scum) < 0) ||
			       (iop == 3 && stmp != scum && Scollate(stmp, scum) > 0) )
				scum = stmp;
			    UNPROTECT(1); /* stmp */
			}
			UNPROTECT(1); /* scum */
			PROTECT(scum);
		    }
		}/*updated*/ else {
		    /*-- in what cases does this happen here at all?
		      -- if there are no non-missing elements.
		     */
		    DbgP2(" NOT updated [!! RARE !!]: int_a=%d\n", int_a);
		}

		break;/*--- end of  min() / max() ---*/

	    case 0:/* sum */

		switch(TYPEOF(a)) {
		case LGLSXP:
		case INTSXP:
		    updated = isum(TYPEOF(a) == LGLSXP ?
				   LOGICAL(a) :INTEGER(a), XLENGTH(a),
				   &itmp, narm, call);
		    if(updated) {
			if(itmp == NA_INTEGER) goto na_answer;
			if(ans_type == INTSXP) {
			    s = (double) icum + (double) itmp;
			    if(s > INT_MAX || s < R_INT_MIN){
				warningcall(call,_("Integer overflow - use sum(as.numeric(.))"));
				goto na_answer;
			    }
			    else icum += itmp;
			} else
			    zcum.r += Int2Real(itmp);
		    }
		    break;
		case REALSXP:
		    if(ans_type == INTSXP) {
			ans_type = REALSXP;
			if(!empty) zcum.r = Int2Real(icum);
		    }
		    updated = rsum(REAL(a), XLENGTH(a), &tmp, narm);
		    if(updated) {
			zcum.r += tmp;
		    }
		    break;
		case CPLXSXP:
		    if(ans_type == INTSXP) {
			ans_type = CPLXSXP;
			if(!empty) zcum.r = Int2Real(icum);
		    } else if (ans_type == REALSXP)
			ans_type = CPLXSXP;
		    updated = csum(COMPLEX(a), XLENGTH(a), &ztmp, narm);
		    if(updated) {
			zcum.r += ztmp.r;
			zcum.i += ztmp.i;
		    }
		    break;
		default:
		    goto invalid_type;
		}

		break;/* sum() part */

	    case 4:/* prod */

		switch(TYPEOF(a)) {
		case LGLSXP:
		case INTSXP:
		case REALSXP:
		    if(TYPEOF(a) == REALSXP)
			updated = rprod(REAL(a), XLENGTH(a), &tmp, narm);
		    else
			updated = iprod(INTEGER(a), XLENGTH(a), &tmp, narm);
		    if(updated) {
			zcum.r *= tmp;
			zcum.i *= tmp;
		    }
		    break;
		case CPLXSXP:
		    ans_type = CPLXSXP;
		    updated = cprod(COMPLEX(a), XLENGTH(a), &ztmp, narm);
		    if(updated) {
			z.r = zcum.r;
			z.i = zcum.i;
			zcum.r = z.r * ztmp.r - z.i * ztmp.i;
			zcum.i = z.r * ztmp.i + z.i * ztmp.r;
		    }
		    break;
		default:
		    goto invalid_type;
		}

		break;/* prod() part */

	    } /* switch(iop) */

	} else { /* len(a)=0 */
	    /* Even though this has length zero it can still be invalid,
	       e.g. list() or raw() */
	    switch(TYPEOF(a)) {
	    case LGLSXP:
	    case INTSXP:
	    case REALSXP:
	    case NILSXP:  /* OK historically, e.g. PR#1283 */
		break;
	    case CPLXSXP:
		if (iop == 2 || iop == 3) goto invalid_type;
		break;
	    case STRSXP:
		if (iop == 2 || iop == 3) {
		    if(!empty && ans_type == INTSXP) {
			scum = StringFromInteger(icum, &warn);
			UNPROTECT(1); /* scum */
			PROTECT(scum);
		    } else if(!empty && ans_type == REALSXP) {
			scum = StringFromReal(zcum.r, &warn);
			UNPROTECT(1); /* scum */
			PROTECT(scum);
		    }
		    ans_type = STRSXP;
		    break;
		}
	    default:
		goto invalid_type;
	    }
	    if(ans_type < TYPEOF(a) && ans_type != CPLXSXP) {
		if(!empty && ans_type == INTSXP)
		    zcum.r = Int2Real(icum);
		ans_type = TYPEOF(a);
	    }
	}
	DbgP3(" .. upd.=%d, empty: old=%d", updated, empty);
	if(empty && updated) empty=0;
	DbgP2(", new=%d\n", empty);
	args = CDR(args);
    } /*-- while(..) loop over args */

    /*-------------------------------------------------------*/
    if(empty && (iop == 2 || iop == 3)) {
	if(ans_type == STRSXP) {
	    warningcall(call, _("no non-missing arguments, returning NA"));
	} else {
	    if(iop == 2)
		warningcall(call, _("no non-missing arguments to min; returning Inf"));
	    else
		warningcall(call, _("no non-missing arguments to max; returning -Inf"));
	    ans_type = REALSXP;
	}
    }

    ans = allocVector(ans_type, 1);
    switch(ans_type) {
    case INTSXP:   INTEGER(ans)[0] = icum;break;
    case REALSXP:  REAL(ans)[0] = zcum.r; break;
    case CPLXSXP:  COMPLEX(ans)[0].r = zcum.r; COMPLEX(ans)[0].i = zcum.i;break;
    case STRSXP:   SET_STRING_ELT(ans, 0, scum); break;
    }
    UNPROTECT(2); /* scum, args */
    return ans;

na_answer: /* only sum(INTSXP, ...) case currently used */
    ans = allocVector(ans_type, 1);
    switch(ans_type) {
    case INTSXP:	INTEGER(ans)[0] = NA_INTEGER; break;
    case REALSXP:	REAL(ans)[0] = NA_REAL; break;
    case CPLXSXP:	COMPLEX(ans)[0].r = COMPLEX(ans)[0].i = NA_REAL; break;
    case STRSXP:        SET_STRING_ELT(ans, 0, NA_STRING); break;
    }
    UNPROTECT(2); /* scum, args */
    return ans;

invalid_type:
    errorcall(call, R_MSG_type, type2char(TYPEOF(a)));
    return R_NilValue;
}/* do_summary */


SEXP attribute_hidden do_range(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, a, b, prargs, call2;

    PROTECT(args = fixup_NaRm(args));
    PROTECT(call2 = shallow_duplicate(call));
    SETCDR(call2, args);

    if (DispatchGroup("Summary", call2, op, args, env, &ans)) {
	UNPROTECT(2);
	return(ans);
    }
    UNPROTECT(1);

    PROTECT(op = findFun(install("range.default"), env));
    PROTECT(prargs = promiseArgs(args, R_GlobalEnv));
    for (a = args, b = prargs; a != R_NilValue; a = CDR(a), b = CDR(b))
	SET_PRVALUE(CAR(b), CAR(a));
    ans = applyClosure(call, op, prargs, env, R_NilValue);
    UNPROTECT(3);
    return(ans);
}

// which.min(x) : The index (starting at 1), of the first min(x) in x
// which.max(x) : The index (starting at 1), of the first max(x) in x
SEXP attribute_hidden do_first_min(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    SEXP sx = CAR(args), ans;
    int nprot = 1;
    R_xlen_t i, n, indx = -1;

    checkArity(op, args);
    if (!isNumeric(sx)) {
	PROTECT(sx = coerceVector(CAR(args), REALSXP)); nprot++;
    }
    n = XLENGTH(sx);
    switch(TYPEOF(sx)) {
    case LGLSXP: // with only (TRUE, FALSE, NA) -- may be fast
    {
	int *r = LOGICAL(sx);
	if(PRIMVAL(op) == 0) { /* which.min */
	    for (i = 0; i < n; i++)
		if (r[i] == FALSE) {
		    indx = i; break; // found FALSE: done
		} else if (indx == -1 && r[i] != NA_LOGICAL) {
		    indx = i; // first TRUE
		}
	} else { /* which.max */
	    for (i = 0; i < n; i++)
		if (r[i] == TRUE) {
		    indx = i; break; // found TRUE: done
		} else if (indx == -1 && r[i] != NA_LOGICAL) {
		    indx = i; // first FALSE
		}
	}
    }
    break;

    case INTSXP:
    {
	int s, *r = INTEGER(sx);
	if(PRIMVAL(op) == 0) { /* which.min */
	    s = INT_MAX;
	    for (i = 0; i < n; i++)
		if (r[i] != NA_INTEGER && (r[i] < s || indx == -1)) {
		    s = r[i]; indx = i;
		}
	} else { /* which.max */
	    s = INT_MIN;
	    for (i = 0; i < n; i++)
		if (r[i] != NA_INTEGER && (r[i] > s || indx == -1)) {
		    s = r[i]; indx = i;
		}
	}
    }
    break;

    case REALSXP:
    {
	double s, *r = REAL(sx);
	if(PRIMVAL(op) == 0) { /* which.min */
	    s = R_PosInf;
	    for (i = 0; i < n; i++)
		if ( !ISNAN(r[i]) && (r[i] < s || indx == -1) ) {
		    s = r[i]; indx = i;
		}
	} else { /* which.max */
	    s = R_NegInf;
	    for (i = 0; i < n; i++)
		if ( !ISNAN(r[i]) && (r[i] > s || indx == -1) ) {
		    s = r[i]; indx = i;
		}
	}
    }
    } // switch()


    i = (indx != -1);
    Rboolean large = (indx + 1) > INT_MAX;
    PROTECT(ans = allocVector(large ? REALSXP : INTSXP, i ? 1 : 0));
    if (i) {
	if(large)
	    REAL(ans)[0] = (double)indx + 1;
	else
	    INTEGER(ans)[0] = (int)indx + 1;
	if (getAttrib(sx, R_NamesSymbol) != R_NilValue) { /* preserve names */
	    SEXP ansnam;
	    PROTECT(ansnam =
		    ScalarString(STRING_ELT(getAttrib(sx, R_NamesSymbol), indx)));
	    setAttrib(ans, R_NamesSymbol, ansnam);
	    UNPROTECT(1);
	}
    }
    UNPROTECT(nprot);
    return ans;
}


/* which(x) : indices of non-NA TRUE values in x */
SEXP attribute_hidden do_which(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    SEXP v, v_nms, ans, ans_nms = R_NilValue;
    int i, j = 0, len, *buf;

    checkArity(op, args);
    v = CAR(args);
    if (!isLogical(v))
	error(_("argument to 'which' is not logical"));
    len = length(v);
    buf = (int *) R_alloc(len, sizeof(int));

    for (i = 0; i < len; i++) {
	if (LOGICAL(v)[i] == TRUE) {
	    buf[j] = i + 1;
	    j++;
	}
    }

    len = j;
    PROTECT(ans = allocVector(INTSXP, len));
    if(len) memcpy(INTEGER(ans), buf, sizeof(int) * len);

    if ((v_nms = getAttrib(v, R_NamesSymbol)) != R_NilValue) {
	PROTECT(ans_nms = allocVector(STRSXP, len));
	for (i = 0; i < len; i++) {
	    SET_STRING_ELT(ans_nms, i,
			   STRING_ELT(v_nms, INTEGER(ans)[i] - 1));
	}
	setAttrib(ans, R_NamesSymbol, ans_nms);
	UNPROTECT(1);
    }
    UNPROTECT(1);
    return ans;
}


/* op = 0 is pmin, op = 1 is pmax
   NULL and logicals are handled as if they had been coerced to integer.
 */
SEXP attribute_hidden do_pmin(SEXP call, SEXP op, SEXP args, SEXP rho)
{
    SEXP a, x, ans;
    int narm;
    R_xlen_t i, n, len, i1;
    SEXPTYPE type, anstype;

    narm = asLogical(CAR(args));
    if(narm == NA_LOGICAL)
	error(_("invalid '%s' value"), "na.rm");
    args = CDR(args);
    x = CAR(args);
    if(args == R_NilValue) error(_("no arguments"));

    anstype = TYPEOF(x);
    switch(anstype) {
    case NILSXP:
    case LGLSXP:
    case INTSXP:
    case REALSXP:
    case STRSXP:
	break;
    default:
	error(_("invalid input type"));
    }
    a = CDR(args);
    if(a == R_NilValue) return x; /* one input */

    len = xlength(x); /* not LENGTH, as NULL is allowed */
    for(; a != R_NilValue; a = CDR(a)) {
	x = CAR(a);
	type = TYPEOF(x);
	switch(type) {
	case NILSXP:
	case LGLSXP:
	case INTSXP:
	case REALSXP:
	case STRSXP:
	    break;
	default:
	    error(_("invalid input type"));
	}
	if(type > anstype) anstype = type;
	n = xlength(x);
	if ((len > 0) ^ (n > 0)) {
	    // till 2.15.0:  error(_("cannot mix 0-length vectors with others"));
	    len = 0;
	    break;
	}
	len = imax2(len, n);
    }
    if(anstype < INTSXP) anstype = INTSXP;
    if(len == 0) return allocVector(anstype, 0);
    /* Check for fractional recycling (added in 2.14.0) */
    for(a = args; a != R_NilValue; a = CDR(a)) {
	n = length(CAR(a));
	if (len % n) {
	    warning(_("an argument will be fractionally recycled"));
	    break;
	}
    }

    PROTECT(ans = allocVector(anstype, len));
    switch(anstype) {
    case INTSXP:
    {
	int *r,  *ra = INTEGER(ans), tmp;
	PROTECT(x = coerceVector(CAR(args), anstype));
	r = INTEGER(x);
	n = XLENGTH(x);
	xcopyIntegerWithRecycle(ra, r, 0, len, n);
	UNPROTECT(1);
	for(a = CDR(args); a != R_NilValue; a = CDR(a)) {
	    x = CAR(a);
	    PROTECT(x = coerceVector(CAR(a), anstype));
	    n = XLENGTH(x);
	    r = INTEGER(x);
	    MOD_ITERATE1(len, n, i, i1, {
		tmp = r[i1];
		if(PRIMVAL(op) == 1) {
		    if( (narm && ra[i] == NA_INTEGER) ||
			(ra[i] != NA_INTEGER && tmp != NA_INTEGER
			 && tmp > ra[i]) ||
			(!narm && tmp == NA_INTEGER) )
			ra[i] = tmp;
		} else {
		    if( (narm && ra[i] == NA_INTEGER) ||
			(ra[i] != NA_INTEGER && tmp != NA_INTEGER
			 && tmp < ra[i]) ||
			(!narm && tmp == NA_INTEGER) )
			ra[i] = tmp;
		}
	    });
	    UNPROTECT(1);
	}
    }
	break;
    case REALSXP:
    {
	double *r, *ra = REAL(ans), tmp;
	PROTECT(x = coerceVector(CAR(args), anstype));
	r = REAL(x);
	n = XLENGTH(x);
	xcopyRealWithRecycle(ra, r, 0, len, n);
	UNPROTECT(1);
	for(a = CDR(args); a != R_NilValue; a = CDR(a)) {
	    PROTECT(x = coerceVector(CAR(a), anstype));
	    n = XLENGTH(x);
	    r = REAL(x);
	    MOD_ITERATE1(len, n, i, i1, {
		tmp = r[i1];
		if(PRIMVAL(op) == 1) {
		    if( (narm && ISNAN(ra[i])) ||
			(!ISNAN(ra[i]) && !ISNAN(tmp) && tmp > ra[i]) ||
			(!narm && ISNAN(tmp)) )
			ra[i] = tmp;
		} else {
		    if( (narm && ISNAN(ra[i])) ||
			(!ISNAN(ra[i]) && !ISNAN(tmp) && tmp < ra[i]) ||
			(!narm && ISNAN(tmp)) )
			ra[i] = tmp;
		}
	    });
	    UNPROTECT(1);
	}
    }
	break;
    case STRSXP:
    {
	PROTECT(x = coerceVector(CAR(args), anstype));
	n = XLENGTH(x);
	xcopyStringWithRecycle(ans, x, 0, len, n);
	UNPROTECT(1);
	for(a = CDR(args); a != R_NilValue; a = CDR(a)) {
	    SEXP tmp, t2;
	    PROTECT(x = coerceVector(CAR(a), anstype));
	    n = XLENGTH(x);
	    MOD_ITERATE1(len, n, i, i1, {
		tmp = STRING_ELT(x, i1);
		t2 = STRING_ELT(ans, i);
		if(PRIMVAL(op) == 1) {
		    if( (narm && t2 == NA_STRING) ||
			(t2 != NA_STRING && tmp != NA_STRING && tmp != t2 && Scollate(tmp, t2) > 0) ||
			(!narm && tmp == NA_STRING) )
			SET_STRING_ELT(ans, i, tmp);
		} else {
		    if( (narm && t2 == NA_STRING) ||
			(t2 != NA_STRING && tmp != NA_STRING && tmp != t2 && Scollate(tmp, t2) < 0) ||
			(!narm && tmp == NA_STRING) )
			SET_STRING_ELT(ans, i, tmp);
		}
	    });
	    UNPROTECT(1);
	}
    }
	break;
    default:
	break;
    }
    UNPROTECT(1);
    return ans;
}
/* PAUL MURRELL
   This is from the GNU plotutils libplot-2.3 distribution
   All references to HAVE_PROTOS removed
   All references to "plotter" replaced with references to "GEDevDesc"
*/

/* <UTF8-FIXME> This assumes single-byte encoding */

/* _controlify() converts a "label" (i.e. a character string), which may
   contain troff-like escape sequences, into a string of unsigned shorts.
   The possible troff-like escape sequences are listed in g_cntrlify.h.

   This conversion is to facilitate rendering.  _controlify() is called by
   alabel(), and the converted label is rendered by _alabel_standard(),
   _alabel_stroke(), or _alabel_device(), depending on what sort of font is
   currently selected.  See g_alabel.c (_controlify() is called by
   labelwidth() too).

   If the currently selected font is a font with ISO-Latin-1 encoding, the
   valid escape sequences include escape sequences for the non-ASCII
   ISO-Latin-1 characters.  Also allowed are such escape sequences as \f0,
   \f1, \f2, \f3, \f4, etc., which switch among the various fonts in the
   current typeface:

	\f1	Switch to font #1, basic
	\f2	Switch to font #2, italic
	\f3	Switch to font #3, bold
	\f4	Switch to font #4, bold italic
	\f0	Switch to font #0, symbol (including Greek characters)

   \fP switches to the previously used font (there is a depth-1 stack,
   i.e. only one previous font is remembered, as in troff).

   All typefaces include at least two fonts: fonts #0 and #1.  Some may
   include more than the above five.  Each unsigned short in the converted
   string is really an annotated character: the low byte is the character,
   and the high byte is the font number.

   Besides font annotations, the controlified string may include control
   codes (unsigned shorts with particular bit patterns in their high
   bytes), which are produced by the escape sequences:

	\sp  start superscript
	\ep  end superscript

	\sb  start subscript
	\eb  end subscript

	\mk  mark location
	\rt  return to mark
	     [useful e.g. for underlining, and filling square roots]

    There are also control codes for horizontal shifts.  \r1, \r2, \r4,
    \r6, \r8, \r^ will produce control codes that will shift right by 1 em,
    1/2 em, 1/4 em, 1/6 em, 1/8 em, 1/12 em, respectively.  \l1, \l2, \l4,
    \l6, \l8, \l^ are similar.

    The string of unsigned shorts, which is returned, is allocated with
    malloc and may be freed later. */

/* PAUL MURRELL
   sys-defines.h not used
*/
/* #include "sys-defines.h" */

/* PAUL MURRELL
   extern.h renamed g_extern.h
*/
#include "g_extern.h"
#include "g_control.h"
#include "g_cntrlify.h"
#include "g_jis.h"

/* these two array lengths must agree with values in file g_her_glyph.c */
#define NUM_OCCIDENTAL_HERSHEY_GLYPHS 4400
#define NUM_ORIENTAL_HERSHEY_GLYPHS 5500

/* PAUL MURRELL
   Added typeface and fontindex arguments
*/

attribute_hidden
unsigned short * _controlify (pGEDevDesc dd, const unsigned char *src,
			      int typeface, int fontindex)
{
  unsigned short *dest;
  unsigned char c, d;
  unsigned char esc[3];
  int j = 0;
  int raw_fontnum, raw_symbol_fontnum;
  unsigned short fontword, symbol_fontword;

  /* note: string length can grow by a factor of 6, because a single
     printable character can be mapped to a sequence of unsigned shorts, of
     length up to 6 (see comment below) */
  /* PAUL MURRELL
     replace _plot_xmalloc with R_alloc
  */
  dest = (unsigned short *) R_alloc (6 * strlen ((char *)src) + 1,
				     sizeof(unsigned short));

  /* PAUL MURRELL
     only for Hershey fonts so removed switch ...
  */
      raw_fontnum = _hershey_typeface_info[typeface].fonts[fontindex];
      raw_symbol_fontnum = _hershey_typeface_info[typeface].fonts[0];
  /* Of the following two words, `fontword' is updated whenever an escape
     sequence like \f0, \f1, \f2 etc. is seen, since raw_fontnum is itself
     updated.  But `symbol_fontword' is fixed */
      fontword = (unsigned short)(raw_fontnum << FONT_SHIFT);
      symbol_fontword = (unsigned short)(raw_symbol_fontnum << FONT_SHIFT);

  while (*src != (unsigned char)'\0')
    {
      /* If EUC, check first for high bit and process two-byte characters
	 separately.  This approach is awkward (we duplicate a lot of code
	 here, which appears elsewhere below). */

      if ((raw_fontnum == HERSHEY_EUC)
	  && (*src & 0x80) && (*(src + 1) & 0x80))
	{
	  unsigned char jis_row = *src & ~(0x80);
	  unsigned char jis_col = *(src + 1) & ~(0x80);

	  if (GOOD_JIS_INDEX(jis_row, jis_col))
	    {
	      int jis_glyphindex = 256 * jis_row + jis_col;

	      if (jis_glyphindex >= BEGINNING_OF_KANJI)
		/* in Kanji range, so check if we have it */
		{
#ifndef NO_KANJI
		  const struct kanjipair *kanji = _builtin_kanji_glyphs;
		  bool matched = false;

		  while (kanji->jis != 0)
		    {
		      if (jis_glyphindex == kanji->jis)
			{
			  matched = true;
			  break;
			}
		      kanji++;
		    }
		  if (matched)
		    {
		      dest[j++] = (unsigned short)( RAW_ORIENTAL_HERSHEY_GLYPH | (kanji->nelson));
		      src += 2;
		      continue;	/* back to top of while loop */
		    }
		  else		/* a Kanji we don't have */
		    {
		      /* render as standard `undefined character' glyph */
		      dest[j++] = RAW_HERSHEY_GLYPH | UNDE;
		      src += 2;
		      continue;	/* back to top of while loop */
		    }
#endif /* not NO_KANJI */
		}
	      else
		/* not in Kanji range, so look for it in char table */
		{
		  const struct jis_entry *char_mapping = _builtin_jis_chars;
		  bool matched = false;

		  while (char_mapping->jis != 0)
		    {
		      if (jis_glyphindex == char_mapping->jis)
			{
			  matched = true;
			  break;
			}
		      char_mapping++;
		    }
		  if (matched)
		    /* the entry in the character table maps the JIS
		       character to a character (in 0..255 range) in
		       one of the fonts in the master table in g_fontdb.c */
		    {
		      int fontnum = char_mapping->font;
		      unsigned short charnum = char_mapping->charnum;

		      if (charnum & RAW_HERSHEY_GLYPH)
			/* a raw Hershey glyph, not in any font */
			dest[j++] = RAW_HERSHEY_GLYPH | charnum;
		      else
			/* a character in one of the fonts in g_fontdb.c */
			  dest[j++] = (unsigned short)((fontnum << FONT_SHIFT) | charnum);
		      src += 2;
		      continue; /* back to top of while loop */
		    }
		  else	/* a character we don't have */
		    {
		      /* render as standard `undefined character' glyph */
		      dest[j++] = RAW_HERSHEY_GLYPH | UNDE;
		      src += 2;
		      continue;	/* back to top of while loop */
		    }
		}
	    }
	  else
	    /* JIS index is OOB */
	    {
	      src += 2;
	      continue;		/* back to top of while loop */
	    }
	}

      /* if current font is Hershey, first try to match each ligature
	 pattern (no ligatures supported in non-Hershey fonts) */
      if (1) /* _plotter->drawstate->font_type == F_HERSHEY) */
	{
	  int i;
	  bool matched = false;

	  for (i = 0; i < NUM_LIGATURES; i++)
	    if ((_ligature_tbl[i].font == raw_fontnum)
		&& (strncmp ((char *)src, _ligature_tbl[i].from,
			     strlen (_ligature_tbl[i].from)) == 0))
	      {
		matched = true;
		break;
	      }

	  if (matched)
	    {
	      dest[j++] = fontword | (unsigned short)_ligature_tbl[i].byte;
	      src += strlen (_ligature_tbl[i].from);
	      continue;		/* back to top of while loop */
	    }
	}

      c = *(src++);		/* no ligature, so get single new char */
      if (c != (unsigned char)'\\') /* ordinary char, may pass through */
	{
	  /* if current font is an ISO-Latin-1 Hershey font ... */
	    if (1 /* _plotter->drawstate->font_type == F_HERSHEY */
	      && _hershey_font_info[raw_fontnum].iso8859_1)
	    {
	      int i;
	      bool matched = false;

	      /* check if this is a `raised' ISO-Latin-1 character */
	      for (i = 0; i < NUM_RAISED_CHARS; i++)
		if (c == _raised_char_tbl[i].from)
		  {
		    matched = true;
		    break;
		  }
	      if (matched)	/* it's a raised character */
		{
		  /* map to string of unsigned shorts, length 3 or 6:
		     `begin superscript' control code, [`mark'
		     control code,] replacement char, [`return'
		     control code, underline,] `end superscript' */
		  dest[j++] =
		    (unsigned short) (CONTROL_CODE | C_BEGIN_SUPERSCRIPT);
		  if (_raised_char_tbl[i].underscored) /* also underline */
		    {
		      dest[j++] =
			(unsigned short) (CONTROL_CODE | C_PUSH_LOCATION);
		      dest[j++] =
			fontword | (unsigned short)_raised_char_tbl[i].to;
		      dest[j++] =
			(unsigned short) (CONTROL_CODE | C_POP_LOCATION);
		      /* select appropriate HersheySymbol font */
		      dest[j++] =
			symbol_fontword | (unsigned short)VECTOR_SYMBOL_FONT_UNDERSCORE;
		    }
		  else	/* just print raised char, no underline */
		    dest[j++] =
		      fontword | (unsigned short)_raised_char_tbl[i].to;

		  dest[j++] =
		    (unsigned short) (CONTROL_CODE | C_END_SUPERSCRIPT);

		  continue; /* back to top of while loop */
		}

	      /* since current font is an ISO-Latin-1 Hershey font, also
		 check if this char should be deligatured */
	      for (i = 0; i < NUM_DELIGATURED_CHARS; i++)
		if (c == _deligature_char_tbl[i].from)
		  {
		    matched = true;
		    break;
		  }
	      if (matched)
		{
		  if (_deligature_char_tbl[i].except_font != raw_fontnum)
		    {
		      dest[j++] = fontword
			| (unsigned short)_deligature_char_tbl[i].to[0];
		      dest[j++] = fontword
			| (unsigned short)_deligature_char_tbl[i].to[1];
		      continue;	/* back to top of while loop */
		    }
		}
	    }

	  /* didn't do anything special, so just pass the character thru */
	  dest[j++] = fontword | (unsigned short)c;
	  continue;		/* back to top of while loop */
	}
      else			/* character is a backslash */
	{
	  int i;

	  c = *(src++);		/* grab next character */
	  if (c == (unsigned char)'\0')	/* ASCII NUL ? */
	    {
	      dest[j++] = fontword | (unsigned short)'\\';
	      break;		/* string terminated with a backslash */
	    }

	  if (c == (unsigned char)'\\')
	    {
	      dest[j++] = fontword | (unsigned short)'\\';
	      dest[j++] = fontword | (unsigned short)'\\';
	      continue;		/* saw \\, leave as is */
	    }

	  d = *(src++);
	  if (d == (unsigned char)'\0')
	    {
	      dest[j++] = fontword | (unsigned short)'\\';
	      dest[j++] = fontword | (unsigned short)c;
	      break;		/* string terminated with \c */
	    }

	  esc[0] = c;
	  esc[1] = d;
	  esc[2] = (unsigned char)'\0';	/* have an escape sequence */

	  /* is this an escape seq. (e.g. \#H0001) for a raw Hershey glyph? */
	  if (1 /* _plotter->drawstate->font_type == F_HERSHEY */
	      && esc[0] == '#' && esc[1] == 'H'
	      && src[0] >= '0' && src[0] <= '9'
	      && src[1] >= '0' && src[1] <= '9'
	      && src[2] >= '0' && src[2] <= '9'
	      && src[3] >= '0' && src[3] <= '9')
	    {
	      int glyphindex;

	      glyphindex = (src[3] - '0') + 10 * (src[2] - '0')
		+ 100 * (src[1] - '0') + 1000 * (src[0] - '0');
	      if (glyphindex < NUM_OCCIDENTAL_HERSHEY_GLYPHS)
		{
		  dest[j++] = (unsigned short)(RAW_HERSHEY_GLYPH | glyphindex);
		  src += 4;
		  continue;	/* back to top of while loop */
		}
	    }

#ifndef NO_KANJI
	  /* is this an escape seq. (e.g. \#N0001) for a raw Japanese
	     Hershey glyph (Kanji), as numbered in Nelson's dictionary? */
	  if (1 /* _plotter->drawstate->font_type == F_HERSHEY */
	      && esc[0] == '#' && esc[1] == 'N'
	      && src[0] >= '0' && src[0] <= '9'
	      && src[1] >= '0' && src[1] <= '9'
	      && src[2] >= '0' && src[2] <= '9'
	      && src[3] >= '0' && src[3] <= '9')
	    {
	      int glyphindex;

	      glyphindex = (src[3] - '0') + 10 * (src[2] - '0')
		+ 100 * (src[1] - '0') + 1000 * (src[0] - '0');
	      if (glyphindex < NUM_ORIENTAL_HERSHEY_GLYPHS)
		{
		  dest[j++] = (unsigned short)(RAW_ORIENTAL_HERSHEY_GLYPH | glyphindex);
		  src += 4;
		  continue;	/* back to top of while loop */
		}
	    }
#endif /* not NO_KANJI */

	  /* is this an escape seq. (e.g. \#J0001) for a raw Japanese
	     Hershey glyph (JIS numbering, in hex)? */
	  if (1 /* _plotter->drawstate->font_type == F_HERSHEY */
	      && esc[0] == '#' && esc[1] == 'J'
	      && ((src[0] >= '0' && src[0] <= '9')
		  || (src[0] >= 'a' && src[0] <= 'f')
		  || (src[0] >= 'A' && src[0] <= 'F'))
	      && ((src[1] >= '0' && src[1] <= '9')
		  || (src[1] >= 'a' && src[1] <= 'f')
		  || (src[1] >= 'A' && src[1] <= 'F'))
	      && ((src[2] >= '0' && src[2] <= '9')
		  || (src[2] >= 'a' && src[2] <= 'f')
		  || (src[2] >= 'A' && src[2] <= 'F'))
	      && ((src[3] >= '0' && src[3] <= '9')
		  || (src[3] >= 'a' && src[3] <= 'f')
		  || (src[3] >= 'A' && src[3] <= 'F')))
	    {
	      int jis_glyphindex;
	      int i, hexnum[4];
	      int jis_row, jis_col;

	      for (i = 0; i < 4; i++)
		if (src[i] >= 'a' && src[i] <= 'f')
		  hexnum[i] = 10 + src[i] - 'a';
		else if (src[i] >= 'A' && src[i] <= 'F')
		  hexnum[i] = 10 + src[i] - 'A';
		else /* a decimal digit */
		  hexnum[i] = src[i] - '0';

	      jis_glyphindex = (hexnum[3] + 16 * hexnum[2]
				+ 256 * hexnum[1] + 4096 * hexnum[0]);
	      jis_row = hexnum[1] + 16 * hexnum[0];
	      jis_col = hexnum[3] + 16 * hexnum[2];

	      if (GOOD_JIS_INDEX(jis_row, jis_col))
		{
		  if (jis_glyphindex >= BEGINNING_OF_KANJI)
		    /* in Kanji range, so check if we have it */
		    {
#ifndef NO_KANJI
		      const struct kanjipair *kanji = _builtin_kanji_glyphs;
		      bool matched = false;

		      while (kanji->jis != 0)
			{
			  if (jis_glyphindex == kanji->jis)
			    {
			      matched = true;
			      break;
			    }
			  kanji++;
			}
		      if (matched)
			{
			  dest[j++] = (unsigned short)(RAW_ORIENTAL_HERSHEY_GLYPH | (kanji->nelson));
			  src += 4;
			  continue;	/* back to top of while loop */
			}
		      else		/* a Kanji we don't have */
			{
			  /* render as standard `undefined character' glyph */
			  dest[j++] = RAW_HERSHEY_GLYPH | UNDE;
			  src += 4;
			  continue;	/* back to top of while loop */
			}
#endif /* not NO_KANJI */
		    }
		  else
		    /* not in Kanji range, so look for it in char table */
		    {
		      const struct jis_entry *char_mapping = _builtin_jis_chars;
		      bool matched = false;

		      while (char_mapping->jis != 0)
			{
			  if (jis_glyphindex == char_mapping->jis)
			    {
			      matched = true;
			      break;
			    }
			  char_mapping++;
			}
		      if (matched)
			/* the entry in the character table maps the JIS
			   character to a character (in 0..255 range) in
			   one of the fonts in the master table in g_fontdb.c*/
			{
			  int fontnum = char_mapping->font;
			  unsigned short charnum = char_mapping->charnum;

			  if (charnum & RAW_HERSHEY_GLYPH)
			    /* a raw Hershey glyph, not in any font */
			    dest[j++] = RAW_HERSHEY_GLYPH | charnum;
			  else
			    /* a character in one of the fonts in g_fontdb.c */
			    dest[j++] = (unsigned short)((fontnum << FONT_SHIFT) | charnum);
			  src += 4;
			  continue; /* back to top of while loop */
			}
		      else	/* a character we don't have */
			{
			  /* render as standard `undefined character' glyph */
			  dest[j++] = RAW_HERSHEY_GLYPH | UNDE;
			  src += 4;
			  continue;	/* back to top of while loop */
			}
		    }
		}
	    }

	  {
	    bool matched = false;

	    /* is this an escape seq. for a control code? */
	    for (i = 0; i < NUM_CONTROLS; i++)
	      if (strcmp ((char *)esc, _control_tbl[i]) == 0)
		{
		  matched = true;
		  break;
		}
	    if (matched)		/* it's a control code */
	      {
		dest[j++] = (unsigned short)(CONTROL_CODE | i);
		continue;	/* back to top of while loop */
	      }
	  }

	  /* if current font is an ISO-Latin-1 Hershey font, is this an
	     escape sequence for an 8-bit (non-ASCII) char, which due to
	     nonexistence should be deligatured? */
	  if (1 /* _plotter->drawstate->font_type == F_HERSHEY */
	      && _hershey_font_info[raw_fontnum].iso8859_1)
	    {
	      int i;
	      bool matched = false;

	      for (i = 0; i < NUM_DELIGATURED_ESCAPES; i++)
		if (strcmp ((char *)esc, _deligature_escape_tbl[i].from) == 0)
		  {
		    matched = true;
		    break;
		  }
	      if (matched)
		{
		  if (_deligature_escape_tbl[i].except_font != raw_fontnum)
		    {
		      dest[j++] = fontword
			| (unsigned short)_deligature_escape_tbl[i].to[0];
		      dest[j++] = fontword
			| (unsigned short)_deligature_escape_tbl[i].to[1];

		      continue;	/* back to top of while loop */
		    }
		}
	    }

	  /* if the current font is an ISO-Latin-1 font (no matter whether
	     font is a a Hershey font, a PS or PCL/Stick font, or a
	     device-specific font for which we have no table entry), is
	     this an escape seq. for an 8-bit (non-ASCII) ISO8859-1 char?  */

	  /* PAUL MURRELL
	     Only concerned with Hershey fonts
	  */
/*
	  if ((_plotter->drawstate->font_type == F_POSTSCRIPT
	       && _ps_font_info[raw_fontnum].iso8859_1)
	      || (_plotter->drawstate->font_type == F_HERSHEY
		  && _hershey_font_info[raw_fontnum].iso8859_1)
	      || (_plotter->drawstate->font_type == F_PCL
		  && _pcl_font_info[raw_fontnum].iso8859_1)
	      || (_plotter->drawstate->font_type == F_STICK
		  && _stick_font_info[raw_fontnum].iso8859_1)
	      || (_plotter->drawstate->font_type == F_OTHER
		  && _plotter->drawstate->font_is_iso8859_1
		  && raw_fontnum == 1))
*/
	  if (1 /* _plotter->drawstate->font_type == F_HERSHEY */
	      && _hershey_font_info[raw_fontnum].iso8859_1)
	    {
	      bool matched = false;

	      for (i = 0; i < NUM_ISO_ESCAPES; i++)
		if (strcmp ((char *)esc, _iso_escape_tbl[i].string) == 0)
		  {
		    matched = true;
		    break;
		  }
	      if (matched)	/* it's an 8-bit ISO8859-1 character */
		{
		  /* certain such characters are drawn in the Hershey fonts
		     as superscripts */
		    if (1) /* _plotter->drawstate->font_type == F_HERSHEY) */
		    {
		      int k;
		      bool matched2 = false;

		      /* check if this is a `raised' ISO-Latin-1 character */
		      for (k = 0; k < NUM_RAISED_CHARS; k++)
			if (_iso_escape_tbl[i].byte == _raised_char_tbl[k].from)
			  {
			    matched2 = true;
			    break;
			  }
		      if (matched2)	/* it's a raised character */
			{
			  /* map to string of unsigned shorts, length 3 or 6:
			     `begin superscript' control code, [`mark'
			     control code,] replacement char, [`return'
			     control code, underline,] `end superscript' */
			  dest[j++] =
			    (unsigned short) (CONTROL_CODE | C_BEGIN_SUPERSCRIPT);
			  if (_raised_char_tbl[k].underscored) /* also underline */
			    {
			      dest[j++] =
				(unsigned short) (CONTROL_CODE | C_PUSH_LOCATION);
			      dest[j++] =
				fontword | (unsigned short)_raised_char_tbl[k].to;
			      dest[j++] =
				(unsigned short) (CONTROL_CODE | C_POP_LOCATION);
			      /* select appropriate HersheySymbol font */
			      dest[j++] =
				symbol_fontword | (unsigned short)VECTOR_SYMBOL_FONT_UNDERSCORE;
			    }
			  else	/* just print raised char, no underline */
			    {
			      dest[j++] =
				fontword | (unsigned short)_raised_char_tbl[k].to;
			    }

			  dest[j++] =
			    (unsigned short) (CONTROL_CODE | C_END_SUPERSCRIPT);

			  continue; /* back to top of while loop */
			}
		    }

		  /* won't draw this char as a superscript; just pass thru */
		  dest[j++] = fontword | (unsigned short)(_iso_escape_tbl[i].byte);
		  continue;	/* back to top of while loop */
		}
	    }

	  /* is this an escape seq. for a `special' (non-ISO, non-Symbol)
	     Hershey glyph?  Such glyphs include astronomical signs, and
	     `final s'. */
	  if (1) /* _plotter->drawstate->font_type == F_HERSHEY) */
	    {
	      bool matched = false;

	      for (i = 0; i < NUM_SPECIAL_ESCAPES; i++)
		if (strcmp ((char *)esc, _special_escape_tbl[i].string) == 0)
		  {
		    matched = true;
		    break;
		  }
	      if (matched)	/* it's a special character */
		{
		  /* "\s-" is special; yields character in current font */
		  if (_special_escape_tbl[i].byte == FINAL_LOWERCASE_S)
		  dest[j++] =
		    fontword | (unsigned short)(_special_escape_tbl[i].byte);
		  else
		  /* we select symbol font of typeface, in which we've
		     stored all other special characters */
		    dest[j++] = symbol_fontword | (unsigned short)(_special_escape_tbl[i].byte);
		  continue;	/* back to top of while loop */
		}
	    }

	  {
	    bool matched = false;

	    /* Irrespective of font type, is this an escape seq. for a char
	       in the font's corresponding symbol font? */
	    for (i = 0; i < NUM_SYMBOL_ESCAPES; i++)
	      if (strcmp (_symbol_escape_tbl[i].string, "NO_ABBREV") != 0
		  && strcmp ((char *)esc, _symbol_escape_tbl[i].string) == 0)
		{
		  matched = true;
		  break;
		}
	    if (matched)	/* it's a character in the symbol font */
	      {
		/* select symbol font by OR'ing in the symbol fontword */
		dest[j++] = symbol_fontword | (unsigned short)(_symbol_escape_tbl[i].byte);
		continue;	/* back to top of while loop */
	      }
	  }

	  /* Gross kludge.  In the non-Hershey fonts we handle the "\rn"
	     control sequence in a painful way.  For a PS font we map it
	     into (1) a left shift, (2) the `radicalex' character in the PS
	     Symbol font, and (3) a right shift.  Shift distances are taken
	     from the bbox of the radicalex char, and are slightly larger
	     than 0.5 em.  For a PCL font it's similar, but the shifts are
	     much smaller.  The reason it's different for PCL is that the
	     PCL radicalex character is different from the PS radicalex
	     character: the overbar is not displaced.  Possibly someone at
	     HP made a mistake while reimplementing the Adobe Symbol font
	     for PCL 5?

	     We don't implement \rn for Stick fonts, because they have
	     no associated symbol font. */

	  /* couldn't match; unknown escape seq., so pass through unchanged */
	  dest[j++] = fontword | (unsigned short)'\\';
	  dest[j++] = fontword | (unsigned short)c;
	  dest[j++] = fontword | (unsigned short)d;
	}
    }

  dest[j] = (unsigned short)'\0';   /* terminate string */

  return dest;
}

#ifdef UNUSED
int
#ifdef _HAVE_PROTOS
_codestring_len (const unsigned short *codestring)
#else
_codestring_len (codestring)
     const unsigned short *codestring;
#endif
{
  int i = 0;

  while (*codestring)
    {
      i++;
      codestring++;
    }

  return i;
}
#endif
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 1995, 1996  Robert Gentleman and Ross Ihaka
 *  Copyright (C) 1997--2016  The R Core Team.
 *  Copyright (C) 2003--2016  The R Foundation
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 *
 *
 * Object Formatting
 *
 *  See ./paste.c for do_paste() , do_format() and do_formatinfo() and
 *       ./util.c for do_formatC()
 *  See ./printutils.c for general remarks on Printing and the Encode.. utils.
 *  See ./print.c  for do_printdefault, do_prmatrix, etc.
 *
 * Exports
 *	formatString
 *	formatLogical
 *	formatInteger
 *	formatReal
 *	formatComplex
 *
 * These  formatFOO() functions determine the proper width, digits, etc.
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <Defn.h>
#include <float.h> /* for DBL_EPSILON */
#include <Rmath.h>
#include <Print.h>

/* this is just for conformity with other types */
attribute_hidden
void formatRaw(Rbyte *x, R_xlen_t n, int *fieldwidth)
{
    *fieldwidth = 2;
}

attribute_hidden
void formatString(SEXP *x, R_xlen_t n, int *fieldwidth, int quote)
{
    int xmax = 0;
    int l;

    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] == NA_STRING) {
	    l = quote ? R_print.na_width : R_print.na_width_noquote;
	} else l = Rstrlen(x[i], quote) + (quote ? 2 : 0);
	if (l > xmax) xmax = l;
    }
    *fieldwidth = xmax;
}

void formatLogical(int *x, R_xlen_t n, int *fieldwidth)
{
    *fieldwidth = 1;
    for(R_xlen_t i = 0 ; i < n; i++) {
	if (x[i] == NA_LOGICAL) {
	    if(*fieldwidth < R_print.na_width)
		*fieldwidth =  R_print.na_width;
	} else if (x[i] != 0 && *fieldwidth < 4) {
	    *fieldwidth = 4;
	} else if (x[i] == 0 && *fieldwidth < 5 ) {
	    *fieldwidth = 5;
	    break;
	    /* this is the widest it can be,  so stop */
	}
    }
}

void formatInteger(int *x, R_xlen_t n, int *fieldwidth)
{
    int xmin = INT_MAX, xmax = INT_MIN, naflag = 0;
    int l;

    for (R_xlen_t i = 0; i < n; i++) {
	if (x[i] == NA_INTEGER)
	    naflag = 1;
	else {
	    if (x[i] < xmin) xmin = x[i];
	    if (x[i] > xmax) xmax = x[i];
	}
    }

    if (naflag) *fieldwidth = R_print.na_width;
    else *fieldwidth = 1;

    if (xmin < 0) {
	l = IndexWidth(-xmin) + 1;	/* +1 for sign */
	if (l > *fieldwidth) *fieldwidth = l;
    }
    if (xmax > 0) {
	l = IndexWidth(xmax);
	if (l > *fieldwidth) *fieldwidth = l;
    }
}

/*---------------------------------------------------------------------------
 * scientific format determination for real numbers.
 * This is time-critical code.	 It is worth optimizing.
 *
 *    nsig		digits altogether
 *    kpower+1		digits to the left of "."
 *    kpower+1+sgn	including sign
 *
 * Using GLOBAL	 R_print.digits	 -- had	 #define MAXDIG R_print.digits
*/

/* long double is C99, so should always be defined but may be slow */
#if defined(HAVE_LONG_DOUBLE) && (SIZEOF_LONG_DOUBLE > SIZEOF_DOUBLE)
# ifdef HAVE_NEARBYINTL
# define R_nearbyintl nearbyintl
/* Cygwin had rintl but not nearbyintl */
# elif defined(HAVE_RINTL)
# define R_nearbyintl rintl
# else
# define R_nearbyintl private_nearbyintl
LDOUBLE private_nearbyintl(LDOUBLE x)
{
    LDOUBLE x1;
    x1 = - floorl(-x + 0.5);
    x = floorl(x + 0.5);
    if (x == x1) return(x);
    else {
	/* FIXME: we should really test for floorl, also C99.
	   But FreeBSD 7.x does have it, but not nearbyintl */
        if (x/2.0 == floorl(x/2.0)) return(x); else return(x1);
    }
}
# endif
# else /* no long double */
# ifdef HAVE_NEARBYINT
#  define R_nearbyint nearbyint
# elif defined(HAVE_RINT)
#  define R_nearbyint rint
# else
#  define R_nearbyint private_rint
#  include "nmath2.h" // for private_rint
# endif
#endif

#define NB 1000
static void format_via_sprintf(double r, int d, int *kpower, int *nsig)
{
    static char buff[NB];
    int i;
    snprintf(buff, NB, "%#.*e", d - 1, r);
    *kpower = (int) strtol(buff + (d + 2), NULL, 10);
    for (i = d; i >= 2; i--)
        if (buff[i] != '0') break;
    *nsig = i;
}


#if defined(HAVE_LONG_DOUBLE) && (SIZEOF_LONG_DOUBLE > SIZEOF_DOUBLE)
static const long double tbl[] =
{
    /* Powers exactly representable with 64 bit mantissa (except the first, which is only used with digits=0) */
    1e-1,
    1e00, 1e01, 1e02, 1e03, 1e04, 1e05, 1e06, 1e07, 1e08, 1e09,
    1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19,
    1e20, 1e21, 1e22, 1e23, 1e24, 1e25, 1e26, 1e27
};
#define KP_MAX 27
#else
static const double tbl[] =
{
    1e-1,
    1e00, 1e01, 1e02, 1e03, 1e04, 1e05, 1e06, 1e07, 1e08, 1e09,
    1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19,
    1e20, 1e21, 1e22
};
#define KP_MAX 22
#endif

static void
scientific(double *x, int *neg, int *kpower, int *nsig, Rboolean *roundingwidens)
{
    /* for a number x , determine
     *	neg    = 1_{x < 0}  {0/1}
     *	kpower = Exponent of 10;
     *	nsig   = min(R_print.digits, #{significant digits of alpha})
     *  roundingwidens = TRUE iff rounding causes x to increase in width
     *
     * where  |x| = alpha * 10^kpower	and	 1 <= alpha < 10
     */
    register double alpha;
    register double r;
    register int kp;
    int j;

    if (*x == 0.0) {
	*kpower = 0;
	*nsig = 1;
	*neg = 0;
	*roundingwidens = FALSE;
    } else {
	if(*x < 0.0) {
	    *neg = 1; r = -*x;
	} else {
	    *neg = 0; r = *x;
	}
        if (R_print.digits >= DBL_DIG + 1) {
            format_via_sprintf(r, R_print.digits, kpower, nsig);
	    *roundingwidens = FALSE;
            return;
        }
        kp = (int) floor(log10(r)) - R_print.digits + 1;/* r = |x|; 10^(kp + digits - 1) <= r */
#if defined(HAVE_LONG_DOUBLE) && (SIZEOF_LONG_DOUBLE > SIZEOF_DOUBLE)
        long double r_prec = r;
        /* use exact scaling factor in long double precision, if possible */
        if (abs(kp) <= 27) {
            if (kp > 0) r_prec /= tbl[kp+1]; else if (kp < 0) r_prec *= tbl[ -kp+1];
        }
#ifdef HAVE_POWL
	else
            r_prec /= powl(10.0, (long double) kp);
#else
        else if (kp <= R_dec_min_exponent)
            r_prec = (r_prec * 1e+303)/Rexp10((double)(kp+303));
        else
            r_prec /= Rexp10((double) kp);
#endif
        if (r_prec < tbl[R_print.digits]) {
            r_prec *= 10.0;
            kp--;
        }
        /* round alpha to integer, 10^(digits-1) <= alpha <= 10^digits
	   accuracy limited by double rounding problem,
	   alpha already rounded to 64 bits */
        alpha = (double) R_nearbyintl(r_prec);
#else
	double r_prec = r;
        /* use exact scaling factor in double precision, if possible */
        if (abs(kp) <= 22) {
            if (kp >= 0) r_prec /= tbl[kp+1]; else r_prec *= tbl[ -kp+1];
        }
        /* on IEEE 1e-308 is not representable except by gradual underflow.
           Shifting by 303 allows for any potential denormalized numbers x,
           and makes the reasonable assumption that R_dec_min_exponent+303
           is in range. Representation of 1e+303 has low error.
         */
        else if (kp <= R_dec_min_exponent)
            r_prec = (r_prec * 1e+303)/Rexp10((double)(kp+303));
        else
            r_prec /= Rexp10((double)kp);
        if (r_prec < tbl[R_print.digits]) {
            r_prec *= 10.0;
            kp--;
        }
        /* round alpha to integer, 10^(digits-1) <= alpha <= 10^digits */
        /* accuracy limited by double rounding problem,
	   alpha already rounded to 53 bits */
        alpha = R_nearbyint(r_prec);
#endif
        *nsig = R_print.digits;
        for (j = 1; j <= R_print.digits; j++) {
            alpha /= 10.0;
            if (alpha == floor(alpha)) {
                (*nsig)--;
            } else {
                break;
            }
        }
        if (*nsig == 0 && R_print.digits > 0) {
            *nsig = 1;
            kp += 1;
        }
        *kpower = kp + R_print.digits - 1;

	/* Scientific format may do more rounding than fixed format, e.g.
	   9996 with 3 digits is 1e+04 in scientific, but 9996 in fixed.
	   This happens when the true value r is less than 10^(kpower+1)
	   and would not round up to it in fixed format.
	   Here rgt is the decimal place that will be cut off by rounding */

	int rgt = R_print.digits - *kpower;
	/* bound rgt by 0 and KP_MAX */
	rgt = rgt < 0 ? 0 : rgt > KP_MAX ? KP_MAX : rgt;
	double fuzz = 0.5/(double)tbl[1 + rgt];
	// kpower can be bigger than the table.
	*roundingwidens = *kpower > 0 && *kpower <= KP_MAX && r < tbl[*kpower + 1] - fuzz;
    }
}

/*
   The return values are
     w : the required field width
     d : use %w.df in fixed format, %#w.de in scientific format
     e : use scientific format if != 0, value is number of exp digits - 1

   nsmall specifies the minimum number of decimal digits in fixed format:
   it is 0 except when called from do_format.
*/

void formatReal(double *x, R_xlen_t n, int *w, int *d, int *e, int nsmall)
{
    int left, right, sleft;
    int mnl, mxl, rgt, mxsl, mxns, wF;
    Rboolean roundingwidens;
    int neg_i, neg, kpower, nsig;
    int naflag, nanflag, posinf, neginf;

    nanflag = 0;
    naflag = 0;
    posinf = 0;
    neginf = 0;
    neg = 0;
    rgt = mxl = mxsl = mxns = INT_MIN;
    mnl = INT_MAX;

    for (R_xlen_t i = 0; i < n; i++) {
	if (!R_FINITE(x[i])) {
	    if(ISNA(x[i])) naflag = 1;
	    else if(ISNAN(x[i])) nanflag = 1;
	    else if(x[i] > 0) posinf = 1;
	    else neginf = 1;
	} else {
	    scientific(&x[i], &neg_i, &kpower, &nsig, &roundingwidens);

	    left = kpower + 1;
	    if (roundingwidens) left--;

	    sleft = neg_i + ((left <= 0) ? 1 : left); /* >= 1 */
	    right = nsig - left; /* #{digits} right of '.' ( > 0 often)*/
	    if (neg_i) neg = 1;	 /* if any < 0, need extra space for sign */

	    /* Infinite precision "F" Format : */
	    if (right > rgt) rgt = right;	/* max digits to right of . */
	    if (left > mxl)  mxl = left;	/* max digits to  left of . */
	    if (left < mnl)  mnl = left;	/* min digits to  left of . */
	    if (sleft> mxsl) mxsl = sleft;	/* max left including sign(s)*/
	    if (nsig > mxns) mxns = nsig;	/* max sig digits */
	}
    }
    /* F Format: use "F" format WHENEVER we use not more space than 'E'
     *		and still satisfy 'R_print.digits' {but as if nsmall==0 !}
     *
     * E Format has the form   [S]X[.XXX]E+XX[X]
     *
     * This is indicated by setting *e to non-zero (usually 1)
     * If the additional exponent digit is required *e is set to 2
     */

    /*-- These	'mxsl' & 'rgt'	are used in F Format
     *	 AND in the	____ if(.) "F" else "E" ___   below: */
    if (R_print.digits == 0) rgt = 0;
    if (mxl < 0) mxsl = 1 + neg;  /* we use %#w.dg, so have leading zero */

    /* use nsmall only *after* comparing "F" vs "E": */
    if (rgt < 0) rgt = 0;
    wF = mxsl + rgt + (rgt != 0);	/* width for F format */

    /*-- 'see' how "E" Exponential format would be like : */
    *e = (mxl > 100 || mnl <= -99) ? 2 /* 3 digit exponent */ : 1;
    if (mxns != INT_MIN) {
	*d = mxns - 1;
	*w = neg + (*d > 0) + *d + 4 + *e; /* width for E format */
	if (wF <= *w + R_print.scipen) { /* Fixpoint if it needs less space */
	    *e = 0;
	    if (nsmall > rgt) {
		rgt = nsmall;
		wF = mxsl + rgt + (rgt != 0);
	    }
	    *d = rgt;
	    *w = wF;
	} /* else : "E" Exponential format -- all done above */
    }
    else { /* when all x[i] are non-finite */
	*w = 0;/* to be increased */
	*d = 0;
	*e = 0;
    }
    if (naflag && *w < R_print.na_width)
	*w = R_print.na_width;
    if (nanflag && *w < 3) *w = 3;
    if (posinf && *w < 3) *w = 3;
    if (neginf && *w < 4) *w = 4;
}

/* As from 2.2.0 the number of digits applies to real and imaginary parts
   together, not separately */
void z_prec_r(Rcomplex *r, Rcomplex *x, double digits);

void formatComplex(Rcomplex *x, R_xlen_t n, int *wr, int *dr, int *er,
		   int *wi, int *di, int *ei, int nsmall)
{
/* format.info() for  x[1..n] for both Re & Im */
    int left, right, sleft;
    int rt, mnl, mxl, mxsl, mxns, wF, i_wF;
    int i_rt, i_mnl, i_mxl, i_mxsl, i_mxns;
    Rboolean roundingwidens;
    int neg_i, neg, kpower, nsig;
    int naflag, rnanflag, rposinf, rneginf, inanflag, iposinf;
    Rcomplex tmp;
    Rboolean all_re_zero = TRUE, all_im_zero = TRUE;

    naflag = 0;
    rnanflag = 0;
    rposinf = 0;
    rneginf = 0;
    inanflag = 0;
    iposinf = 0;
    neg = 0;

    rt	=  mxl =  mxsl =  mxns = INT_MIN;
    i_rt= i_mxl= i_mxsl= i_mxns= INT_MIN;
    i_mnl = mnl = INT_MAX;

    for (R_xlen_t i = 0; i < n; i++) {
	/* Now round */
	z_prec_r(&tmp, &(x[i]), R_print.digits);
	if(ISNA(tmp.r) || ISNA(tmp.i)) {
	    naflag = 1;
	} else {
	    /* real part */

	    if(!R_FINITE(tmp.r)) {
		if (ISNAN(tmp.r)) rnanflag = 1;
		else if (tmp.r > 0) rposinf = 1;
		else rneginf = 1;
	    } else {
		if(x[i].r != 0) all_re_zero = FALSE;
		scientific(&(tmp.r), &neg_i, &kpower, &nsig, &roundingwidens);

		left = kpower + 1;
		if (roundingwidens) left--;
		sleft = neg_i + ((left <= 0) ? 1 : left); /* >= 1 */
		right = nsig - left; /* #{digits} right of '.' ( > 0 often)*/
		if (neg_i) neg = 1; /* if any < 0, need extra space for sign */

		if (right > rt) rt = right;	/* max digits to right of . */
		if (left > mxl) mxl = left;	/* max digits to left of . */
		if (left < mnl) mnl = left;	/* min digits to left of . */
		if (sleft> mxsl) mxsl = sleft;	/* max left including sign(s) */
		if (nsig > mxns) mxns = nsig;	/* max sig digits */

	    }
	    /* imaginary part */

	    /* this is always unsigned */
	    /* we explicitly put the sign in when we print */

	    if(!R_FINITE(tmp.i)) {
		if (ISNAN(tmp.i)) inanflag = 1;
		else iposinf = 1;
	    } else {
		if(x[i].i != 0) all_im_zero = FALSE;
		scientific(&(tmp.i), &neg_i, &kpower, &nsig, &roundingwidens);

		left = kpower + 1;
		if (roundingwidens) left--;
		sleft = ((left <= 0) ? 1 : left);
		right = nsig - left;

		if (right > i_rt) i_rt = right;
		if (left > i_mxl) i_mxl = left;
		if (left < i_mnl) i_mnl = left;
		if (sleft> i_mxsl) i_mxsl = sleft;
		if (nsig > i_mxns) i_mxns = nsig;
	    }
	    /* done: ; */
	}
    }

    /* see comments in formatReal() for details on this */

    /* overall format for real part	*/

    if (R_print.digits == 0) rt = 0;
    if (mxl != INT_MIN) {
	if (mxl < 0) mxsl = 1 + neg;
	if (rt < 0) rt = 0;
	wF = mxsl + rt + (rt != 0);

	*er = (mxl > 100 || mnl < -99) ? 2 : 1;
	*dr = mxns - 1;
	*wr = neg + (*dr > 0) + *dr + 4 + *er;
    } else {
	*er = 0;
	*wr = 0;
	*dr = 0;
	wF = 0;
    }

    /* overall format for imaginary part */

    if (R_print.digits == 0) i_rt = 0;
    if (i_mxl != INT_MIN) {
	if (i_mxl < 0) i_mxsl = 1;
	if (i_rt < 0) i_rt = 0;
	i_wF = i_mxsl + i_rt + (i_rt != 0);

	*ei = (i_mxl > 100 || i_mnl < -99) ? 2 : 1;
	*di = i_mxns - 1;
	*wi = (*di > 0) + *di + 4 + *ei;
    } else {
	*ei = 0;
	*wi = 0;
	*di = 0;
	i_wF = 0;
    }

    /* Now make the fixed/scientific decision */
    if(all_re_zero) {
	*er = *dr = 0;
	*wr = wF;
	if (i_wF <= *wi + R_print.scipen) {
	    *ei = 0;
	    if (nsmall > i_rt) {i_rt = nsmall; i_wF = i_mxsl + i_rt + (i_rt != 0);}
	    *di = i_rt;
	    *wi = i_wF;
	}
    } else if(all_im_zero) {
	if (wF <= *wr + R_print.scipen) {
	    *er = 0;
	    if (nsmall > rt) {rt = nsmall; wF = mxsl + rt + (rt != 0);}
	    *dr = rt;
	    *wr = wF;
	    }
	*ei = *di = 0;
	*wi = i_wF;
    } else if(wF + i_wF < *wr + *wi + 2*R_print.scipen) {
	    *er = 0;
	    if (nsmall > rt) {rt = nsmall; wF = mxsl + rt + (rt != 0);}
	    *dr = rt;
	    *wr = wF;

	    *ei = 0;
	    if (nsmall > i_rt) {
		i_rt = nsmall;
		i_wF = i_mxsl + i_rt + (i_rt != 0);
	    }
	    *di = i_rt;
	    *wi = i_wF;
    } /* else scientific for both */
    if(*wr < 0) *wr = 0;
    if(*wi < 0) *wi = 0;

    /* Ensure space for Inf and NaN */
    if (rnanflag && *wr < 3) *wr = 3;
    if (rposinf &&  *wr < 3) *wr = 3;
    if (rneginf &&  *wr < 4) *wr = 4;
    if (inanflag && *wi < 3) *wi = 3;
    if (iposinf  && *wi < 3) *wi = 3;

    /* finally, ensure that there is space for NA */

    if (naflag && *wr+*wi+2 < R_print.na_width)
	*wr += (R_print.na_width -(*wr + *wi + 2));
}
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 2002--2016     The R Core Team
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 *
 * Originally written by Jonathan Rougier
*/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <Defn.h>
#include <Internal.h>
#include "RBufferUtils.h"
#include <R_ext/RS.h> /* for Calloc/Free */
#ifdef Win32
#include <trioremap.h>
#endif

#define MAXLINE MAXELTSIZE
#define MAXNARGS 100
/*               ^^^ not entirely arbitrary, but strongly linked to allowing %$1 to %$99 !*/

/*
   This is passed a format that started with % and may include other
   chars, e.g. '.2f abc'.  It's aim is to show that this is a valid
   format from one of the types given in pattern.
*/

static const char *findspec(const char *str)
{
    /* This is not strict about checking where '.' is allowed.
       It should allow  - + ' ' # 0 as flags
       m m. .n n.m as width/precision
    */
    const char *p = str;

    if(*p != '%') return p;
    for(p++; ; p++) {
	if(*p == '-' || *p == '+' || *p == ' ' || *p == '#' || *p == '.' ) continue;
	/* '*' will currently have got substituted before this */
	if(*p == '*' || (*p >= '0' && *p <= '9')) continue;
	break;
    }
    return p;
}


/*   FALSE is success, TRUE is an error: pattern *not* found . */
static Rboolean checkfmt(const char *fmt, const char *pattern)
{
    const char *p =fmt;

    if(*p != '%') return TRUE;
    p = findspec(fmt);
    return strcspn(p, pattern) ? TRUE : FALSE;
}

#define TRANSLATE_CHAR(_STR_, _i_)  \
   ((use_UTF8) ? translateCharUTF8(STRING_ELT(_STR_, _i_))  \
    : translateChar(STRING_ELT(_STR_, _i_)))


SEXP attribute_hidden do_sprintf(SEXP call, SEXP op, SEXP args, SEXP env)
{
    int i, nargs, cnt, v, thislen, nfmt, nprotect = 0;
    /* fmt2 is a copy of fmt with '*' expanded.
       bit will hold numeric formats and %<w>s, so be quite small. */
    char fmt[MAXLINE+1], fmt2[MAXLINE+10], *fmtp, bit[MAXLINE+1],
	*outputString;
    const char *formatString;
    size_t n, cur, chunk;

    SEXP format, _this, a[MAXNARGS], ans /* -Wall */ = R_NilValue;
    int ns, maxlen, lens[MAXNARGS], nthis, nstar, star_arg = 0;
    static R_StringBuffer outbuff = {NULL, 0, MAXELTSIZE};
    Rboolean has_star, use_UTF8;

#define _my_sprintf(_X_)						\
    {									\
	int nc = snprintf(bit, MAXLINE+1, fmtp, _X_);			\
	if (nc > MAXLINE)						\
	    error(_("required resulting string length %d is greater than maximal %d"), \
		  nc, MAXLINE);						\
    }

    nargs = length(args);
    /* grab the format string */
    format = CAR(args);
    if (!isString(format))
	error(_("'fmt' is not a character vector"));
    nfmt = length(format);
    if (nfmt == 0) return allocVector(STRSXP, 0);
    args = CDR(args); nargs--;
    if(nargs >= MAXNARGS)
	error(_("only %d arguments are allowed"), MAXNARGS);

    /* record the args for possible coercion and later re-ordering */
    for(i = 0; i < nargs; i++, args = CDR(args)) {
	SEXPTYPE t_ai;
	a[i] = CAR(args);
	if((t_ai = TYPEOF(a[i])) == LANGSXP || t_ai == SYMSXP) /* << maybe add more .. */
	    error(_("invalid type of argument[%d]: '%s'"),
		  i+1, CHAR(type2str(t_ai)));
	lens[i] = length(a[i]);
	if(lens[i] == 0) return allocVector(STRSXP, 0);
    }

#define CHECK_maxlen							\
    maxlen = nfmt;							\
    for(i = 0; i < nargs; i++)						\
	if(maxlen < lens[i]) maxlen = lens[i];				\
    if(maxlen % nfmt)							\
	error(_("arguments cannot be recycled to the same length"));	\
    for(i = 0; i < nargs; i++)						\
	if(maxlen % lens[i])						\
	    error(_("arguments cannot be recycled to the same length"))

    CHECK_maxlen;

    outputString = R_AllocStringBuffer(0, &outbuff);

    /* We do the format analysis a row at a time */
    for(ns = 0; ns < maxlen; ns++) {
	outputString[0] = '\0';
	use_UTF8 = getCharCE(STRING_ELT(format, ns % nfmt)) == CE_UTF8;
	if (!use_UTF8) {
	    for(i = 0; i < nargs; i++) {
		if (!isString(a[i])) continue;
		if (getCharCE(STRING_ELT(a[i], ns % lens[i])) == CE_UTF8) {
		    use_UTF8 = TRUE; break;
		}
	    }
	}

	formatString = TRANSLATE_CHAR(format, ns % nfmt);
	n = strlen(formatString);
	if (n > MAXLINE)
	    error(_("'fmt' length exceeds maximal format length %d"), MAXLINE);
	/* process the format string */
	for (cur = 0, cnt = 0; cur < n; cur += chunk) {
	    const char *curFormat = formatString + cur, *ss;
	    char *starc;
	    ss = NULL;
	    if (formatString[cur] == '%') { /* handle special format command */

		if (cur < n - 1 && formatString[cur + 1] == '%') {
		    /* take care of %% in the format */
		    chunk = 2;
		    strcpy(bit, "%");
		}
		else {
		    /* recognise selected types from Table B-1 of K&R */
		    /* NB: we deal with "%%" in branch above. */
		    /* This is MBCS-OK, as we are in a format spec */
		    chunk = strcspn(curFormat + 1, "diosfeEgGxXaA") + 2;
		    if (cur + chunk > n)
			error(_("unrecognised format specification '%s'"), curFormat);

		    strncpy(fmt, curFormat, chunk);
		    fmt[chunk] = '\0';

		    nthis = -1;
		    /* now look for %n$ or %nn$ form */
		    if (strlen(fmt) > 3 && fmt[1] >= '1' && fmt[1] <= '9') {
			v = fmt[1] - '0';
			if(fmt[2] == '$') {
			    if(v > nargs)
				error(_("reference to non-existent argument %d"), v);
			    nthis = v-1;
			    memmove(fmt+1, fmt+3, strlen(fmt)-2);
			} else if(fmt[2] >= '0' && fmt[2] <= '9' && fmt[3] == '$') {
			    v = 10*v + fmt[2] - '0';
			    if(v > nargs)
				error(_("reference to non-existent argument %d"), v);
			    nthis = v-1;
			    memmove(fmt+1, fmt+4, strlen(fmt)-3);
			}
		    }

		    starc = Rf_strchr(fmt, '*');
		    if (starc) { /* handle  *  format if present */
			nstar = -1;
			if (strlen(starc) > 3 && starc[1] >= '1' && starc[1] <= '9') {
			    v = starc[1] - '0';
			    if(starc[2] == '$') {
				if(v > nargs)
				    error(_("reference to non-existent argument %d"), v);
				nstar = v-1;
				memmove(starc+1, starc+3, strlen(starc)-2);
			    } else if(starc[2] >= '0' && starc[2] <= '9'
				      && starc[3] == '$') {
				v = 10*v + starc[2] - '0';
				if(v > nargs)
				    error(_("reference to non-existent argument %d"), v);
				nstar = v-1;
				memmove(starc+1, starc+4, strlen(starc)-3);
			    }
			}

			if(nstar < 0) {
			    if (cnt >= nargs) error(_("too few arguments"));
			    nstar = cnt++;
			}

			if (Rf_strchr(starc+1, '*'))
			    error(_("at most one asterisk '*' is supported in each conversion specification"));

			_this = a[nstar];
			if(ns == 0 && TYPEOF(_this) == REALSXP) {
			    _this = coerceVector(_this, INTSXP);
			    PROTECT(a[nstar] = _this);
			    nprotect++;
			}
			if(TYPEOF(_this) != INTSXP || LENGTH(_this)<1 ||
			   INTEGER(_this)[ns % LENGTH(_this)] == NA_INTEGER)
			    error(_("argument for '*' conversion specification must be a number"));
			star_arg = INTEGER(_this)[ns % LENGTH(_this)];
			has_star = TRUE;
		    }
		    else
			has_star = FALSE;

		    if (fmt[strlen(fmt) - 1] == '%') {
			/* handle % with formatting options */
			if (has_star)
			    snprintf(bit, MAXLINE+1, fmt, star_arg);
			else
			    strcpy(bit, fmt);
			/* was sprintf(..)  for which some compiler warn */
		    } else {
			Rboolean did_this = FALSE;
			if(nthis < 0) {
			    if (cnt >= nargs) error(_("too few arguments"));
			    nthis = cnt++;
			}
			_this = a[nthis];
			if (has_star) {
			    size_t nf; char *p, *q = fmt2;
			    for (p = fmt; *p; p++)
				if (*p == '*') q += sprintf(q, "%d", star_arg);
				else *q++ = *p;
			    *q = '\0';
			    nf = strlen(fmt2);
			    if (nf > MAXLINE)
				error(_("'fmt' length exceeds maximal format length %d"),
				      MAXLINE);
			    fmtp = fmt2;
			} else fmtp = fmt;

#define CHECK_this_length						\
			do {						\
			    PROTECT(_this);				\
			    thislen = length(_this);			\
			    if(thislen == 0)				\
				error(_("coercion has changed vector length to 0")); \
			} while (0)

			/* Now let us see if some minimal coercion
			   would be sensible, but only do so once, for ns = 0: */
			if(ns == 0) {
			    SEXP tmp; Rboolean do_check;
			    switch(*findspec(fmtp)) {
			    case 'd':
			    case 'i':
			    case 'o':
			    case 'x':
			    case 'X':
				if(TYPEOF(_this) == REALSXP) {
				    double r = REAL(_this)[0];
				    // qdapTools manages to call this with NaN
				    if(R_FINITE(r) && (double)((int) r) == r)
					_this = coerceVector(_this, INTSXP);
				    PROTECT(a[nthis] = _this);
				    nprotect++;
				}
				break;
			    case 'a':
			    case 'A':
			    case 'e':
			    case 'f':
			    case 'g':
			    case 'E':
			    case 'G':
				if(TYPEOF(_this) != REALSXP &&
				   /* no automatic as.double(<string>) : */
				   TYPEOF(_this) != STRSXP) {
				    PROTECT(tmp = lang2(install("as.double"), _this));
#define COERCE_THIS_TO_A						\
				    _this = eval(tmp, env);		\
				    UNPROTECT(1);			\
				    PROTECT(a[nthis] = _this);		\
				    nprotect++;				\
				    did_this = TRUE;			\
				    CHECK_this_length;			\
				    do_check = (lens[nthis] == maxlen);	\
				    lens[nthis] = thislen; /* may have changed! */ \
				    if(do_check && thislen < maxlen) {	\
					CHECK_maxlen;			\
				    }

				    COERCE_THIS_TO_A
				}
				break;
			    case 's':
				if(TYPEOF(_this) != STRSXP) {
				    /* as.character method might call sprintf() */
				    size_t nc = strlen(outputString);
				    char *z = Calloc(nc+1, char);
				    strcpy(z, outputString);
				    PROTECT(tmp = lang2(R_AsCharacterSymbol, _this));

				    COERCE_THIS_TO_A
				    strcpy(outputString, z);
				    Free(z);
				}
				break;
			    default:
				break;
			    }
			} /* ns == 0 (first-time only) */

			if(!did_this)
			    CHECK_this_length;

			switch(TYPEOF(_this)) {
			case LGLSXP:
			    {
				int x = LOGICAL(_this)[ns % thislen];
				if (checkfmt(fmtp, "di"))
				    error(_("invalid format '%s'; %s"), fmtp,
					  _("use format %d or %i for logical objects"));
				if (x == NA_LOGICAL) {
				    fmtp[strlen(fmtp)-1] = 's';
				    _my_sprintf("NA")
				} else {
				    _my_sprintf(x)
				}
				break;
			    }
			case INTSXP:
			    {
				int x = INTEGER(_this)[ns % thislen];
				if (checkfmt(fmtp, "dioxX"))
				    error(_("invalid format '%s'; %s"), fmtp,
					  _("use format %d, %i, %o, %x or %X for integer objects"));
				if (x == NA_INTEGER) {
				    fmtp[strlen(fmtp)-1] = 's';
				    _my_sprintf("NA")
				} else {
				    _my_sprintf(x)
				}
				break;
			    }
			case REALSXP:
			    {
				double x = REAL(_this)[ns % thislen];
				if (checkfmt(fmtp, "aAfeEgG"))
				    error(_("invalid format '%s'; %s"), fmtp,
					  _("use format %f, %e, %g or %a for numeric objects"));
				if (R_FINITE(x)) {
				    _my_sprintf(x)
				} else {
				    char *p = Rf_strchr(fmtp, '.');
				    if (p) {
					*p++ = 's'; *p ='\0';
				    } else
					fmtp[strlen(fmtp)-1] = 's';
				    if (ISNA(x)) {
					if (strcspn(fmtp, " ") < strlen(fmtp))
					    _my_sprintf(" NA")
					else
					    _my_sprintf("NA")
				    } else if (ISNAN(x)) {
					if (strcspn(fmtp, " ") < strlen(fmtp))
					    _my_sprintf(" NaN")
					else
					    _my_sprintf("NaN")
				    } else if (x == R_PosInf) {
					if (strcspn(fmtp, "+") < strlen(fmtp))
					    _my_sprintf("+Inf")
					else if (strcspn(fmtp, " ") < strlen(fmtp))
					    _my_sprintf(" Inf")
					else
					    _my_sprintf("Inf")
				    } else if (x == R_NegInf)
					_my_sprintf("-Inf")
				}
				break;
			    }
			case STRSXP:
			    /* NA_STRING will be printed as 'NA' */
			    if (checkfmt(fmtp, "s"))
				error(_("invalid format '%s'; %s"), fmtp,
				      _("use format %s for character objects"));

			    ss = TRANSLATE_CHAR(_this, ns % thislen);
			    if(fmtp[1] != 's') {
				if(strlen(ss) > MAXLINE)
				    warning(_("likely truncation of character string to %d characters"),
					    MAXLINE-1);
				_my_sprintf(ss)
				bit[MAXLINE] = '\0';
				ss = NULL;
			    }
			    break;

			default:
			    error(_("unsupported type"));
			    break;
			}

			UNPROTECT(1);
		    }
		}
	    }
	    else { /* not '%' : handle string part */
		char *ch = Rf_strchr(curFormat, '%'); /* MBCS-aware version used */
		chunk = (ch) ? (size_t) (ch - curFormat) : strlen(curFormat);
		strncpy(bit, curFormat, chunk);
		bit[chunk] = '\0';
	    }
	    if(ss) {
		outputString = R_AllocStringBuffer(strlen(outputString) +
						   strlen(ss) + 1, &outbuff);
		strcat(outputString, ss);
	    } else {
		outputString = R_AllocStringBuffer(strlen(outputString) +
						   strlen(bit) + 1, &outbuff);
		strcat(outputString, bit);
	    }
	}  /* end for ( each chunk ) */

	if(ns == 0) { /* may have adjusted maxlen now ... */
	    PROTECT(ans = allocVector(STRSXP, maxlen));
	    nprotect++;
	}
	SET_STRING_ELT(ans, ns, mkCharCE(outputString,
					 use_UTF8 ? CE_UTF8 : CE_NATIVE));
    } /* end for(ns ...) */

    UNPROTECT(nprotect);
    R_FreeStringBufferL(&outbuff);
    return ans;
}
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 2001--2015 The R Core Team
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Pulic License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 */

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#include <Defn.h>
#include <Internal.h>

#define isRaw(x) (TYPEOF(x) == RAWSXP)

/* charToRaw works at byte level, ignores encoding */
SEXP attribute_hidden do_charToRaw(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, x = CAR(args);
    int nc;

    checkArity(op, args);
    if (!isString(x) || LENGTH(x) == 0)
	error(_("argument must be a character vector of length 1"));
    if (LENGTH(x) > 1)
	warning(_("argument should be a character vector of length 1\nall but the first element will be ignored"));
    nc = LENGTH(STRING_ELT(x, 0));
    ans = allocVector(RAWSXP, nc);
    if (nc) memcpy(RAW(ans), CHAR(STRING_ELT(x, 0)), nc);
    return ans;
}

/* <UTF8>  rawToChar should work at byte level */
SEXP attribute_hidden do_rawToChar(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, x = CAR(args);

    checkArity(op, args);
    if (!isRaw(x))
	error(_("argument 'x' must be a raw vector"));
    int multiple = asLogical(CADR(args));
    if (multiple == NA_LOGICAL)
	error(_("argument 'multiple' must be TRUE or FALSE"));
    if (multiple) {
	R_xlen_t i, nc = XLENGTH(x);
	char buf[2];
	buf[1] = '\0';
	PROTECT(ans = allocVector(STRSXP, nc));
	for (i = 0; i < nc; i++) {
	    buf[0] = (char) RAW(x)[i];
	    SET_STRING_ELT(ans, i, mkChar(buf));
	}
	/* do we want to copy e.g. names here? */
    } else {
	int i, j, nc = LENGTH(x);
	/* String is not necessarily 0-terminated and may contain nuls.
	   Strip trailing nuls */
	for (i = 0, j = -1; i < nc; i++) if(RAW(x)[i]) j = i;
	nc = j + 1;
	PROTECT(ans = allocVector(STRSXP, 1));
	SET_STRING_ELT(ans, 0,
		       mkCharLenCE((const char *)RAW(x), j+1, CE_NATIVE));
    }
    UNPROTECT(1);
    return ans;
}


SEXP attribute_hidden do_rawShift(SEXP call, SEXP op, SEXP args, SEXP env)
{
    checkArity(op, args);

    SEXP ans, x = CAR(args);
    int shift = asInteger(CADR(args));

    if (!isRaw(x))
	error(_("argument 'x' must be a raw vector"));
    if (shift == NA_INTEGER || shift < -8 || shift > 8)
	error(_("argument 'shift' must be a small integer"));
    PROTECT(ans = duplicate(x));
    if (shift > 0)
	for (R_xlen_t i = 0; i < XLENGTH(x); i++)
	    RAW(ans)[i] <<= shift;
    else
	for (R_xlen_t i = 0; i < XLENGTH(x); i++)
	    RAW(ans)[i] >>= (-shift);
    UNPROTECT(1);
    return ans;
}

SEXP attribute_hidden do_rawToBits(SEXP call, SEXP op, SEXP args, SEXP env)
{
    checkArity(op, args);

    SEXP ans, x = CAR(args);
    R_xlen_t i, j = 0;
    unsigned int tmp;

    if (!isRaw(x))
	error(_("argument 'x' must be a raw vector"));
    PROTECT(ans = allocVector(RAWSXP, 8*XLENGTH(x)));
    for (i = 0; i < XLENGTH(x); i++) {
	tmp = (unsigned int) RAW(x)[i];
	for (int k = 0; k < 8; k++, tmp >>= 1)
	    RAW(ans)[j++] = tmp & 0x1;
    }
    UNPROTECT(1);
    return ans;
}

SEXP attribute_hidden do_intToBits(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, x;
    R_xlen_t i, j = 0;
    unsigned int tmp;

    checkArity(op, args);
    PROTECT(x = coerceVector(CAR(args), INTSXP));
    if (!isInteger(x))
	error(_("argument 'x' must be an integer vector"));
    PROTECT(ans = allocVector(RAWSXP, 32*XLENGTH(x)));
    for (i = 0; i < XLENGTH(x); i++) {
	tmp = (unsigned int) INTEGER(x)[i];
	for (int k = 0; k < 32; k++, tmp >>= 1)
	    RAW(ans)[j++] = tmp & 0x1;
    }
    UNPROTECT(2);
    return ans;
}

SEXP attribute_hidden do_packBits(SEXP call, SEXP op, SEXP args, SEXP env)
{
    checkArity(op, args);
    SEXP ans, x = CAR(args), stype = CADR(args);
    Rboolean useRaw;
    R_xlen_t i, len = XLENGTH(x), slen;
    int fac;

    if (TYPEOF(x) != RAWSXP && TYPEOF(x) != LGLSXP && TYPEOF(x) != INTSXP)
	error(_("argument 'x' must be raw, integer or logical"));
    if (!isString(stype)  || LENGTH(stype) != 1)
	error(_("argument '%s' must be a character string"), "type");
    useRaw = strcmp(CHAR(STRING_ELT(stype, 0)), "integer");
    fac = useRaw ? 8 : 32;
    if (len% fac)
	error(_("argument 'x' must be a multiple of %d long"), fac);
    slen = len/fac;
    PROTECT(ans = allocVector(useRaw ? RAWSXP : INTSXP, slen));
    for (i = 0; i < slen; i++)
	if (useRaw) {
	    Rbyte btmp = 0;
	    for (int k = 7; k >= 0; k--) {
		btmp <<= 1;
		if (isRaw(x))
		    btmp |= RAW(x)[8*i + k] & 0x1;
		else if (isLogical(x) || isInteger(x)) {
		    int j = INTEGER(x)[8*i+k];
		    if (j == NA_INTEGER)
			error(_("argument 'x' must not contain NAs"));
		    btmp |= j & 0x1;
		}
	    }
	    RAW(ans)[i] = btmp;
	} else {
	    unsigned int itmp = 0;
	    for (int k = 31; k >= 0; k--) {
		itmp <<= 1;
		if (isRaw(x))
		    itmp |= RAW(x)[32*i + k] & 0x1;
		else if (isLogical(x) || isInteger(x)) {
		    int j = INTEGER(x)[32*i+k];
		    if (j == NA_INTEGER)
			error(_("argument 'x' must not contain NAs"));
		    itmp |= j & 0x1;
		}
	    }
	    INTEGER(ans)[i] = (int) itmp;
	}
    UNPROTECT(1);
    return ans;
}

static int mbrtoint(int *w, const char *s)
{
    unsigned int byte;
    byte = *((unsigned char *)s);

    if (byte == 0) {
	*w = 0;
	return 0;
    } else if (byte < 0xC0) {
	*w = (int) byte;
	return 1;
    } else if (byte < 0xE0) {
	if (!s[1]) return -2;
	if ((s[1] & 0xC0) == 0x80) {
	    *w = (int) (((byte & 0x1F) << 6) | (s[1] & 0x3F));
	    return 2;
	} else return -1;
    } else if (byte < 0xF0) {
	if (!s[1] || !s[2]) return -2;
	if (((s[1] & 0xC0) == 0x80) && ((s[2] & 0xC0) == 0x80)) {
	    *w = (int) (((byte & 0x0F) << 12)
			| ((s[1] & 0x3F) << 6) | (s[2] & 0x3F));
	    byte = *w;
	    if (byte >= 0xD800 && byte <= 0xDFFF) return -1; /* surrogate */
	    if (byte == 0xFFFE || byte == 0xFFFF) return -1;
	    return 3;
	} else return -1;
    } else if (byte < 0xF8) {
	if (!s[1] || !s[2] || !s[3]) return -2;
	if (((s[1] & 0xC0) == 0x80)
	    && ((s[2] & 0xC0) == 0x80)
	    && ((s[3] & 0xC0) == 0x80)) {
	    *w = (int) (((byte & 0x07) << 18)
			| ((s[1] & 0x3F) << 12)
			| ((s[2] & 0x3F) << 6)
			| (s[3] & 0x3F));
	    byte = *w;
	    return 4;
	} else return -1;
    } else if (byte < 0xFC) {
	if (!s[1] || !s[2] || !s[3] || !s[4]) return -2;
	if (((s[1] & 0xC0) == 0x80)
	    && ((s[2] & 0xC0) == 0x80)
	    && ((s[3] & 0xC0) == 0x80)
	    && ((s[4] & 0xC0) == 0x80)) {
	    *w = (int) (((byte & 0x03) << 24)
			| ((s[1] & 0x3F) << 18)
			| ((s[2] & 0x3F) << 12)
			| ((s[3] & 0x3F) << 6)
			| (s[4] & 0x3F));
	    byte = *w;
	    return 5;
	} else return -1;
    } else {
	if (!s[1] || !s[2] || !s[3] || !s[4] || !s[5]) return -2;
	if (((s[1] & 0xC0) == 0x80)
	    && ((s[2] & 0xC0) == 0x80)
	    && ((s[3] & 0xC0) == 0x80)
	    && ((s[4] & 0xC0) == 0x80)
	    && ((s[5] & 0xC0) == 0x80)) {
	    *w = (int) (((byte & 0x01) << 30)
			| ((s[1] & 0x3F) << 24)
			| ((s[2] & 0x3F) << 18)
			| ((s[3] & 0x3F) << 12)
			| ((s[5] & 0x3F) << 6)
			| (s[5] & 0x3F));
	    byte = *w;
	    return 6;
	} else return -1;
    }
    /* return -2; not reached */
}

SEXP attribute_hidden do_utf8ToInt(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, x = CAR(args);
    int tmp, used = 0; /* -Wall */
    R_xlen_t i, j, nc;

    checkArity(op, args);
    if (!isString(x) || LENGTH(x) == 0)
	error(_("argument must be a character vector of length 1"));
    if (LENGTH(x) > 1)
	warning(_("argument should be a character vector of length 1\nall but the first element will be ignored"));
    if (STRING_ELT(x, 0) == NA_STRING) return ScalarInteger(NA_INTEGER);
    const char *s = CHAR(STRING_ELT(x, 0));
    if (!utf8Valid(s)) return ScalarInteger(NA_INTEGER);
    nc = XLENGTH(STRING_ELT(x, 0)); /* ints will be shorter */
    int *ians = (int *) R_alloc(nc, sizeof(int));
    for (i = 0, j = 0; i < nc; i++) {
	used = mbrtoint(&tmp, s);
	if (used <= 0) break;
	ians[j++] = tmp;
	s += used;
    }
    if (used < 0) error(_("invalid UTF-8 string"));
    ans = allocVector(INTSXP, j);
    if (j) memcpy(INTEGER(ans), ians, sizeof(int) * j);
    return ans;
}

/* based on pcre.c */
static const int utf8_table1[] =
    { 0x7f, 0x7ff, 0xffff, 0x1fffff, 0x3ffffff, 0x7fffffff};
static const int utf8_table2[] = { 0, 0xc0, 0xe0, 0xf0, 0xf8, 0xfc};

static size_t inttomb(char *s, const int wc)
{
    register int i, j;
    unsigned int cvalue = wc;
    char buf[10], *b;

    b = s ? s : buf;
    if (cvalue == 0) {*b = 0; return 0;}
    for (i = 0; i < sizeof(utf8_table1)/sizeof(int); i++)
	if (cvalue <= utf8_table1[i]) break;
    b += i;
    for (j = i; j > 0; j--) {
	*b-- = (char)(0x80 | (cvalue & 0x3f));
	cvalue >>= 6;
    }
    *b = (char)(utf8_table2[i] | cvalue);
    return i + 1;
}

#include <R_ext/RS.h>  /* for Calloc/Free */

SEXP attribute_hidden do_intToUtf8(SEXP call, SEXP op, SEXP args, SEXP env)
{
    SEXP ans, x;
    int multiple;
    size_t used, len;
    char buf[10], *tmp;

    checkArity(op, args);
    PROTECT(x = coerceVector(CAR(args), INTSXP));
    if (!isInteger(x))
	error(_("argument 'x' must be an integer vector"));
    multiple = asLogical(CADR(args));
    if (multiple == NA_LOGICAL)
	error(_("argument 'multiple' must be TRUE or FALSE"));
    if (multiple) {
	R_xlen_t i, nc = XLENGTH(x);
	PROTECT(ans = allocVector(STRSXP, nc));
	for (i = 0; i < nc; i++) {
	    if (INTEGER(x)[i] == NA_INTEGER)
		SET_STRING_ELT(ans, i, NA_STRING);
	    else {
		used = inttomb(buf, INTEGER(x)[i]);
		buf[used] = '\0';
		SET_STRING_ELT(ans, i, mkCharCE(buf, CE_UTF8));
	    }
	}
	/* do we want to copy e.g. names here? */
    } else {
	int i, nc = LENGTH(x);
	Rboolean haveNA = FALSE;
	/* Note that this gives zero length for input '0', so it is omitted */
	for (i = 0, len = 0; i < nc; i++) {
	    if (INTEGER(x)[i] == NA_INTEGER) { haveNA = TRUE; break; }
	    len += inttomb(NULL, INTEGER(x)[i]);
	}
	if (haveNA) {
	    PROTECT(ans = allocVector(STRSXP, 1));
	    SET_STRING_ELT(ans, 0, NA_STRING);
	    UNPROTECT(2);
	    return ans;
	}
	if (len >= 10000) {
	    tmp = Calloc(len+1, char);
	} else {
	    R_CheckStack2(len+1);
	    tmp = alloca(len+1); tmp[len] = '\0';
	}
	for (i = 0, len = 0; i < nc; i++) {
	    used = inttomb(buf, INTEGER(x)[i]);
	    strncpy(tmp + len, buf, used);
	    len += used;
	}
	PROTECT(ans = allocVector(STRSXP, 1));
	SET_STRING_ELT(ans, 0, mkCharLenCE(tmp, (int) len, CE_UTF8));
	if(len >= 10000) Free(tmp);
    }
    UNPROTECT(2);
    return ans;
}
/*
 *  R : A Computer Language for Statistical Data Analysis
 *  Copyright (C) 2005-2014 The R Core Team
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, a copy is available at
 *  https://www.R-project.org/Licenses/
 */

/*  This file was contributed by Ei-ji Nakama.
 *  It exports locale2charset for use in gram.y, and rlocale.c on macOS.
 *  And sysutils.c, grDevices/src/devPS.c
 */

/* setlocale(LC_CTYPE,NULL) to encodingname cf nl_langinfo(LC_CTYPE) */


/*********************************************************************
 * usage : char *locale2charset(const char *locale)                  *
 * return : ASCII - default and undefine                             *
 *          other - encodename                                       *
 *                                                                   *
 *         cc -o localecharset -DDEBUG_TEST=1  localecharset.c       *
 *                                or                                 *
 *         cc -o localecharset -DDEBUG_TEST=2  localecharset.c       *
 *********************************************************************/

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#ifdef DEBUG_TEST
#define SPRINT(x) printf("%6d:" #x "=%s\n", __LINE__, x)
#define DPRINT(x) printf("%6d:" #x "=%d\n", __LINE__, x)
//#define HAVE_STRING_H
#endif

#include <string.h>
#include <memory.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

//#include <rlocale.h> /* To get the correct linkage for locale2charset */

/* name_value struct */
typedef struct {
    char *name;
    char *value;
} name_value;


#ifndef __APPLE__
/*
 * codeset name defined.
 *
 cat /usr/X11R6/lib/X11/locale/locale.alias | \
 sed -e '/#.*$/d' -e 's/://' | \
 awk '{gsub(/^[^.]+\./, "", $2);
       $2=toupper($2);
       gsub(/^EUC/, "EUC-",$2);
       gsub(/^BIG5HKSCS$/, "BIG5-HKSCS",$2);
       if (($2!="")&&(!system("iconv --list|grep " $2 ))) print $2
       }' | \
       sed -e '/\/$/d' | \
       sort | uniq | \
       awk '{NAME=$1;gsub(/-/,"_",NAME);
	     printf("static  const   char    ENC_%-20s\"%s\";\n",
	     NAME "[]=" ,
	     $1)}'
  */
static  char    ENC_ARMSCII_8[]=        "ARMSCII-8";
static  char    ENC_BIG5[]=             "BIG5";
static  char    ENC_BIG5_HKSCS[]=       "BIG5-HKSCS";
static  char    ENC_C[]=                "C";
static  char    ENC_CP1251[]=           "CP1251";
static  char    ENC_CP1255[]=           "CP1255";
static  char    ENC_CP1256[]=           "CP1256";
static  char    ENC_EUC_CN[]=           "EUC-CN";
static  char    ENC_EUC_JP[]=           "EUC-JP";
static  char    ENC_EUC_KR[]=           "EUC-KR";
static  char    ENC_EUC_TW[]=           "EUC-TW";
static  char    ENC_GB2312[]=           "GB2312";
static  char    ENC_GBK[]=              "GBK";
static  char    ENC_GEORGIAN_ACADEMY[]= "GEORGIAN-ACADEMY";
/* static  char    ENC_GEORGIAN_PS[]=      "GEORGIAN-PS"; */
/* static  char    ENC_ISIRI_3342[]=       "ISIRI-3342"; */
static  char    ENC_ISO8859_1[]=        "ISO8859-1";
static  char    ENC_ISO8859_10[]=       "ISO8859-10";
static  char    ENC_ISO8859_11[]=       "ISO8859-11";
static  char    ENC_ISO8859_13[]=       "ISO8859-13";
/* static  char    ENC_ISO8859_14[]=       "ISO8859-14"; */
static  char    ENC_ISO8859_15[]=       "ISO8859-15";
static  char    ENC_ISO8859_2[]=        "ISO8859-2";
static  char    ENC_ISO8859_3[]=        "ISO8859-3";
/* static  char    ENC_ISO8859_4[]=        "ISO8859-4"; */
static  char    ENC_ISO8859_5[]=        "ISO8859-5";
static  char    ENC_ISO8859_6[]=        "ISO8859-6";
static  char    ENC_ISO8859_7[]=        "ISO8859-7";
static  char    ENC_ISO8859_8[]=        "ISO8859-8";
static  char    ENC_ISO8859_9[]=        "ISO8859-9";
static  char    ENC_KOI8_R[]=           "KOI8-R";
static  char    ENC_KOI8_U[]=           "KOI8-U";
/* static  char    ENC_SJIS[]=             "SJIS"; */
static  char    ENC_TCVN[]=             "TCVN";
/* static  char    ENC_TIS620[]=           "TIS620"; */
static  char    ENC_UTF_8[]=            "UTF-8";
/* static  char    ENC_VISCII[]=           "VISCII"; */

/*
   # charset getscript. iconv list output line is backslant.
 cat /usr/X11R6/lib/X11/locale/locale.alias | \
 sed -e '/#.*$/d ; /^[A-z]*\./d' -e 's/://' | \
 awk '{gsub(/^[^.]+\./, "", $2);
       $2=toupper($2);
       gsub(/^EUC/, "EUC-",$2);
       gsub(/^BIG5HKSCS$/, "BIG5-HKSCS",$2);
       NAME=$2;
       gsub(/\xe7/,"\"\"\\xe7\"\"",$1);
       gsub(/\xe5/,"\"\"\\xe5\"\"",$1);
       gsub(/-/, "_",NAME);
       NAME="ENC_" NAME;
       if (($2!="")&&(!system("iconv --list|grep " $2 ))) print  $1 " " NAME
    }' | \
 sed -e '/\/$/d' | \
 sort -k 1 | uniq | \
 awk '{printf ("    {%-34s%s},\n", "\"" $1 "\",", $2)}'
*/

static const name_value guess[] = {
    {"Cextend",                        ENC_ISO8859_1},
    {"English_United-States.437",      ENC_C},
    {"ISO-8859-1",                     ENC_ISO8859_1},
    {"ISO8859-1",                      ENC_ISO8859_1},
    {"Japanese-EUC",                   ENC_EUC_JP},
    {"Jp_JP",                          ENC_EUC_JP},
    {"POSIX",                          ENC_C},
    {"POSIX-UTF2",                     ENC_C},
    {"aa_DJ",                          ENC_ISO8859_1},
    {"aa_ER",                          ENC_UTF_8},
    {"aa_ER@saaho",                    ENC_UTF_8},
    {"aa_ET",                          ENC_UTF_8},
    {"af",                             ENC_ISO8859_1},
    {"af_ZA",                          ENC_ISO8859_1},
    {"am",                             ENC_UTF_8},
    {"am_ET",                          ENC_UTF_8},
    {"an_ES",                          ENC_ISO8859_15},
    {"ar",                             ENC_ISO8859_6},
    {"ar_AA",                          ENC_ISO8859_6},
    {"ar_AE",                          ENC_ISO8859_6},
    {"ar_BH",                          ENC_ISO8859_6},
    {"ar_DZ",                          ENC_ISO8859_6},
    {"ar_EG",                          ENC_ISO8859_6},
    {"ar_IN",                          ENC_UTF_8},
    {"ar_IQ",                          ENC_ISO8859_6},
    {"ar_JO",                          ENC_ISO8859_6},
    {"ar_KW",                          ENC_ISO8859_6},
    {"ar_LB",                          ENC_ISO8859_6},
    {"ar_LY",                          ENC_ISO8859_6},
    {"ar_MA",                          ENC_ISO8859_6},
    {"ar_OM",                          ENC_ISO8859_6},
    {"ar_QA",                          ENC_ISO8859_6},
    {"ar_SA",                          ENC_ISO8859_6},
    {"ar_SD",                          ENC_ISO8859_6},
    {"ar_SY",                          ENC_ISO8859_6},
    {"ar_TN",                          ENC_ISO8859_6},
    {"ar_YE",                          ENC_ISO8859_6},
    {"be",                             ENC_CP1251},
    {"be_BY",                          ENC_CP1251},
    {"bg",                             ENC_CP1251},
    {"bg_BG",                          ENC_CP1251},
    {"bn_BD",                          ENC_UTF_8},
    {"bn_IN",                          ENC_UTF_8},
    {"bokm""\xe5""l",                  ENC_ISO8859_1},
    {"bokmal",                         ENC_ISO8859_1},
    {"br",                             ENC_ISO8859_1},
    {"br_FR",                          ENC_ISO8859_1},
    {"br_FR@euro",                     ENC_ISO8859_15},
    {"bs_BA",                          ENC_ISO8859_2},
    {"bulgarian",                      ENC_CP1251},
    {"byn_ER",                         ENC_UTF_8},
    {"c-french.iso88591",              ENC_ISO8859_1},
    {"ca",                             ENC_ISO8859_1},
    {"ca_ES",                          ENC_ISO8859_1},
    {"ca_ES@euro",                     ENC_ISO8859_15},
    {"catalan",                        ENC_ISO8859_1},
    {"chinese-s",                      ENC_EUC_CN},
    {"chinese-t",                      ENC_EUC_TW},
    {"croatian",                       ENC_ISO8859_2},
    {"cs",                             ENC_ISO8859_2},
    {"cs_CS",                          ENC_ISO8859_2},
    {"cs_CZ",                          ENC_ISO8859_2},
    {"cy",                             ENC_ISO8859_1},
    {"cy_GB",                          ENC_ISO8859_1},
    {"cz",                             ENC_ISO8859_2},
    {"cz_CZ",                          ENC_ISO8859_2},
    {"czech",                          ENC_ISO8859_2},
    {"da",                             ENC_ISO8859_1},
    {"da_DK",                          ENC_ISO8859_1},
    {"danish",                         ENC_ISO8859_1},
    {"dansk",                          ENC_ISO8859_1},
    {"de",                             ENC_ISO8859_1},
    {"de_AT",                          ENC_ISO8859_1},
    {"de_AT@euro",                     ENC_ISO8859_15},
    {"de_BE",                          ENC_ISO8859_1},
    {"de_BE@euro",                     ENC_ISO8859_15},
    {"de_CH",                          ENC_ISO8859_1},
    {"de_DE",                          ENC_ISO8859_1},
    {"de_DE@euro",                     ENC_ISO8859_15},
    {"de_LI",                          ENC_ISO8859_1},
    {"de_LI@euro",                     ENC_ISO8859_15},
    {"de_LU",                          ENC_ISO8859_1},
    {"de_LU@euro",                     ENC_ISO8859_15},
    {"deutsch",                        ENC_ISO8859_1},
    {"dutch",                          ENC_ISO8859_1},
    {"eesti",                          ENC_ISO8859_1},
    {"el",                             ENC_ISO8859_7},
    {"el_GR",                          ENC_ISO8859_7},
    {"en",                             ENC_ISO8859_1},
    {"en_AU",                          ENC_ISO8859_1},
    {"en_BW",                          ENC_ISO8859_1},
    {"en_CA",                          ENC_ISO8859_1},
    {"en_DK",                          ENC_ISO8859_1},
    {"en_GB",                          ENC_ISO8859_1},
    {"en_HK",                          ENC_ISO8859_1},
    {"en_IE",                          ENC_ISO8859_1},
    {"en_IE@euro",                     ENC_ISO8859_15},
    {"en_IN",                          ENC_UTF_8},
    {"en_NZ",                          ENC_ISO8859_1},
    {"en_PH",                          ENC_ISO8859_1},
    {"en_SG",                          ENC_ISO8859_1},
    {"en_UK",                          ENC_ISO8859_1},
    {"en_US",                          ENC_ISO8859_1},
    {"en_ZA",                          ENC_ISO8859_1},
    {"en_ZW",                          ENC_ISO8859_1},
    {"es",                             ENC_ISO8859_1},
    {"es_AR",                          ENC_ISO8859_1},
    {"es_BO",                          ENC_ISO8859_1},
    {"es_CL",                          ENC_ISO8859_1},
    {"es_CO",                          ENC_ISO8859_1},
    {"es_CR",                          ENC_ISO8859_1},
    {"es_DO",                          ENC_ISO8859_1},
    {"es_EC",                          ENC_ISO8859_1},
    {"es_ES",                          ENC_ISO8859_1},
    {"es_ES@euro",                     ENC_ISO8859_15},
    {"es_GT",                          ENC_ISO8859_1},
    {"es_HN",                          ENC_ISO8859_1},
    {"es_MX",                          ENC_ISO8859_1},
    {"es_NI",                          ENC_ISO8859_1},
    {"es_PA",                          ENC_ISO8859_1},
    {"es_PE",                          ENC_ISO8859_1},
    {"es_PR",                          ENC_ISO8859_1},
    {"es_PY",                          ENC_ISO8859_1},
    {"es_SV",                          ENC_ISO8859_1},
    {"es_US",                          ENC_ISO8859_1},
    {"es_UY",                          ENC_ISO8859_1},
    {"es_VE",                          ENC_ISO8859_1},
    {"estonian",                       ENC_ISO8859_1},
    {"et",                             ENC_ISO8859_15},
    {"et_EE",                          ENC_ISO8859_15},
    {"eu",                             ENC_ISO8859_1},
    {"eu_ES",                          ENC_ISO8859_1},
    {"eu_ES@euro",                     ENC_ISO8859_15},
    {"eu_FR",                          ENC_ISO8859_1},
    {"eu_FR@euro",                     ENC_ISO8859_15},
    {"fa",                             ENC_UTF_8},
    {"fa_IR",                          ENC_UTF_8},
    {"fi",                             ENC_ISO8859_1},
    {"fi_FI",                          ENC_ISO8859_1},
    {"fi_FI@euro",                     ENC_ISO8859_15},
    {"finnish",                        ENC_ISO8859_1},
    {"fo",                             ENC_ISO8859_1},
    {"fo_FO",                          ENC_ISO8859_1},
    {"fr",                             ENC_ISO8859_1},
    {"fr_BE",                          ENC_ISO8859_1},
    {"fr_BE@euro",                     ENC_ISO8859_15},
    {"fr_CA",                          ENC_ISO8859_1},
    {"fr_CH",                          ENC_ISO8859_1},
    {"fr_FR",                          ENC_ISO8859_1},
    {"fr_FR@euro",                     ENC_ISO8859_15},
    {"fr_LU",                          ENC_ISO8859_1},
    {"fr_LU@euro",                     ENC_ISO8859_15},
    {"fran""\xe7""ais",                ENC_ISO8859_1},
    {"french",                         ENC_ISO8859_1},
    {"ga",                             ENC_ISO8859_1},
    {"ga_IE",                          ENC_ISO8859_1},
    {"ga_IE@euro",                     ENC_ISO8859_15},
    {"galego",                         ENC_ISO8859_1},
    {"galician",                       ENC_ISO8859_1},
    {"gd",                             ENC_ISO8859_1},
    {"gd_GB",                          ENC_ISO8859_1},
    {"german",                         ENC_ISO8859_1},
    {"gez_ER",                         ENC_UTF_8},
    {"gez_ER@abegede",                 ENC_UTF_8},
    {"gez_ET",                         ENC_UTF_8},
    {"gez_ET@abegede",                 ENC_UTF_8},
    {"gl",                             ENC_ISO8859_1},
    {"gl_ES",                          ENC_ISO8859_1},
    {"gl_ES@euro",                     ENC_ISO8859_15},
    {"greek",                          ENC_ISO8859_7},
    {"gu_IN",                          ENC_UTF_8},
    {"gv",                             ENC_ISO8859_1},
    {"gv_GB",                          ENC_ISO8859_1},
    {"he",                             ENC_ISO8859_8},
    {"he_IL",                          ENC_ISO8859_8},
    {"hebrew",                         ENC_ISO8859_8},
    {"hr",                             ENC_ISO8859_2},
    {"hr_HR",                          ENC_ISO8859_2},
    {"hrvatski",                       ENC_ISO8859_2},
    {"hu",                             ENC_ISO8859_2},
    {"hu_HU",                          ENC_ISO8859_2},
    {"hungarian",                      ENC_ISO8859_2},
    {"hy",                             ENC_ARMSCII_8},
    {"hy_AM",                          ENC_ARMSCII_8},
    {"icelandic",                      ENC_ISO8859_1},
    {"id",                             ENC_ISO8859_1},
    {"id_ID",                          ENC_ISO8859_1},
    {"in",                             ENC_ISO8859_1},
    {"in_ID",                          ENC_ISO8859_1},
    {"is",                             ENC_ISO8859_1},
    {"is_IS",                          ENC_ISO8859_1},
    {"iso_8859_1",                     ENC_ISO8859_1},
    {"it",                             ENC_ISO8859_1},
    {"it_CH",                          ENC_ISO8859_1},
    {"it_IT",                          ENC_ISO8859_1},
    {"it_IT@euro",                     ENC_ISO8859_15},
    {"italian",                        ENC_ISO8859_1},
    {"iw",                             ENC_ISO8859_8},
    {"iw_IL",                          ENC_ISO8859_8},
    {"ja",                             ENC_EUC_JP},
    {"ja_JP",                          ENC_EUC_JP},
    {"japan",                          ENC_EUC_JP},
    {"japanese",                       ENC_EUC_JP},
    {"ka",                             ENC_GEORGIAN_ACADEMY},
    {"ka_GE",                          ENC_GEORGIAN_ACADEMY},
    {"kl",                             ENC_ISO8859_1},
    {"kl_GL",                          ENC_ISO8859_1},
    {"kn_IN",                          ENC_UTF_8},
    {"ko",                             ENC_EUC_KR},
    {"ko_KR",                          ENC_EUC_KR},
    {"korean",                         ENC_EUC_KR},
    {"kw",                             ENC_ISO8859_1},
    {"kw_GB",                          ENC_ISO8859_1},
    {"lg_UG",                          ENC_ISO8859_10},
    {"lithuanian",                     ENC_ISO8859_13},
    {"lt",                             ENC_ISO8859_13},
    {"lt_LT",                          ENC_ISO8859_13},
    {"lv",                             ENC_ISO8859_13},
    {"lv_LV",                          ENC_ISO8859_13},
    {"mi",                             ENC_ISO8859_13},
    {"mi_NZ",                          ENC_ISO8859_13},
    {"mk",                             ENC_ISO8859_5},
    {"mk_MK",                          ENC_ISO8859_5},
    {"ml_IN",                          ENC_UTF_8},
    {"mn_MN",                          ENC_UTF_8},
    {"mr_IN",                          ENC_UTF_8},
    {"ms",                             ENC_ISO8859_1},
    {"ms_MY",                          ENC_ISO8859_1},
    {"mt",                             ENC_ISO8859_3},
    {"mt_MT",                          ENC_ISO8859_3},
    {"nb",                             ENC_ISO8859_1},
    {"nb_NO",                          ENC_ISO8859_1},
    {"ne_NP",                          ENC_UTF_8},
    {"nl",                             ENC_ISO8859_1},
    {"nl_BE",                          ENC_ISO8859_1},
    {"nl_BE@euro",                     ENC_ISO8859_15},
    {"nl_NL",                          ENC_ISO8859_1},
    {"nl_NL@euro",                     ENC_ISO8859_15},
    {"nn",                             ENC_ISO8859_1},
    {"nn_NO",                          ENC_ISO8859_1},
    {"no",                             ENC_ISO8859_1},
    {"no@nynorsk",                     ENC_ISO8859_1},
    {"no_NO",                          ENC_ISO8859_1},
    {"norwegian",                      ENC_ISO8859_1},
    {"nynorsk",                        ENC_ISO8859_1},
    {"oc",                             ENC_ISO8859_1},
    {"oc_FR",                          ENC_ISO8859_1},
    {"oc_FR@euro",                     ENC_ISO8859_15},
    {"om_ET",                          ENC_UTF_8},
    {"om_KE",                          ENC_ISO8859_1},
    {"pa_IN",                          ENC_UTF_8},
    {"ph",                             ENC_ISO8859_1},
    {"ph_PH",                          ENC_ISO8859_1},
    {"pl",                             ENC_ISO8859_2},
    {"pl_PL",                          ENC_ISO8859_2},
    {"polish",                         ENC_ISO8859_2},
    {"portuguese",                     ENC_ISO8859_1},
    {"pp",                             ENC_ISO8859_1},
    {"pp_AN",                          ENC_ISO8859_1},
    {"pt",                             ENC_ISO8859_1},
    {"pt_BR",                          ENC_ISO8859_1},
    {"pt_PT",                          ENC_ISO8859_1},
    {"pt_PT@euro",                     ENC_ISO8859_15},
    {"ro",                             ENC_ISO8859_2},
    {"ro_RO",                          ENC_ISO8859_2},
    {"romanian",                       ENC_ISO8859_2},
    {"ru",                             ENC_KOI8_R},
    {"ru_RU",                          ENC_KOI8_R},
    {"ru_UA",                          ENC_KOI8_U},
    {"rumanian",                       ENC_ISO8859_2},
    {"russian",                        ENC_ISO8859_5},
    {"se_NO",                          ENC_UTF_8},
    {"serbocroatian",                  ENC_ISO8859_2},
    {"sh",                             ENC_ISO8859_2},
    {"sh_SP",                          ENC_ISO8859_2},
    {"sh_YU",                          ENC_ISO8859_2},
    {"sid_ET",                         ENC_UTF_8},
    {"sk",                             ENC_ISO8859_2},
    {"sk_SK",                          ENC_ISO8859_2},
    {"sl",                             ENC_ISO8859_2},
    {"sl_SI",                          ENC_ISO8859_2},
    {"slovak",                         ENC_ISO8859_2},
    {"slovene",                        ENC_ISO8859_2},
    {"slovenian",                      ENC_ISO8859_2},
    {"so_DJ",                          ENC_ISO8859_1},
    {"so_ET",                          ENC_UTF_8},
    {"so_KE",                          ENC_ISO8859_1},
    {"so_SO",                          ENC_ISO8859_1},
    {"sp",                             ENC_ISO8859_5},
    {"sp_YU",                          ENC_ISO8859_5},
    {"spanish",                        ENC_ISO8859_1},
    {"sq",                             ENC_ISO8859_2},
    {"sq_AL",                          ENC_ISO8859_2},
    {"sr",                             ENC_ISO8859_5},
    {"sr@cyrillic",                    ENC_ISO8859_5},
    {"sr_SP",                          ENC_ISO8859_2},
    {"sr_YU",                          ENC_ISO8859_5},
    {"sr_YU@cyrillic",                 ENC_ISO8859_5},
    {"st_ZA",                          ENC_ISO8859_1},
    {"sv",                             ENC_ISO8859_1},
    {"sv_FI",                          ENC_ISO8859_1},
    {"sv_FI@euro",                     ENC_ISO8859_15},
    {"sv_SE",                          ENC_ISO8859_1},
    {"sv_SE@euro",                     ENC_ISO8859_15},
    {"swedish",                        ENC_ISO8859_1},
    {"te_IN",                          ENC_UTF_8},
    {"th",                             ENC_ISO8859_11},
    {"th_TH",                          ENC_ISO8859_11},
    {"thai",                           ENC_ISO8859_11},
    {"ti_ER",                          ENC_UTF_8},
    {"ti_ET",                          ENC_UTF_8},
    {"tig_ER",                         ENC_UTF_8},
    {"tl",                             ENC_ISO8859_1},
    {"tl_PH",                          ENC_ISO8859_1},
    {"tr",                             ENC_ISO8859_9},
    {"tr_TR",                          ENC_ISO8859_9},
    {"turkish",                        ENC_ISO8859_9},
    {"uk",                             ENC_KOI8_U},
    {"uk_UA",                          ENC_KOI8_U},
    {"ur",                             ENC_CP1256},
    {"ur_PK",                          ENC_CP1256},
    {"uz_UZ",                          ENC_ISO8859_1},
    {"uz_UZ@cyrillic",                 ENC_UTF_8},
    {"vi",                             ENC_TCVN},
    {"vi_VN",                          ENC_TCVN},
    {"wa",                             ENC_ISO8859_1},
    {"wa_BE",                          ENC_ISO8859_1},
    {"wa_BE@euro",                     ENC_ISO8859_15},
    {"xh_ZA",                          ENC_ISO8859_1},
    {"yi",                             ENC_CP1255},
    {"yi_US",                          ENC_CP1255},
    {"zh_CN",                          ENC_GBK},
    {"zh_HK",                          ENC_BIG5_HKSCS},
    {"zh_SG",                          ENC_GB2312},
    {"zh_TW",                          ENC_BIG5},
    {"zu_ZA",                          ENC_ISO8859_1},
};
static const int guess_count = (sizeof(guess)/sizeof(name_value));
#endif

static const name_value known[] = {
    {"iso88591", "ISO8859-1"},
    {"iso88592", "ISO8859-2"},
    {"iso88593", "ISO8859-3"},
    {"iso88596", "ISO8859-6"},
    {"iso88597", "ISO8859-7"},
    {"iso88598", "ISO8859-8"},
    {"iso88599", "ISO8859-9"},
    {"iso885910", "ISO8859-10"},
    {"iso885913", "ISO8859-13"},
    {"iso885914", "ISO8859-14"},
    {"iso885915", "ISO8859-15"},
    {"cp1251", "CP1251"},
    {"cp1255", "CP1255"},
    {"eucjp", "EUC-JP"},
    {"euckr", "EUC-KR"},
    {"euctw", "EUC-TW"},
    {"georgianps", "GEORGIAN-PS"},
    {"koi8u", "KOI8-U"},
    {"tcvn", "TCVN"},
    {"big5", "BIG5"},
    {"gb2312", "GB2312"},
    {"gb18030", "GB18030"},
    {"gbk", "GBK"},
    {"tis-620", "TIS-620"},
    {"sjis", "SHIFT_JIS"},
    {"euccn", "GB2312"},
    {"big5-hkscs", "BIG5-HKSCS"},
#ifdef __APPLE__
    /* known additional Apple encodings (see locale -a) up to macOS 10.5,
       unlike other systems they correspond directly */
    {"iso8859-1", "ISO8859-1"},
    {"iso8859-2", "ISO8859-2"},
    {"iso8859-4", "ISO8859-4"},
    {"iso8859-7", "ISO8859-7"},
    {"iso8859-9", "ISO8859-9"},
    {"iso8859-13", "ISO8859-13"},
    {"iso8859-15", "ISO8859-15"},
    {"koi8-u", "KOI8-U"},
    {"koi8-r", "KOI8-R"},
    {"pt154", "PT154"},
    {"us-ascii", "ASCII"},
    {"armscii-8", "ARMSCII-8"},
    {"iscii-dev", "ISCII-DEV"},
    {"big5hkscs", "BIG5-HKSCS"},
#endif
};
static const int known_count = (sizeof(known)/sizeof(name_value));


#ifndef __APPLE__
static char* name_value_search(const char *name, const name_value table[],
			       const int table_count)
{
    int min, mid, max;

#if defined(DEBUG_TEST)
    static last;
    DPRINT(last);
    last = 0;
#endif

    min = 0;
    max = table_count - 1;

    if ( 0 > strcmp(name,table[min].name) ||
	 0 < strcmp(name,table[max].name) ) {
#if defined(DEBUG_TEST) && DEBUG_TEST > 1
	DPRINT(strcmp(name, table[min].name));
	DPRINT(strcmp(name, table[max].name));
#endif
	return (NULL);
    }
    while (max >= min) {
#if defined(DEBUG_TEST)
	last++;
#endif
	mid = (min + max) / 2;
#if defined(DEBUG_TEST) && DEBUG_TEST > 1
	SPRINT(table[mid].name);
#endif
	if (0 < strcmp(name,table[mid].name)) {
#if defined(DEBUG_TEST) && DEBUG_TEST > 1
	    DPRINT(strcmp(name, table[mid].name));
#endif
	    min = mid + 1;
	} else if (0 > strcmp(name, table[mid].name)) {
#if defined(DEBUG_TEST) && DEBUG_TEST > 1
	    DPRINT(strcmp(name, table[mid].name));
#endif
	    max = mid - 1;
	} else {
#if defined(DEBUG_TEST) && DEBUG_TEST > 1
	    DPRINT(strcmp(name, table[mid].name));
#endif
	    return(table[mid].value);
	}
    }
    return (NULL);
}
#endif

const char *locale2charset(const char *locale)
{
    static char charset[128];

    char la_loc[128];
    char enc[128], *p;
    int i;
    int  cp;
#ifndef __APPLE__
    char *value;
#endif

    if ((locale == NULL) || (0 == strcmp(locale, "NULL")))
	locale = setlocale(LC_CTYPE,NULL);

    /* in some rare circumstances Darwin may return NULL */
    if (!locale || !strcmp(locale, "C") || !strcmp(locale, "POSIX"))
	return ("ASCII");

    memset(charset,0,sizeof(charset));

    /* separate language_locale.encoding
       NB, under Windows 'locale' may contains dots
     */
    memset(la_loc, 0, sizeof(la_loc));
    memset(enc, 0, sizeof(enc));
    p = strrchr(locale, '.');
    if(p) {
	strncpy(enc, p+1, sizeof(enc)-1);
        enc[sizeof(enc) - 1] = '\0';
	strncpy(la_loc, locale, sizeof(la_loc)-1);
        la_loc[sizeof(la_loc) - 1] = '\0';
	p = strrchr(la_loc, '.');
	if(p) *p = '\0';
    }
    
#ifdef Win32
    /*
      ## PUTTY suggests mapping Windows code pages as
      ## 1250 -> ISO 8859-2: this is WRONG
      ## 1251 -> KOI8-U
      ## 1252 -> ISO 8859-1
      ## 1253 -> ISO 8859-7
      ## 1254 -> ISO 8859-9
      ## 1255 -> ISO 8859-8
      ## 1256 -> ISO 8859-6
      ## 1257 -> ISO 8859-13
    */
    switch(cp = atoi(enc)) {
	/* case 1250: return "ISO8859-2"; */
	/* case 1251: return "KOI8-U"; This is not anywhere near the same */
    case 1252: return "ISO8859-1";
	/*
	  case 1253: return "ISO8859-7";
	  case 1254: return "ISO8859-9";
	  case 1255: return "ISO8859-8";
	  case 1256: return "ISO8859-6";
	*/
    case 1257: return "ISO8859-13";
    default:
	snprintf(charset, 128, "CP%u", cp);
	return charset;
    }
#endif

    /*
     * Assume locales are like en_US[.utf8[@euro]]
     */
    /* cut encoding @hoge  no use.
       for(i=0;enc[i] && enc[i]!='@' && i<sizeof(enc)-1;i++);
       enc[i]='\0';
    */

    /* for AIX */
    if (0 == strcmp(enc, "UTF-8")) strcpy(enc, "utf8");

    if(strcmp(enc, "") && strcmp(enc, "utf8")) {
	for(i = 0; enc[i]; i++) enc[i] = (char) tolower(enc[i]);

	for(i = 0; i < known_count; i++)
	    if (0 == strcmp(known[i].name,enc)) return known[i].value;

	/* cut encoding old linux cp- */
	if (0 == strncmp(enc, "cp-", 3)){
	    snprintf(charset, 128, "CP%s", enc+3);
	    return charset;
	}
	/* cut encoding IBM ibm- */
	if (0 == strncmp(enc, "ibm", 3)){
	    cp = atoi(enc + 3);
	    snprintf(charset, 128, "IBM-%d", abs(cp));
	    /* IBM-[0-9]+ case */
	    if(cp != 0) return charset;
	    /* IBM-eucXX case */
	    strncpy(charset, (enc[3] == '-') ? enc+4: enc+3, sizeof(charset));
            charset[sizeof(charset) - 1] = '\0';
	    if(strncmp(charset, "euc", 3)) {
		if (charset[3] != '-') {
		    for(i = (int) strlen(charset)-3; 0 < i; i--)
			charset[i+1] = charset[i];
		    charset[3] = '-';
		}
		for(i = 0; charset[i]; i++)
		    charset[i] = (char) toupper(charset[i]);
