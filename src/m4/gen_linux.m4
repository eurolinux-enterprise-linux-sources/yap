divert(-1)  # don t output this trash to C
# Preprocessor for i386 linux
# a macro to get the hd of a list
define(m4_hd,`ifelse(index(`$1',`,'),-1,`substr(`$1',1,eval(len(`$1')-2))',dnl
`substr(`$1',1,decr(index(`$1',`,')))')')
# a macro to get the tail of a list
define(m4_tl,`ifelse(index(`$1',`,'),-1,`',dnl
`(substr(`$1',incr(index(`$1',`,')))')')

#macros to split a string
define(substr_up_to,`substr($1,0,index($1,$2))')
define(substr_after,`substr($1,incr(index($1,$2)))')

# a macro to iterate over members of a list
define(`foreach',dnl
`pushdef(`$1',m4_hd(`$2'))_foreach(`$1',m4_tl(`$2'),`$3')popdef(`$1')')
define(`_foreach',`$3'`ifelse($2,`',,dnl
`define(`$1',m4_hd($2))_foreach(`$1',m4_tl(`$2'),`$3')')')

define(`m4_rev',`ifelse($#,0,,$#,1,``$1'',`m4_rev(shift($@)),`$1'')')
# same as above but backwards
define(`foreachb',`foreach(`$1',(m4_rev$2),`$3')')

# macros to process an absmi definition
define(defami, `define(`m4_i_of',m4_opcode_size)'`define(`m4_ami_args',(shift($*)))'
 `$1:ifelse($2,`',`',
    `foreach(`argspec',(shift($*)),`m4_arg(substr_up_to(argspec,:),substr_after(argspec,:))')')m4_redef(InstructionSize,m4_i_of)')

define(endami,
`foreach(`argspec',m4_ami_args,`m4_endami(substr_up_to(argspec,:))')'`#undef InstructionSize')


define(m4_endami,`ifelse($1,,,#undef $1
)')

define(m4_arg,`m4_redef($1,(*(($2 *) (S_P+m4_i_of))))define(`m4_i_of',eval(m4_i_of+m4_$2_size))')


define(m4_redef,`
`#define' $1 $2')

#define a multiple push operation
define(multiple_push,`define(`m4_i',eval($#-1))$1 -= m4_i foreach(`m4arg',(shift($*)),`m4_push1($1,`m4arg')')')

define(m4_push1,`define(`m4_i',eval(m4_i-1))ifelse(m4arg,dummy,,`;
	$1[m4_i] = (CELL) m4arg ')')

define(m4_n_args,`define(`m4_n',$#)')


#define a multiple pop operation
define(multiple_pop,`define(`m4_i',0)foreachb(`m4arg',(shift($*)),`m4_pop1($1)')$1 += m4_i')

define(multiple_restore,`define(`m4_i',0)foreachb(`m4arg',(shift($*)),`m4_restore1($1)')')

define(multiple_shorten,`define(`m4_i',-1)foreach(`m4arg',(shift($*)),`m4_shorten1($1)')')


define(m4_pop1,`ifelse(m4arg,dummy,,`m4arg = (typeof(m4arg)) $1[m4_i];
	')define(`m4_i',eval(m4_i+1))')

define(m4_restore1,`ifelse(m4arg,dummy,,`m4arg = (typeof(m4arg)) $1[m4_i];
	')define(`m4_i',eval(m4_i+1))')

define(m4_shorten1,`ifelse(m4arg,dummy,,`m4arg = (typeof(m4arg)) $1[m4_i];
	')define(`m4_i',eval(m4_i-1))')

# these are machine dependent
define(m4_reg_size,2)
define(m4_small_size,2)
define(m4_long_size,4)
define(m4_opcode_size,2)

define(ShadowRegister,`
define(shadow_$1)
#define LoadShadow_$1	S_$1 = (typeof(S_$1)) $1;
#define StoreShadow_$1  $1 = (typeof($1))S_$1;
')

define(ShadowRegisterDeclarations,
`ifdef(shadow_P,,`    register char *S_P;
')'
`ifdef(shadow_Y,,`    register CELL *S_Y;
')
')

define(DerefA, dnl (ptr,NonVarCase,VarCase) 
``  {
	register CELL *VarValue = (CELL *)$1, NonVarValue;
	while(1) {
	   if(IsVarTerm(NonVarValue = *VarValue) ) {
	    	if(NonVarValue == (CELL) VarValue) {
			$3;
			break;
		}
	    	VarValue = (CELL *) NonVarValue;
	   } else {
		$2;
      		break;
	   }
	}
    }'')


define(DerefD, dnl (data,NonVarCase,VarCase)
  ``{	
	register CELL *VarValue, NonVarValue=(CELL) $1;
	while(1) {
	    if(IsVarTerm(NonVarValue)) {
	        NonVarValue = *(VarValue = (CELL *) NonVarValue);
	        if(NonVarValue == (CELL) VarValue) {
		  $3;
		  break;
		}
	    } else {
		$2;
		break;
	    }
	}
    }'')

define(DerefD1, dnl (data,NonVarCase,VarCase)
``    {
	register CELL *VarValue1, NonVarValue1=(CELL) $1;
	while(1) {
	   if(IsVarTerm(NonVarValue1)) {
	     NonVarValue1 = *(VarValue1 = (CELL *) NonVarValue1);
	     if(NonVarValue1 == (CELL) VarValue1) {
		$3;
		break;
	      }
	   } else {
		$2;
		break;
	   }
	}
    }'')

define(DerefI, dnl (data,NonVarCase,VarCase)
  ``{	
	register CELL *VarValue;
	I_R=(CELL) $1;
	while(1) {
	  if(IsVarTerm(I_R)) {
	    	I_R = *(VarValue = (CELL *) I_R);
	    	if(I_R == (CELL) VarValue) {
			$3;
			break;
	    	}
	   }
	  else { $2; break; }
	}
    }'')

divert

#define Y YENV

ShadowRegister(P)
ShadowRegister(Y)


#define shadow_all() \
	TestCount = 0; \
	LoadShadow_P; \
	LoadShadow_Y; \

#define unshadow_all() \
	StoreShadow_P; \
	StoreShadow_Y;

#ifndef LoadShadow_CP
#define S_CP CP
#endif

#ifndef LoadShadow_ENV
#define S_ENV ENV
#endif

#ifndef LoadShadow_B
#define S_B B
#endif

#ifndef LoadShadow_H
#define S_H H
#endif

#ifndef LoadShadow_TR
#define S_TR TR
#endif

#ifndef LoadShadow_N
#define S_N N
#endif

#ifndef LoadShadow_BH
#define LoadShadow_BH(X) HB = (CELL *) X
#define S_BH  HB
#endif

#ifndef LoadShadow_S
#define LoadShadow_S()
#define S_S	S
#endif



#define CHECK(B) if(--TestCount <= 0) { TestCount=10; B }
#define ENSURECHECK() TestCount=1

#define MACHINE_SPECIFIC_MACROS

#define EFAIL  		asm volatile ("jmp FAIL" : : )
#define UFAIL  		asm volatile ("jmp UFAIL" : : )
#define SaveSP(X) 	asm volatile ("movl %%esp,%0\n\tmovl %%ebp,_SAVEBP" : "=rm"(X) : )
#define RestoreSP(X)	asm volatile ("movl %0,%%esp\n\tmovl _SAVEBP,%%ebp" : : "r" (X))
#define push2(X,Y)	asm volatile ("pushl %0\n\tpushl %1" : :  "r" (X) , "r" (Y) )
#define stack_top(X)	asm volatile ("popl %0\n\tpushl %0" :  "=r" (X) : )
#define push(X)		asm volatile ("pushl %0" : :  "r" (X)  )
#define pop2(X,Y)	asm volatile ("popl %0\n\tpopl %1":  "=r" (Y), "=r" (X) :)
#define add_sp(N)	asm volatile ("addl %0,%%esp": : "r" (N))




#define small	short
#define reg	short

