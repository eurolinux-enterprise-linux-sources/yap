typedef struct{
  UInt		    ssize;
  UInt		    tsize;
  int		   (*cancel)(int thread);
} thread_attr;

Int STD_PROTO(Yap_thread_self,(void));
int STD_PROTO(Yap_get_thread_ref_count,(int));
void STD_PROTO(Yap_set_thread_ref_count,(int,int));
CELL STD_PROTO(Yap_thread_create_engine,(thread_attr *));
Int STD_PROTO(Yap_thread_attach_engine,(int));
Int STD_PROTO(Yap_thread_detach_engine,(int));
Int STD_PROTO(Yap_thread_destroy_engine,(int));

