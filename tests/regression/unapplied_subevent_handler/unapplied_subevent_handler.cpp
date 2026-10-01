#include "unapplied_subevent_handler.h"

crane::obj Function::Id_IFun(crane::obj e) { return e; }

crane::obj Function::Cat_IFun(IFun<crane::obj, crane::obj> f1,
                              IFun<crane::obj, crane::obj> f2, crane::obj e) {
  return f2(f1(e));
}

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}
