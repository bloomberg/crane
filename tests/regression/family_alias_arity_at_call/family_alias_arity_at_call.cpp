#include "family_alias_arity_at_call.h"

crane::obj Function::Id_IFun(crane::obj e) { return e; }

crane::obj Function::Cat_IFun(IFun<crane::obj, crane::obj> f1,
                              IFun<crane::obj, crane::obj> f2, crane::obj e) {
  return f2(f1(e));
}

crane::obj Function::Inr_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inr1(x);
}
