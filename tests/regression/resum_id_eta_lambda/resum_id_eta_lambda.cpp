#include "resum_id_eta_lambda.h"

crane::obj Function::Id_IFun(crane::obj e) { return e; }

crane::obj Function::Cat_IFun(IFun<crane::obj, crane::obj> f1,
                              IFun<crane::obj, crane::obj> f2, crane::obj e) {
  return f2(f1(e));
}

crane::obj Function::Case_sum1(IFun<crane::obj, crane::obj> x,
                               IFun<crane::obj, crane::obj> x0, crane::obj x1) {
  return Function::case_sum1(
      std::move(x), std::move(x0),
      crane::any_cast<Sum1<crane::obj, crane::obj, crane::obj>>(x1));
}

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}

crane::obj Function::Inr_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inr1(x);
}
