#include "program_fixpoint.h"

List<unsigned int> ProgFix::interleave_func(
    const SigT<List<unsigned int>, List<unsigned int>> &x) {
  List<unsigned int> l1 = x.projT1();
  List<unsigned int> l2 = x.projT2();
  std::function<List<unsigned int>(List<unsigned int>, List<unsigned int>)>
      interleave0 = [](List<unsigned int> l3, List<unsigned int> l4) {
        Sig<SigT<List<unsigned int>, List<unsigned int>>> y =
            Sig<SigT<List<unsigned int>, List<unsigned int>>>::exist(
                SigT<List<unsigned int>, List<unsigned int>>::existt(l3, l4));
        return interleave_func([=]() mutable {
          auto &[x0] = std::get<typename Sig<
              SigT<List<unsigned int>, List<unsigned int>>>::Exist>(y.v_mut());
          return x0;
        }());
      };
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v_mut())) {
    return l2;
  } else {
    auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l1.v_mut());
    return List<unsigned int>::cons(std::move(a0),
                                    interleave0(std::move(l2), *a1));
  }
}

List<unsigned int> ProgFix::interleave(List<unsigned int> l1,
                                       List<unsigned int> l2) {
  return interleave_func(SigT<List<unsigned int>, List<unsigned int>>::existt(
      std::move(l1), std::move(l2)));
}
