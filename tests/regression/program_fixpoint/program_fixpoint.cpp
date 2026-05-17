#include "program_fixpoint.h"

List<uint64_t>
ProgFix::interleave_func(const SigT<List<uint64_t>, List<uint64_t>> &x) {
  List<uint64_t> l1 = x.projT1();
  List<uint64_t> l2 = x.projT2();
  std::function<List<uint64_t>(List<uint64_t>, List<uint64_t>)> interleave0 =
      [](List<uint64_t> l3, List<uint64_t> l4) {
        Sig<SigT<List<uint64_t>, List<uint64_t>>> y =
            Sig<SigT<List<uint64_t>, List<uint64_t>>>::exist(
                SigT<List<uint64_t>, List<uint64_t>>::existt(l3, l4));
        return interleave_func([=]() mutable {
          auto &[x0] = y;
          return x0;
        }());
      };
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v_mut())) {
    return l2;
  } else {
    auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v_mut());
    return List<uint64_t>::cons(std::move(a0), interleave0(std::move(l2), *a1));
  }
}

List<uint64_t> ProgFix::interleave(List<uint64_t> l1, List<uint64_t> l2) {
  return interleave_func(SigT<List<uint64_t>, List<uint64_t>>::existt(
      std::move(l1), std::move(l2)));
}
