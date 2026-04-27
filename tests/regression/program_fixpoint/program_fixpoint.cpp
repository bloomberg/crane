#include <program_fixpoint.h>

__attribute__((pure)) List<unsigned int> ProgFix::interleave_func(
    const SigT<List<unsigned int>, List<unsigned int>> &x) {
  List<unsigned int> l1 = x.projT1();
  List<unsigned int> l2 = x.projT2();
  std::function<List<unsigned int>(List<unsigned int>, List<unsigned int>)>
      interleave0 = [](List<unsigned int> l3, List<unsigned int> l4) {
        Sig<SigT<List<unsigned int>, List<unsigned int>>> y =
            Sig<SigT<List<unsigned int>, List<unsigned int>>>::exist(
                SigT<List<unsigned int>, List<unsigned int>>::existt(l3, l4));
        return interleave_func([=]() mutable {
          const auto &[d_x] = std::get<typename Sig<
              SigT<List<unsigned int>, List<unsigned int>>>::Exist>(y.v());
          return d_x;
        }());
      };
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
    return l2;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l1.v());
    return List<unsigned int>::cons(d_a0, interleave0(l2, *(d_a1)));
  }
}

__attribute__((pure)) List<unsigned int>
ProgFix::interleave(List<unsigned int> l1, List<unsigned int> l2) {
  return interleave_func(
      SigT<List<unsigned int>, List<unsigned int>>::existt(l1, l2));
}
