#include <program_fixpoint.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> ProgFix::interleave_func(
    const std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                               std::shared_ptr<List<unsigned int>>>> &x) {
  std::shared_ptr<List<unsigned int>> l1 = x->projT1();
  std::shared_ptr<List<unsigned int>> l2 = x->projT2();
  std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>, std::shared_ptr<List<unsigned int>>)>
      interleave0 = [](std::shared_ptr<List<unsigned int>> l3,
                       std::shared_ptr<List<unsigned int>> l4) {
        std::shared_ptr<
            Sig<std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>>>>>
            y = Sig<
                std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>>>>::
                exist(
                    SigT<std::shared_ptr<List<unsigned int>>,
                         std::shared_ptr<List<unsigned int>>>::existt(l3, l4));
        return interleave_func([&]() {
          const auto &[d_x] = std::get<typename Sig<std::shared_ptr<
              SigT<std::shared_ptr<List<unsigned int>>,
                   std::shared_ptr<List<unsigned int>>>>>::Exist>(y->v());
          return d_x;
        }());
      };
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l1->v())) {
    return l2;
  } else {
    if (l1.use_count() == 1) {
      auto &_rf = std::get<typename List<unsigned int>::Cons>(l1->v_mut());
      unsigned int x0 = std::move(_rf.d_a0);
      std::shared_ptr<List<unsigned int>> xs = std::move(_rf.d_a1);
      _rf.d_a0 = std::move(x0);
      _rf.d_a1 = std::move(interleave0)(l2, xs);
      return l1;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l1->v());
      return List<unsigned int>::cons(d_a0, interleave0(l2, d_a1));
    }
  }
}

std::shared_ptr<List<unsigned int>>
ProgFix::interleave(std::shared_ptr<List<unsigned int>> l1,
                    std::shared_ptr<List<unsigned int>> l2) {
  return interleave_func(
      SigT<std::shared_ptr<List<unsigned int>>,
           std::shared_ptr<List<unsigned int>>>::existt(l1, l2));
}
