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
        return interleave_func(std::visit(
            Overloaded{[](const typename Sig<std::shared_ptr<
                              SigT<std::shared_ptr<List<unsigned int>>,
                                   std::shared_ptr<List<unsigned int>>>>>::Exist
                              &_args)
                           -> std::shared_ptr<
                               SigT<std::shared_ptr<List<unsigned int>>,
                                    std::shared_ptr<List<unsigned int>>>> {
              return _args.d_x;
            }},
            y->v()));
      };
  if (l1.use_count() == 1 && l1->v().index() == 1) {
    auto &_rf = std::get<1>(l1->v_mut());
    unsigned int x0 = std::move(_rf.d_a0);
    std::shared_ptr<List<unsigned int>> xs = std::move(_rf.d_a1);
    _rf.d_a0 = std::move(x0);
    _rf.d_a1 = std::move(interleave0)(l2, xs);
    return l1;
  } else {
    return std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil &)
                       -> std::shared_ptr<List<unsigned int>> { return l2; },
                   [&](const typename List<unsigned int>::Cons &_args)
                       -> std::shared_ptr<List<unsigned int>> {
                     return List<unsigned int>::cons(
                         _args.d_a0, interleave0(l2, _args.d_a1));
                   }},
        l1->v());
  }
}

std::shared_ptr<List<unsigned int>>
ProgFix::interleave(std::shared_ptr<List<unsigned int>> l1,
                    std::shared_ptr<List<unsigned int>> l2) {
  return interleave_func(
      SigT<std::shared_ptr<List<unsigned int>>,
           std::shared_ptr<List<unsigned int>>>::existt(l1, l2));
}
