#include "tmc_nested_ctor_wrap.h"

Nat TmcNestedCtorWrap::rsize(const TmcNestedCtorWrap::rose &r) {
  const auto &[a0] = std::get<typename TmcNestedCtorWrap::rose::Rnode>(r.v());
  const List<TmcNestedCtorWrap::rose> &a0_value = *a0;
  return Nat::s(a0_value.template fold_left<Nat>(
      [](const Nat &acc, const TmcNestedCtorWrap::rose &c) {
        return acc.add(rsize(c));
      },
      Nat::o()));
}

TmcNestedCtorWrap::rose TmcNestedCtorWrap::spine(const Nat &n) {
  std::shared_ptr<TmcNestedCtorWrap::rose> _head{};
  std::shared_ptr<TmcNestedCtorWrap::rose> *_write = &_head;
  const Nat *_loop_n = &n;
  while (true) {
    if (std::holds_alternative<typename Nat::O>(_loop_n->v())) {
      *_write = std::make_shared<TmcNestedCtorWrap::rose>(
          rose::rnode(List<TmcNestedCtorWrap::rose>::nil()));
      break;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(_loop_n->v());
      auto _cell = std::make_shared<TmcNestedCtorWrap::rose>(
          typename rose::Rnode(nullptr));
      auto _cell1 = std::make_shared<TmcNestedCtorWrap::rose>(
          typename List<TmcNestedCtorWrap::rose>::Cons(
              nullptr, std::make_shared<TmcNestedCtorWrap::rose>(
                           List<TmcNestedCtorWrap::rose>::nil())));
      std::get<typename rose::Rnode>(_cell->v_mut()).a0 = std::move(_cell1);
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<TmcNestedCtorWrap::rose>::Cons>(
               std::get<typename rose::Rnode>((*_write)->v_mut()).a0->v_mut())
               .a;
      _loop_n = crane_raw(a0);
      continue;
    }
  }
  return std::move(*_head);
}
