#include "recursive_record_incomplete_type.h"

uint64_t RecursiveRecordIncompleteType::csum(
    const RecursiveRecordIncompleteType::cell &c) {
  return (c.key + [=]() mutable {
    auto go_impl =
        [](auto &_self_go,
           const List<RecursiveRecordIncompleteType::cell> &l) -> uint64_t {
      if (std::holds_alternative<
              typename List<RecursiveRecordIncompleteType::cell>::Nil>(l.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<RecursiveRecordIncompleteType::cell>::Cons>(
                l.v());
        return (csum(a0) + _self_go(_self_go, *a1));
      }
    };
    auto go =
        [&](const List<RecursiveRecordIncompleteType::cell> &l) -> uint64_t {
      return go_impl(go_impl, l);
    };
    return go(c.kids);
  }());
}

uint64_t RecursiveRecordIncompleteType::run(uint64_t n) {
  List<RecursiveRecordIncompleteType::cell> ks =
      List<RecursiveRecordIncompleteType::cell>::cons(
          cell{n, List<RecursiveRecordIncompleteType::cell>::nil()},
          List<RecursiveRecordIncompleteType::cell>::cons(
              cell{(n + 1), List<RecursiveRecordIncompleteType::cell>::nil()},
              List<RecursiveRecordIncompleteType::cell>::cons(
                  cell{((n + 1) + 1),
                       List<RecursiveRecordIncompleteType::cell>::nil()},
                  List<RecursiveRecordIncompleteType::cell>::nil())));
  uint64_t a = csum(cell{UINT64_C(1), ks});
  uint64_t b = csum(cell{UINT64_C(2), ks});
  return (a + b);
}
