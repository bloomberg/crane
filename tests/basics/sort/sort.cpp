#include "sort.h"

List<uint64_t> Sort::sort_cons_prog(uint64_t a, const List<uint64_t> &,
                                    const List<uint64_t> &l_) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l_.v())) {
    return List<uint64_t>::cons(a, List<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l_.v());
    List<uint64_t> s = sort_cons_prog(a, *a1, *a1);
    const List<uint64_t> &x = std::move(s);
    bool s0 = a <= a0;
    if (s0) {
      return List<uint64_t>::cons(
          a, List<uint64_t>::cons(a0, crane::shared_child(a1)));
    } else {
      return List<uint64_t>::cons(a0, x);
    }
  }
}

List<uint64_t> Sort::isort(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &x = isort(*a1);
    return sort_cons_prog(a0, *a1, x);
  }
}

List<uint64_t> Sort::merge(List<uint64_t> l1, const List<uint64_t> &l2) {
  auto merge_aux_impl =
      [&](auto &_self_merge_aux, const List<uint64_t> &l3) -> List<uint64_t> {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
          return l3;
        } else {
          const auto &[a0, a2] =
              std::get<typename List<uint64_t>::Cons>(l1.v());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l3.v())) {
            return l1;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(l3.v());
            if (a0 <= a00) {
              return List<uint64_t>::cons(a0, merge(*a2, l3));
            } else {
              return List<uint64_t>::cons(
                  a00, _self_merge_aux(_self_merge_aux, *a10));
            }
          }
        }
      };
  {
    const List<uint64_t> &_lc1_l3 = l2;
    return merge_aux_impl(merge_aux_impl, _lc1_l3);
  }
}

List<uint64_t> Sort::merge_prog(const List<uint64_t> &, List<uint64_t> l1,
                                const List<uint64_t> &l2) {
  return merge(std::move(l1), l2);
}

List<uint64_t> Sort::msort(const List<uint64_t> &x0_) {
  return div_conq_split<uint64_t, List<uint64_t>>(
      List<uint64_t>::nil(),
      [](uint64_t a) { return List<uint64_t>::cons(a, List<uint64_t>::nil()); },
      [](const List<uint64_t> &ls, const List<uint64_t> &x,
         const List<uint64_t> &x0) {
        const List<uint64_t> &x1 = x;
        const List<uint64_t> &x2 = x0;
        return merge_prog(ls, x1, x2);
      },
      x0_);
}

List<uint64_t> Sort::pair_merge_prog(uint64_t, uint64_t, const List<uint64_t> &,
                                     const List<uint64_t> &l_,
                                     List<uint64_t> l_0) {
  return merge(std::move(l_0), l_);
}

List<uint64_t> Sort::psort(const List<uint64_t> &x0_) {
  return div_conq_pair<uint64_t, List<uint64_t>>(
      List<uint64_t>::nil(),
      [](uint64_t a) { return List<uint64_t>::cons(a, List<uint64_t>::nil()); },
      [](uint64_t a1, uint64_t a2) -> List<uint64_t> {
        bool s = a1 <= a2;
        if (s) {
          return List<uint64_t>::cons(
              a1, List<uint64_t>::cons(a2, List<uint64_t>::nil()));
        } else {
          return List<uint64_t>::cons(
              a2, List<uint64_t>::cons(a1, List<uint64_t>::nil()));
        }
      },
      [](uint64_t a1, uint64_t a2, const List<uint64_t> &l,
         const List<uint64_t> &x, const List<uint64_t> &x0) {
        const List<uint64_t> &x1 = x;
        const List<uint64_t> &x2 = x0;
        return pair_merge_prog(a1, a2, l, x2, x1);
      },
      x0_);
}

List<uint64_t> Sort::qsort(const List<uint64_t> &x0_) {
  return div_conq_pivot<uint64_t, List<uint64_t>>(
      Compare_dec::le_dec,
      List<uint64_t>::nil(),
      [](uint64_t a, List<uint64_t>, const List<uint64_t> &x,
         const List<uint64_t> &x0) {
        const List<uint64_t> &x1 = x;
        const List<uint64_t> &x2 = x0;
        return merge(x1, List<uint64_t>::cons(a, x2));
      },
      x0_);
}

bool Compare_dec::le_gt_dec(uint64_t x0_, uint64_t x1_) { return x0_ <= x1_; }

bool Compare_dec::le_dec(uint64_t n, uint64_t m) {
  bool s = Compare_dec::le_gt_dec(n, m);
  if (s) {
    return true;
  } else {
    return false;
  }
}
