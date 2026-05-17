#include "sort.h"

Sig<List<uint64_t>> Sort::sort_cons_prog(uint64_t a, const List<uint64_t> &,
                                         const List<uint64_t> &l_) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l_.v())) {
    return Sig<List<uint64_t>>::exist(
        List<uint64_t>::cons(a, List<uint64_t>::nil()));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l_.v());
    Sig<List<uint64_t>> s = sort_cons_prog(a, *a1, *a1);
    auto &[x0] = s;
    bool s0 = a <= a0;
    if (s0) {
      return Sig<List<uint64_t>>::exist(
          List<uint64_t>::cons(a, List<uint64_t>::cons(a0, *a1)));
    } else {
      return Sig<List<uint64_t>>::exist(
          List<uint64_t>::cons(a0, std::move(x0)));
    }
  }
}

Sig<List<uint64_t>> Sort::isort(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return Sig<List<uint64_t>>::exist(List<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const auto &_sv0 = isort(*a1);
    const auto &[x0] = _sv0;
    return sort_cons_prog(a0, *a1, x0);
  }
}

List<uint64_t> Sort::merge(List<uint64_t> l1, const List<uint64_t> &l2) {
  auto merge_aux_impl = [&](auto &_self_merge_aux,
                            List<uint64_t> l3) -> List<uint64_t> {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
      return l3;
    } else {
      const auto &[a0, a2] = std::get<typename List<uint64_t>::Cons>(l1.v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l3.v_mut())) {
        return l1;
      } else {
        auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l3.v_mut());
        if (a0 <= a00) {
          return List<uint64_t>::cons(a0, merge(*a2, l3));
        } else {
          return List<uint64_t>::cons(std::move(a00),
                                      _self_merge_aux(_self_merge_aux, *a10));
        }
      }
    }
  };
  auto merge_aux = [&](List<uint64_t> l3) -> List<uint64_t> {
    return merge_aux_impl(merge_aux_impl, l3);
  };
  return merge_aux(l2);
}

Sig<List<uint64_t>> Sort::merge_prog(const List<uint64_t> &,
                                     const List<uint64_t> &l1,
                                     const List<uint64_t> &l2) {
  return Sig<List<uint64_t>>::exist(merge(l1, l2));
}

Sig<List<uint64_t>> Sort::msort(const List<uint64_t> &_x0) {
  return div_conq_split(
      Sig<List<uint64_t>>::exist(List<uint64_t>::nil()),
      [](uint64_t a) {
        return Sig<List<uint64_t>>::exist(
            List<uint64_t>::cons(a, List<uint64_t>::nil()));
      },
      [](const List<uint64_t> &ls, const Sig<List<uint64_t>> &x,
         const Sig<List<uint64_t>> &x0) {
        const auto &[x2] = x;
        const auto &[x3] = x0;
        return merge_prog(ls, x2, x3);
      },
      _x0);
}

Sig<List<uint64_t>> Sort::pair_merge_prog(uint64_t, uint64_t,
                                          const List<uint64_t> &,
                                          const List<uint64_t> &l_,
                                          const List<uint64_t> &l_0) {
  return Sig<List<uint64_t>>::exist(merge(l_0, l_));
}

Sig<List<uint64_t>> Sort::psort(const List<uint64_t> &_x0) {
  return div_conq_pair(
      Sig<List<uint64_t>>::exist(List<uint64_t>::nil()),
      [](uint64_t a) {
        return Sig<List<uint64_t>>::exist(
            List<uint64_t>::cons(a, List<uint64_t>::nil()));
      },
      [](uint64_t a1, uint64_t a2) {
        bool s = a1 <= a2;
        if (s) {
          return Sig<List<uint64_t>>::exist(List<uint64_t>::cons(
              a1, List<uint64_t>::cons(a2, List<uint64_t>::nil())));
        } else {
          return Sig<List<uint64_t>>::exist(List<uint64_t>::cons(
              a2, List<uint64_t>::cons(a1, List<uint64_t>::nil())));
        }
      },
      [](uint64_t a1, uint64_t a2, const List<uint64_t> &l,
         const Sig<List<uint64_t>> &x, const Sig<List<uint64_t>> &x0) {
        const auto &[x2] = x;
        const auto &[x3] = x0;
        return pair_merge_prog(a1, a2, l, x3, x2);
      },
      _x0);
}

Sig<List<uint64_t>> Sort::qsort(const List<uint64_t> &_x0) {
  return div_conq_pivot(
      Compare_dec::le_dec, Sig<List<uint64_t>>::exist(List<uint64_t>::nil()),
      [](uint64_t a, const List<uint64_t> &, const Sig<List<uint64_t>> &x,
         const Sig<List<uint64_t>> &x0) {
        const auto &[x2] = x;
        const auto &[x3] = x0;
        return Sig<List<uint64_t>>::exist(
            merge(x2, List<uint64_t>::cons(a, x3)));
      },
      _x0);
}

bool Compare_dec::le_gt_dec(uint64_t _x0, uint64_t _x1) { return _x0 <= _x1; }

bool Compare_dec::le_dec(uint64_t n, uint64_t m) {
  bool s = Compare_dec::le_gt_dec(n, m);
  if (s) {
    return true;
  } else {
    return false;
  }
}
