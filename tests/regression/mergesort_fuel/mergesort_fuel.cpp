#include "mergesort_fuel.h"

/// * Split
std::pair<List<uint64_t>, List<uint64_t>>
MergesortFuel::split(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::make_pair(List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                            List<uint64_t>::nil());
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      auto _cs = split(*a10);
      const List<uint64_t> &l1 = _cs.first;
      const List<uint64_t> &l2 = _cs.second;
      return std::make_pair(List<uint64_t>::cons(a0, l1),
                            List<uint64_t>::cons(a00, l2));
    }
  }
} /// * Merge

List<uint64_t> MergesortFuel::merge(List<uint64_t> l1,
                                    const List<uint64_t> &l2) {
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
        if (Compare_dec::le_lt_dec(a0, a00)) {
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

/// * Fuel-based merge sort
List<uint64_t> MergesortFuel::msort_go(uint64_t fuel, List<uint64_t> l) {
  if (fuel <= 0) {
    return l;
  } else {
    uint64_t fuel_ = fuel - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return List<uint64_t>::nil();
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        return List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
      } else {
        auto _cs = split(l);
        const List<uint64_t> &l1 = _cs.first;
        const List<uint64_t> &l2 = _cs.second;
        return merge(msort_go(fuel_, l1), msort_go(fuel_, l2));
      }
    }
  }
}

/// * Top-level sort and correctness
List<uint64_t> MergesortFuel::msort(const List<uint64_t> &l) {
  return msort_go(l.length(), l);
}

bool Compare_dec::le_lt_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      if (Compare_dec::le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}
