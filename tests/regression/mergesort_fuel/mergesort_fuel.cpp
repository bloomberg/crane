#include <mergesort_fuel.h>

/// * Split
__attribute__((pure)) std::pair<List<unsigned int>, List<unsigned int>>
MergesortFuel::split(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(List<unsigned int>::nil(), List<unsigned int>::nil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return std::make_pair(
          List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
          List<unsigned int>::nil());
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      auto _cs = split(*(d_a10));
      const List<unsigned int> &l1 = _cs.first;
      const List<unsigned int> &l2 = _cs.second;
      return std::make_pair(List<unsigned int>::cons(d_a0, l1),
                            List<unsigned int>::cons(d_a00, l2));
    }
  }
}

/// * Merge
__attribute__((pure)) List<unsigned int>
MergesortFuel::merge(List<unsigned int> l1, const List<unsigned int> &l2) {
  std::function<List<unsigned int>(List<unsigned int>)> merge_aux;
  merge_aux = [&](List<unsigned int> l3) -> List<unsigned int> {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
      return l3;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              l3.v_mut())) {
        return l1;
      } else {
        auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(l3.v_mut());
        if (Compare_dec::le_lt_dec(d_a0, d_a00)) {
          return List<unsigned int>::cons(d_a0, merge(*(d_a1), l3));
        } else {
          return List<unsigned int>::cons(d_a00, merge_aux(*(d_a10)));
        }
      }
    }
  };
  return merge_aux(l2);
}

/// * Fuel-based merge sort
__attribute__((pure)) List<unsigned int>
MergesortFuel::msort_go(const unsigned int &fuel, List<unsigned int> l) {
  if (fuel <= 0) {
    return l;
  } else {
    unsigned int fuel_ = fuel - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v_mut())) {
      return List<unsigned int>::nil();
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v_mut());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else {
        auto _cs = split(l);
        const List<unsigned int> &l1 = _cs.first;
        const List<unsigned int> &l2 = _cs.second;
        return merge(msort_go(fuel_, l1), msort_go(fuel_, l2));
      }
    }
  }
}

/// * Top-level sort and correctness
__attribute__((pure)) List<unsigned int>
MergesortFuel::msort(const List<unsigned int> &l) {
  return msort_go(l.length(), l);
}

__attribute__((pure)) bool Compare_dec::le_lt_dec(const unsigned int &n,
                                                  const unsigned int &m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      if (Compare_dec::le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}
