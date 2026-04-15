#include <mergesort_fuel.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// * Split
__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
MergesortFuel::split(const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return std::make_pair(List<unsigned int>::nil(), List<unsigned int>::nil());
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::make_pair(
          List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil()),
          List<unsigned int>::nil());
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      auto _cs = split(_m0.d_a1);
      const std::shared_ptr<List<unsigned int>> &l1 = _cs.first;
      const std::shared_ptr<List<unsigned int>> &l2 = _cs.second;
      return std::make_pair(List<unsigned int>::cons(_m.d_a0, l1),
                            List<unsigned int>::cons(_m0.d_a0, l2));
    }
  }
}

/// * Merge
std::shared_ptr<List<unsigned int>>
MergesortFuel::merge(std::shared_ptr<List<unsigned int>> l1,
                     const std::shared_ptr<List<unsigned int>> &l2) {
  std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>)>
      merge_aux;
  merge_aux = [&](std::shared_ptr<List<unsigned int>> l3)
      -> std::shared_ptr<List<unsigned int>> {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l1->v())) {
      return l3;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l3->v())) {
        return l1;
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&l3->v());
        if (Compare_dec::le_lt_dec(_m.d_a0, _m0.d_a0)) {
          return List<unsigned int>::cons(_m.d_a0, merge(_m.d_a1, l3));
        } else {
          return List<unsigned int>::cons(_m0.d_a0, merge_aux(_m0.d_a1));
        }
      }
    }
  };
  return merge_aux(l2);
}

/// * Fuel-based merge sort
std::shared_ptr<List<unsigned int>>
MergesortFuel::msort_go(const unsigned int fuel,
                        std::shared_ptr<List<unsigned int>> l) {
  if (fuel <= 0) {
    return l;
  } else {
    unsigned int fuel_ = fuel - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v()) &&
        l.use_count() == 1) {
      return l;
    } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                   l->v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
      auto &&_sv = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
        return List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
      } else {
        auto _cs = split(l);
        const std::shared_ptr<List<unsigned int>> &l1 = _cs.first;
        const std::shared_ptr<List<unsigned int>> &l2 = _cs.second;
        return merge(msort_go(fuel_, l1), msort_go(fuel_, l2));
      }
    }
  }
}

/// * Top-level sort and correctness
std::shared_ptr<List<unsigned int>>
MergesortFuel::msort(const std::shared_ptr<List<unsigned int>> &l) {
  return msort_go(l->length(), l);
}

__attribute__((pure)) bool Compare_dec::le_lt_dec(const unsigned int n,
                                                  const unsigned int m) {
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
