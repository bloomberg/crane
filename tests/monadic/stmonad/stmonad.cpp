#include "stmonad.h"

uint64_t STMonadTests::array_simp_fixed_init() {
  std::vector<uint64_t> *arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      nat_idx::suc(nat_idx::suc(
          nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::zero()))))) -
          nat_idx::zero() + 1,
      UINT64_C(5));
  uint64_t elem = (*arr)[nat_idx::suc(nat_idx::zero())];
  return elem;
}

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
STMonadTests::array_simp_list() {
  std::vector<uint64_t> *arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::zero()))) -
      nat_idx::zero() + 1);
  {
    auto _xs = List<uint64_t>::cons(
        UINT64_C(5),
        List<uint64_t>::cons(
            UINT64_C(4),
            List<uint64_t>::cons(
                UINT64_C(3),
                List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))));
    for (size_t _i = 0; _i < arr->size(); _i++) {
      if (std::holds_alternative<
              typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v())) {
        auto &[_a, _l] =
            std::get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(
                _xs.v_mut());
        (*arr)[_i] = _a;
        if (_l)
          _xs = *_l;
      }
    }
  };
  uint64_t elem = (*arr)[nat_idx::zero()];
  List<uint64_t> lst = [&]() {
    using _E = typename std::remove_pointer_t<
        std::remove_cvref_t<decltype(arr)>>::value_type;
    List<_E> _r = List<_E>::nil();
    for (size_t _i = arr->size(); _i > 0; _i--) {
      _r = List<_E>::cons((*arr)[_i - 1], std::move(_r));
    }
    return _r;
  }();
  return std::make_pair(std::make_pair(elem, lst.length()), lst);
}

uint64_t STMonadTests::fib_fun(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m0 = n - 1;
    if (m0 <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t m = m0 - 1;
      return (fib_fun(m0) + fib_fun(m));
    }
  }
}

uint64_t STMonadTests::nth(uint64_t n, const List<uint64_t> &l,
                           uint64_t default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l.v());
      return nth(m, *a10, default0);
    }
  }
}

List<uint64_t> STMonadTests::quicksort_fun(const List<uint64_t> &x) {
  return STMonadExamples::quicksort_fun_functional(
      x, [](const List<uint64_t> &y) { return quicksort_fun(y); });
}

List<uint64_t> STMonadTests::quicksort_ST_mine(const List<uint64_t> &xs) {
  std::vector<uint64_t> *arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      nat_idx::fromNat((((xs.length() - UINT64_C(1)) > xs.length()
                             ? 0
                             : (xs.length() - UINT64_C(1))))) -
      nat_idx::zero() + 1);
  {
    auto _xs = xs;
    for (size_t _i = 0; _i < arr->size(); _i++) {
      if (std::holds_alternative<
              typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v())) {
        auto &[_a, _l] =
            std::get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(
                _xs.v_mut());
        (*arr)[_i] = _a;
        if (_l)
          _xs = *_l;
      }
    }
  };
  [&]() {
    static std::vector<std::pair<
        std::pair<std::pair<std::vector<uint64_t> *, uint64_t>, uint64_t>,
        uint64_t>>
        _stack;
    _stack.push_back(std::make_pair(
        std::make_pair(std::make_pair(arr, nat_idx::zero()), nat_idx::zero()),
        nat_idx::fromNat((((xs.length() - UINT64_C(1)) > xs.length()
                               ? 0
                               : (xs.length() - UINT64_C(1)))))));
    while (!_stack.empty()) {
      std::pair<
          std::pair<std::pair<std::vector<uint64_t> *, uint64_t>, uint64_t>,
          uint64_t>
          _arg = _stack.back();
      _stack.pop_back();
      [](std::pair<
          std::pair<std::pair<std::vector<uint64_t> *, uint64_t>, uint64_t>,
          uint64_t>
             args) {
        const auto &[p, r] = args;
        const auto &[p0, l] = p;
        const auto &[arr0, arr_idx] = p0;
        if (nat_idx::toNat(l) < nat_idx::toNat(r)) {
          uint64_t newPivot = [&]() {
            uint64_t pivotValue = (*arr0)[nat_idx::fromNat(
                (nat_idx::toNat(l) +
                 (UINT64_C(2)
                      ? (((nat_idx::toNat(r) - nat_idx::toNat(l)) >
                                  nat_idx::toNat(r)
                              ? 0
                              : (nat_idx::toNat(r) - nat_idx::toNat(l)))) /
                            UINT64_C(2)
                      : 0)))];
            [&]() {
              uint64_t leftVal = (*arr0)[nat_idx::fromNat(
                  (nat_idx::toNat(l) +
                   (UINT64_C(2)
                        ? (((nat_idx::toNat(r) - nat_idx::toNat(l)) >
                                    nat_idx::toNat(r)
                                ? 0
                                : (nat_idx::toNat(r) - nat_idx::toNat(l)))) /
                              UINT64_C(2)
                        : 0)))];
              uint64_t rightVal = (*arr0)[r];
              (*arr0)[nat_idx::fromNat(
                  (nat_idx::toNat(l) +
                   (UINT64_C(2)
                        ? (((nat_idx::toNat(r) - nat_idx::toNat(l)) >
                                    nat_idx::toNat(r)
                                ? 0
                                : (nat_idx::toNat(r) - nat_idx::toNat(l)))) /
                              UINT64_C(2)
                        : 0)))] = rightVal;
              (*arr0)[r] = leftVal;
              return std::monostate{};
            }();
            uint64_t storeIndex = [&]() {
              auto for_each_with_impl =
                  [](auto &_self_for_each_with, const List<uint64_t> &xs0,
                     uint64_t v, std::function<uint64_t(uint64_t, uint64_t)> f)
                  -> uint64_t {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        xs0.v())) {
                  return v;
                } else {
                  const auto &[a0, a1] =
                      std::get<typename List<uint64_t>::Cons>(xs0.v());
                  uint64_t v_ = f(v, a0);
                  return _self_for_each_with(_self_for_each_with, *a1, v_, f);
                }
              };
              auto for_each_with =
                  [&](const List<uint64_t> &xs0, uint64_t v,
                      std::function<uint64_t(uint64_t, uint64_t)> f)
                  -> uint64_t {
                return for_each_with_impl(for_each_with_impl, xs0, v, f);
              };
              return for_each_with(
                  nat_idx::range(
                      l, nat_idx::sub(r, nat_idx::suc(nat_idx::zero()))),
                  l, [=](uint64_t storeIndex, uint64_t i) mutable {
                    uint64_t val = (*arr0)[i];
                    if (val <= pivotValue) {
                      [&]() {
                        uint64_t leftVal = (*arr0)[i];
                        uint64_t rightVal = (*arr0)[storeIndex];
                        (*arr0)[i] = rightVal;
                        (*arr0)[storeIndex] = leftVal;
                        return std::monostate{};
                      }();
                      return nat_idx::suc(storeIndex);
                    } else {
                      return storeIndex;
                    }
                  });
            }();
            [&]() {
              uint64_t leftVal = (*arr0)[storeIndex];
              uint64_t rightVal = (*arr0)[r];
              (*arr0)[storeIndex] = rightVal;
              (*arr0)[r] = leftVal;
              return std::monostate{};
            }();
            return storeIndex;
          }();
          (_stack.push_back(std::make_pair(
               std::make_pair(std::make_pair(arr0, arr_idx), l),
               nat_idx::fromNat(
                   (((nat_idx::toNat(newPivot) - UINT64_C(1)) >
                             nat_idx::toNat(newPivot)
                         ? 0
                         : (nat_idx::toNat(newPivot) - UINT64_C(1))))))),
           std::monostate{});
          return (
              _stack.push_back(std::make_pair(
                  std::make_pair(std::make_pair(arr0, arr_idx),
                                 nat_idx::fromNat(
                                     (nat_idx::toNat(newPivot) + UINT64_C(1)))),
                  r)),
              std::monostate{});
        } else {
          return std::monostate{};
        }
      }(_arg);
    }
  }();
  ;
  List<uint64_t> newXs = [&]() {
    using _E = typename std::remove_pointer_t<
        std::remove_cvref_t<decltype(arr)>>::value_type;
    List<_E> _r = List<_E>::nil();
    for (size_t _i = arr->size(); _i > 0; _i--) {
      _r = List<_E>::cons((*arr)[_i - 1], std::move(_r));
    }
    return _r;
  }();
  return newXs;
}

std::string STMonadTests::list_to_string_helper(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return "";
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return std::to_string(a0) + ", "s + list_to_string_helper(*a1);
  }
}

std::string STMonadTests::list_to_string(const List<uint64_t> &l) {
  return "[ "s + list_to_string_helper(l) + " ]"s;
}

std::string STMonadTests::test_quicksort_ST(std::monostate) {
  List<uint64_t> out = quicksort_ST_mine(input_lst1);
  return list_to_string(std::move(out));
}

std::string STMonadTests::test_quicksort_fun(std::monostate) {
  List<uint64_t> out = quicksort_fun(input_lst1);
  return list_to_string(std::move(out));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}

uint64_t Nat::tail_add(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

uint64_t Nat::tail_addmul(uint64_t r, uint64_t n, uint64_t m) {
  if (n <= 0) {
    return r;
  } else {
    uint64_t n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

uint64_t Nat::tail_mul(uint64_t n, uint64_t m) {
  return Nat::tail_addmul(UINT64_C(0), n, m);
}

uint64_t Nat::of_uint_acc(const Uint &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Nat::of_uint_acc(*a0, Nat::tail_mul(UINT64_C(10), acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Nat::of_uint_acc(*a0, (Nat::tail_mul(UINT64_C(10), acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Nat::of_uint_acc(*a0, ((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Nat::of_uint_acc(*a0,
                            (((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Nat::of_uint_acc(
        *a0, ((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Nat::of_uint_acc(
        *a0, (((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Nat::of_uint_acc(
        *a0,
        ((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Nat::of_uint_acc(
        *a0,
        (((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Nat::of_uint_acc(
        *a0,
        ((((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Nat::of_uint_acc(
        *a0,
        (((((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  }
}

uint64_t Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_hex_uint_acc(const Uint0 &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return Nat::of_hex_uint_acc(*a0, Nat::tail_mul(UINT64_C(16), acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return Nat::of_hex_uint_acc(*a0, (Nat::tail_mul(UINT64_C(16), acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return Nat::of_hex_uint_acc(*a0,
                                ((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, (((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, ((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, (((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  }
}

uint64_t Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(u);
  }
}
