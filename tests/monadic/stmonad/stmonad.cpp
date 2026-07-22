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

uint64_t
STMonadTests::fib_fun(uint64_t n) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_m: saves [m0], dispatches next recursive call.
  struct _After_m {
    uint64_t m0;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_m, _Combine_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified fib_fun: _Enter -> _After_m -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m0 = n - 1;
        if (m0 <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = m0 - 1;
          _stack.emplace_back(_After_m{m0});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_Combine_m{std::move(_result)});
      _stack.emplace_back(_Enter{_f.m0});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t STMonadTests::nth(uint64_t n, const List<uint64_t> &l,
                           uint64_t default0) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return default0;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        return a0;
      }
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return default0;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = a10.get();
        _loop_n = m;
      }
    }
  }
}

List<uint64_t> STMonadTests::quicksort_fun(
    const List<uint64_t>
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> x;
  };

  /// _After_Cons: saves [_s0, _s1], dispatches next recursive call.
  struct _After_Cons {
    List<uint64_t> _s0;
    std::decay_t<decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                               List<uint64_t>::nil()))>
        _s1;
  };

  /// _Combine_Cons: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Cons {
    List<uint64_t> _result;
    std::decay_t<decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                               List<uint64_t>::nil()))>
        _s1;
  };

  using _Frame = std::variant<_Enter, _After_Cons, _Combine_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{x});
  /// Loopified quicksort_fun: _Enter -> _After_Cons -> _Combine_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &x = std::move(_f.x);
      const List<uint64_t> &_inl_l = x;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_inl_l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename List<uint64_t>::Cons>(_inl_l.v());
        const List<uint64_t> &_inl_a1_value = *_inl_a1;
        _stack.emplace_back(_After_Cons{
            std::move(_inl_a1_value.filter(
                [=](uint64_t _inl_x) mutable { return _inl_x < _inl_a0; })),
            List<uint64_t>::cons(_inl_a0, List<uint64_t>::nil())});
        _stack.emplace_back(_Enter{_inl_a1_value.filter(
            [=](uint64_t _inl_x) mutable { return _inl_a0 <= _inl_x; })});
      }
    } else if (std::holds_alternative<_After_Cons>(_frame)) {
      auto _f = std::move(std::get<_After_Cons>(_frame));
      _stack.emplace_back(_Combine_Cons{std::move(_result), _f._s1});
      _stack.emplace_back(_Enter{std::move(_f._s0)});
    } else {
      auto _f = std::move(std::get<_Combine_Cons>(_frame));
      _result = std::move(_result).app(_f._s1.app(std::move(_f._result)));
    }
  }
  return _result;
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
                  [](auto &, const List<uint64_t> &xs0, uint64_t v,
                     std::function<uint64_t(uint64_t, uint64_t)> f)
                  -> uint64_t {
                uint64_t _loop_v = std::move(v);
                const List<uint64_t> *_loop_xs0 = &xs0;
                while (true) {
                  if (std::holds_alternative<typename List<uint64_t>::Nil>(
                          _loop_xs0->v())) {
                    return _loop_v;
                  } else {
                    const auto &[a0, a1] =
                        std::get<typename List<uint64_t>::Cons>(_loop_xs0->v());
                    uint64_t v_ = f(_loop_v, a0);
                    _loop_v = v_;
                    _loop_xs0 = a1.get();
                  }
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

std::string STMonadTests::list_to_string_helper(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0, _s1], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::to_string(std::declval<uint64_t &>()))> a0;
    std::decay_t<decltype(", ")> _s1;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  std::string _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_to_string_helper: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = "";
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{std::to_string(a0), ", "});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.a0 + _f._s1 + std::move(_result);
    }
  }
  return _result;
}

std::string STMonadTests::list_to_string(const List<uint64_t> &l) {
  return "[ "s + list_to_string_helper(l) + " ]"s;
}

List<uint64_t>
STMonadTests::rep_list_nat(List<uint64_t> l,
                           uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_x: resumes after recursive call with _result.
  struct _Resume_x {};

  using _Frame = std::variant<_Enter, _Resume_x>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified rep_list_nat: _Enter -> _Resume_x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::move(l);
      } else {
        uint64_t x = n - 1;
        _stack.emplace_back(_Resume_x{});
        _stack.emplace_back(_Enter{x});
      }
    } else {
      auto _f = std::move(std::get<_Resume_x>(_frame));
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

std::string STMonadTests::test_quicksort_ST(std::monostate) {
  List<uint64_t> out = quicksort_ST_mine(input_lst1);
  return list_to_string(std::move(out));
}

std::string STMonadTests::test_quicksort_fun(std::monostate) {
  List<uint64_t> out = quicksort_fun(input_lst1);
  return list_to_string(std::move(out));
}

List<uint64_t>
ListDef::seq(uint64_t start,
             uint64_t len) { /// _Enter: captures varying parameters for each
                             /// recursive call.

  struct _Enter {
    uint64_t len;
    uint64_t start;
  };

  /// _Resume_len0: saves [start], resumes after recursive call with _result.
  struct _Resume_len0 {
    uint64_t start;
  };

  using _Frame = std::variant<_Enter, _Resume_len0>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{len, start});
  /// Loopified seq: _Enter -> _Resume_len0.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t len = _f.len;
      uint64_t start = _f.start;
      if (len <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t len0 = len - 1;
        _stack.emplace_back(_Resume_len0{start});
        _stack.emplace_back(_Enter{len0, (start + 1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_len0>(_frame));
      _result = List<uint64_t>::cons(_f.start, std::move(_result));
    }
  }
  return _result;
}
