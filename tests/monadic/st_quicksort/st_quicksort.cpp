#include "st_quicksort.h"

List<uint64_t> StQuicksort::quicksort_fun(const List<uint64_t> &x) {
  // Explicit stack replaces the non-tail recursion of quicksort_fun: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> x;
  };

  struct _after_quicksort_fun_in_Cons {
    uint64_t a0;
    std::shared_ptr<List<uint64_t>> a1;
  };

  struct _after_quicksort_fun_in_Cons_2 {
    uint64_t a0;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_quicksort_fun_in_Cons,
                              _after_quicksort_fun_in_Cons_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &x = _f.x;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
        const List<uint64_t> &a1_value = *a1;
        _stack.emplace_back(_after_quicksort_fun_in_Cons{a0, a1});
        _stack.emplace_back(
            _call{a1_value.filter([=](uint64_t x0) { return x0 < a0; })});
      }
    } else if (std::holds_alternative<_after_quicksort_fun_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_quicksort_fun_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      const List<uint64_t> &a1_value = *a1;
      _stack.emplace_back(
          _after_quicksort_fun_in_Cons_2{a0, std::move(_result)});
      _stack.emplace_back(
          _call{a1_value.filter([=](uint64_t x0) { return a0 <= x0; })});
    } else {
      auto _f = std::move(std::get<_after_quicksort_fun_in_Cons_2>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result =
          _f._tmp2.app(List<uint64_t>::cons(a0, List<uint64_t>::nil()).app(
              std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> StQuicksort::quicksort_ST_mine(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return List<uint64_t>::nil();
  } else {
    std::vector<uint64_t> * arr;
    arr = new std::remove_pointer_t<decltype(arr)>(
        nat_idx::fromNat((((xs.length() - UINT64_C(1)) > xs.length()
                               ? 0
                               : (xs.length() - UINT64_C(1))))) -
        nat_idx::zero() + 1);
    {
      auto _xs = xs;
      for (size_t _i = 0; _i < arr->size(); _i++) {
        if (holds_alternative<typename std::remove_cvref_t<decltype(_xs)>::Cons>(
                _xs.v())) {
          const auto &[_a, _l] =
              get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v());
          (*arr)[_i] = _a;
          if (_l) _xs = *_l;
        }
      }
    };
    auto _once8 = xs.length();
    [&]() {
      static std::vector<std::pair<
          std::pair<std::pair<std::vector<uint64_t> *, uint64_t>, uint64_t>,
          uint64_t>> _stack;
      _stack.push_back(std::make_pair(
          std::make_pair(std::make_pair(arr, nat_idx::zero()), nat_idx::zero()),
          nat_idx::fromNat(
              (((_once8 - UINT64_C(1)) > _once8 ? 0
                                                : (_once8 - UINT64_C(1)))))));
      while (!_stack.empty()) {
        std::pair<
            std::pair<std::pair<std::vector<uint64_t> *, uint64_t>, uint64_t>,
            uint64_t> _arg = _stack.back();
        _stack.pop_back();
        [](std::pair<
            std::pair<std::pair<std::vector<uint64_t> *, uint64_t>, uint64_t>,
            uint64_t> args) {
          auto [p, r] = std::move(args);
          auto [p0, l] = std::move(p);
          auto [arr0, arr_idx] = std::move(p0);
          if (nat_idx::toNat(l) < nat_idx::toNat(r)) {
            uint64_t newPivot = [&]() {
              auto _once1 = nat_idx::toNat(r);
              auto _once2 = nat_idx::toNat(l);
              uint64_t pivotValue =
                  (*arr0)[nat_idx::fromNat(
                       (nat_idx::toNat(l) +
                        (UINT64_C(2) ? (((_once1 - _once2) > _once1
                                             ? 0
                                             : (_once1 - _once2))) /
                                       UINT64_C(2)
                                     : 0)))];
              [&]() {
                auto _once3 = nat_idx::toNat(r);
                auto _once4 = nat_idx::toNat(l);
                uint64_t vi =
                    (*arr0)[nat_idx::fromNat(
                         (nat_idx::toNat(l) +
                          (UINT64_C(2) ? (((_once3 - _once4) > _once3
                                               ? 0
                                               : (_once3 - _once4))) /
                                         UINT64_C(2)
                                       : 0)))];
                uint64_t vj = (*arr0)[r];
                auto _once5 = nat_idx::toNat(r);
                auto _once6 = nat_idx::toNat(l);
                (*arr0)[nat_idx::fromNat(
                     (nat_idx::toNat(l) +
                      (UINT64_C(2) ? (((_once5 - _once6) > _once5
                                           ? 0
                                           : (_once5 - _once6))) /
                                     UINT64_C(2)
                                   : 0)))] = vj;
                (*arr0)[r] = vi;
                return std::monostate{};
              }();
              uint64_t storeIndex = [&]() {
                auto for_each_with =
                    [](const List<uint64_t> &xs0, uint64_t v,
                       const crane::fn<uint64_t(uint64_t,
                                                uint64_t)> &f)
                         -> uint64_t {
                      // Loop replaces the tail recursion: each recursive call
                      // updates the loop variables.
                      uint64_t _loop_v = v;
                      const List<uint64_t> *_loop_xs0 = &xs0;
                      while (true) {
                        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                                _loop_xs0->v())) {
                          return _loop_v;
                        } else {
                          const auto &[a2, a3] =
                              std::get<typename List<uint64_t>::Cons>(
                                  _loop_xs0->v());
                          uint64_t v_ = f(_loop_v, a2);
                          _loop_v = v_;
                          _loop_xs0 = crane_raw(a3);
                        }
                      }
                    };
                return for_each_with(nat_idx::range(
                    l, nat_idx::sub(r, nat_idx::suc(nat_idx::zero()))),
                                     l, [=](uint64_t storeIndex, uint64_t i) {
                                       uint64_t val = (*arr0)[i];
                                       if (val <= pivotValue) {
                                         [&]() {
                                           uint64_t vi = (*arr0)[i];
                                           uint64_t vj = (*arr0)[storeIndex];
                                           (*arr0)[i] = vj;
                                           (*arr0)[storeIndex] = vi;
                                           return std::monostate{};
                                         }();
                                         return nat_idx::suc(storeIndex);
                                       } else {
                                         return storeIndex;
                                       }
                                     });
              }();
              [&]() {
                uint64_t vi = (*arr0)[storeIndex];
                uint64_t vj = (*arr0)[r];
                (*arr0)[storeIndex] = vj;
                (*arr0)[r] = vi;
                return std::monostate{};
              }();
              return storeIndex;
            }();
            auto _once7 = nat_idx::toNat(newPivot);
            (
                _stack.push_back(std::make_pair(
                    std::make_pair(std::make_pair(arr0, arr_idx), l),
                    nat_idx::fromNat((((_once7 - UINT64_C(1)) > _once7
                                           ? 0
                                           : (_once7 - UINT64_C(1))))))),
                std::monostate{});
            return (
                _stack.push_back(std::make_pair(std::make_pair(
                    std::make_pair(std::move(arr0), arr_idx),
                    nat_idx::fromNat((nat_idx::toNat(newPivot) + UINT64_C(1)))),
                                                r)),
                std::monostate{});
          } else {
            return std::monostate{};
          }
        }(_arg);
      }
    } ();
    ;
    auto &&_once9 = std::move(arr);
    return [&]() {
      using _E = typename std::remove_pointer_t<
          std::remove_cvref_t<decltype(_once9)>>::value_type;
      List<_E> _r = List<_E>::nil();
      for (size_t _i = _once9->size(); _i > 0; _i--) {
        _r = List<_E>::cons((*_once9)[_i - 1], std::move(_r));
      }
      return _r;
    }();
  }
}

uint64_t StQuicksort::nth(uint64_t n, const List<uint64_t> &l,
                          uint64_t default0) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return default0;
      } else {
        const auto &[a0, _] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        return a0;
      }
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return default0;
      } else {
        const auto &[_, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a10);
        _loop_n = m;
      }
    }
  }
}

std::string StQuicksort::list_to_string_helper(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of list_to_string_helper:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_list_to_string_helper_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_list_to_string_helper_in_Cons>;
  std::string _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = "";
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_list_to_string_helper_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f =
          std::move(std::get<_after_list_to_string_helper_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = std::to_string(a0) + std::string(", ") + std::move(_result);
    }
  }
  return _result;
}

std::string StQuicksort::list_to_string(const List<uint64_t> &l) {
  return std::string("[ ") + list_to_string_helper(l) + std::string(" ]");
}

std::string StQuicksort::test_quicksort_ST() {
  List<uint64_t> out = quicksort_ST_mine(input_lst1);
  return list_to_string(std::move(out));
}

std::string StQuicksort::test_quicksort_fun() {
  return list_to_string(quicksort_fun(input_lst1));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
