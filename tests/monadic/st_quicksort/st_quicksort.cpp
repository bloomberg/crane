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
        _stack.emplace_back(_call{a1_value.filter(
            [=, a0 = std::move(a0)](uint64_t x0) { return x0 < a0; })});
      }
    } else if (std::holds_alternative<_after_quicksort_fun_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_quicksort_fun_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      const List<uint64_t> &a1_value = *a1;
      _stack.emplace_back(
          _after_quicksort_fun_in_Cons_2{a0, std::move(_result)});
      _stack.emplace_back(_call{a1_value.filter(
          [=, a0 = std::move(a0)](uint64_t x0) { return a0 <= x0; })});
    } else {
      auto _f = std::move(std::get<_after_quicksort_fun_in_Cons_2>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = _f._tmp2.app(List<uint64_t>::cons(std::move(a0),
                                                  List<uint64_t>::nil())
                                 .app(std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> StQuicksort::quicksort_ST_mine(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return List<uint64_t>::nil();
  } else {
    auto _once1 = xs.length();
    auto _once2 = nat_idx::zero();
    auto _once3 = nat_idx::fromNat(
        (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1)))));
    std::shared_ptr<crane::array_storage<uint64_t>> arr =
        crane::st::new_list_array<uint64_t>(
            crane::st::extent(std::move(_once2), std::move(_once3)), xs);
    auto _once4 = xs.length();
    quicksort_ST<StQuicksort::nat_stref, StQuicksort::nat_idx, uint64_t,
                 std::monostate>(
        xs.length(), arr, nat_idx::zero(), nat_idx::zero(),
        nat_idx::fromNat(
            (((_once4 - UINT64_C(1)) > _once4 ? 0 : (_once4 - UINT64_C(1))))));
    return crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
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
      _result = crane::string_capped(
          std::to_string(a0) +
          crane::string_capped(std::string(", ") + std::move(_result)));
    }
  }
  return _result;
}

std::string StQuicksort::list_to_string(const List<uint64_t> &l) {
  return crane::string_capped(
      std::string("[ ") +
      crane::string_capped(list_to_string_helper(l) + std::string(" ]")));
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
