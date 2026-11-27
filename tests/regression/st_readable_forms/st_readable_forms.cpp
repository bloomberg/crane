#include "st_readable_forms.h"

uint64_t pair_parts() {
  std::pair<uint64_t, uint64_t> r = std::make_pair(UINT64_C(3), UINT64_C(4));
  std::shared_ptr<crane::array_storage<std::pair<uint64_t, uint64_t>>> a =
      std::make_shared<crane::array_storage<std::pair<uint64_t, uint64_t>>>(
          static_cast<std::size_t>(UINT64_C(2)),
          std::make_pair(UINT64_C(5), UINT64_C(6)));
  auto [x, _] = r;
  auto [_, y] = std::span{std::as_const(*a)}[UINT64_C(1)];
  return (x + y);
}

uint64_t fib_step(uint64_t n) {
  uint64_t a = UINT64_C(0);
  uint64_t b = UINT64_C(1);
  auto go = [&]() -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    uint64_t _loop_k = n;
    while (true) {
      if (_loop_k <= 0) {
        return;
      } else {
        uint64_t k_ = _loop_k - 1;
        uint64_t x = a;
        a = b;
        b = (x + b);
        _loop_k = k_;
      }
    }
    return;
  };
  go();
  return a;
}

uint64_t add_at(std::span<const uint64_t> arr, uint64_t acc, uint64_t i) {
  uint64_t v = arr[i];
  return (acc + v);
}

uint64_t sum_with() {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          static_cast<std::size_t>(UINT64_C(4)), UINT64_C(3));
  std::span{*arr}[UINT64_C(2)] = UINT64_C(10);
  return STMonad::template for_each_with<uint64_t, uint64_t>(
      ListDef::seq(UINT64_C(0), UINT64_C(4)), UINT64_C(0),
      [=, arr = std::move(arr)](uint64_t _x0,
                                uint64_t _x1)
           -> uint64_t {
        return add_at(std::span{std::as_const(*arr)}, _x0, _x1);
      });
}

uint64_t count_back(std::span<uint64_t> arr, uint64_t k) {
  // Explicit stack replaces the non-tail recursion of count_back: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t k;
  };

  struct _after_count_back_in_S {
    uint64_t k;
    uint64_t k_;
  };

  using _frame = std::variant<_call, _after_count_back_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      if (k <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t k_ = k - 1;
        _stack.emplace_back(_after_count_back_in_S{k, k_});
        _stack.emplace_back(_call{k_});
      }
    } else {
      auto _f = std::move(std::get<_after_count_back_in_S>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      uint64_t k_ = _f.k_;
      arr[(UINT64_C(4) ? k_ % UINT64_C(4) : k_)] = _result;
      _result = (_result + k);
    }
  }
  return _result;
}

uint64_t run_count_back() {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          static_cast<std::size_t>(UINT64_C(4)), UINT64_C(0));
  return count_back(std::span{*arr}, UINT64_C(5));
}

uint64_t ignore_ref(const uint64_t *, uint64_t n) { return (n + UINT64_C(1)); }

uint64_t pass_view(uint64_t *r0) {
  *r0 = UINT64_C(2);
  return ignore_ref(r0, UINT64_C(4));
}

uint64_t unused_param() {
  uint64_t r0 = UINT64_C(0);
  return pass_view(&r0);
}

uint64_t StReadableForms::fib_step(uint64_t n) { return ::fib_step(n); }

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = len - 1;
      auto _cell = typename List<uint64_t>::Cons(start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      len = len0;
      start = (start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
