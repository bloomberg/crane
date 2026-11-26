#include "st_array_loops.h"

void StArrayLoops::zero_from(std::span<uint64_t> arr, uint64_t i, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return;
    } else {
      uint64_t m = n - 1;
      arr[i] = UINT64_C(0);
      n = m;
      i = (i + 1);
    }
  }
  return;
}

uint64_t StArrayLoops::sum_from(std::span<const uint64_t> arr, uint64_t i,
                                uint64_t n) {
  // Explicit stack replaces the non-tail recursion of sum_from: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t i;
  };

  struct _after_sum_from_in_S {
    uint64_t x;
  };

  using _frame = std::variant<_call, _after_sum_from_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, i});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t i = _f.i;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        uint64_t x = arr[i];
        _stack.emplace_back(_after_sum_from_in_S{x});
        _stack.emplace_back(_call{m, (i + 1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_from_in_S>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      uint64_t r = std::move(_result);
      _result = (x + r);
    }
  }
  return _result;
}

std::pair<uint64_t, List<uint64_t>> StArrayLoops::loops_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(n),
                                                       UINT64_C(2));
  zero_from(std::span<uint64_t>{*arr}, UINT64_C(1), UINT64_C(2));
  uint64_t s = sum_from(std::span<const uint64_t>{*arr}, UINT64_C(0), n);
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
  return std::make_pair(s, std::move(elems));
}
