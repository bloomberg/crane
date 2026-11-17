#include "mem_safety_probe7.h"

uint64_t MemSafetyProbe7::sum_list(const MemSafetyProbe7::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe7::mylist<uint64_t> *l;
  };

  struct _after_sum_list_in_Mycons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_list_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe7::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Mycons>(_popped));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Build a list of closures where each captures the TAIL
/// and computes its length. The tail is unique_ptr.
MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>
MemSafetyProbe7::build_len_closures(const MemSafetyProbe7::mylist<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>> _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>> *_write =
      nullptr;
  const MemSafetyProbe7::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      auto _value = mylist<crane::fn<uint64_t(std::monostate)>>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                      crane::fn<uint64_t(std::monostate)>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[_, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe7::mylist<
          crane::fn<uint64_t(std::monostate)>>::Mycons(
          [=](std::monostate) { return a1_value.length(); }, nullptr);
      MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                          crane::fn<uint64_t(std::monostate)>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(std::monostate)>>::Mycons>(_node.v_mut()).a1;
      _loop_l = &a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe7::sum_fns(
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &l) {
  // Explicit stack replaces the non-tail recursion of sum_fns: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> *l;
  };

  struct _after_sum_fns_in_Mycons {
    crane::fn<uint64_t(std::monostate)> a0;
  };

  using _frame = std::variant<_call, _after_sum_fns_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(std::monostate)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe7::mylist<
            crane::fn<uint64_t(std::monostate)>>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_fns_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_fns_in_Mycons>(_popped));
      crane::fn<uint64_t(std::monostate)> a0 = std::move(_f.a0);
      _result = (a0(std::monostate{}) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 2: Build closures that compute the SUM of the tail.
/// Each closure captures the entire tail sublist.
MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>
MemSafetyProbe7::build_sum_closures(const MemSafetyProbe7::mylist<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>> _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>> *_write =
      nullptr;
  const MemSafetyProbe7::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      auto _value = mylist<crane::fn<uint64_t(std::monostate)>>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                      crane::fn<uint64_t(std::monostate)>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[_, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe7::mylist<
          crane::fn<uint64_t(std::monostate)>>::Mycons(
          [=](std::monostate) { return sum_list(a1_value); }, nullptr);
      MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                          crane::fn<uint64_t(std::monostate)>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(std::monostate)>>::Mycons>(_node.v_mut()).a1;
      _loop_l = &a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

/// TEST 4: Each closure captures the tail AND the current value.
/// After building all closures, call them — the captured lists
/// must be independent copies.
MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe7::build_accum_closures(
    const MemSafetyProbe7::mylist<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>> *_write =
      nullptr;
  const MemSafetyProbe7::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe7::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons(
          [=](uint64_t n) { return ((a0 + sum_list(a1_value)) + n); }, nullptr);
      MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                          crane::fn<uint64_t(uint64_t)>>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut()).a1;
      _loop_l = &a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe7::apply_all(
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> &l,
    uint64_t x) {
  // Explicit stack replaces the non-tail recursion of apply_all: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  struct _after_apply_all_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_apply_all_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = x;
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe7::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_after_apply_all_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_apply_all_in_Mycons>(_popped));
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = a0(std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Stress test — large list, each closure captures
/// the entire remaining tail.
MemSafetyProbe7::mylist<uint64_t> MemSafetyProbe7::make_nat_list(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe7::mylist<uint64_t>> _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = mylist<uint64_t>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell =
          typename MemSafetyProbe7::mylist<uint64_t>::Mycons(_loop_n, nullptr);
      MemSafetyProbe7::mylist<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<MemSafetyProbe7::mylist<uint64_t>>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _node.v_mut())
              .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}
