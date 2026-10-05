#include "mem_safety_probe6.h"

/// TEST 5: Chain of closures each pre-computing from the tail.
MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe6::build_chain(const MemSafetyProbe6::mylist<uint64_t> &l) {
  std::optional<MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = nullptr;
  MemSafetyProbe6::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe6::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe6::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe6::mylist<uint64_t> &a1_value = *a1;
      uint64_t rest_len = a1_value.length();
      auto _cell = typename MemSafetyProbe6::
          mylist<crane::fn<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t n) { return ((a0 + rest_len) + n); }, nullptr);
      MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write
               ? *(*_write = std::make_shared<
                       MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe6::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut())
                    .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe6::apply_chain(
    const MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>> &fns,
    uint64_t x) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    const MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>> *fns;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&fns});
  /// Loopified apply_chain: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe6::mylist<crane::fn<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe6::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = x;
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe6::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(fns.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = a0(std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Closure captures tail, then tail is used again
/// after the closure is created — tests double use.
uint64_t
MemSafetyProbe6::capture_and_reuse(uint64_t,
                                   const MemSafetyProbe6::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename MemSafetyProbe6::mylist<uint64_t>::Mynil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename MemSafetyProbe6::mylist<uint64_t>::Mycons>(l.v());
    const MemSafetyProbe6::mylist<uint64_t> &a1_value = *a1;
    crane::fn<uint64_t(uint64_t)> f = [=](uint64_t n) {
      return (a1_value.length() + n);
    };
    uint64_t tail_len = a1_value.length();
    return (f(a0) + tail_len);
  }
}
