#include "mem_safety_probe7.h"

uint64_t MemSafetyProbe7::sum_list(const MemSafetyProbe7::mylist<uint64_t> &l) {
  {
    const MemSafetyProbe7::mylist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const MemSafetyProbe7::mylist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// TEST 1: Build a list of closures where each captures the TAIL
/// and computes its length. The tail is unique_ptr.
MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>
MemSafetyProbe7::build_len_closures(
    const MemSafetyProbe7::mylist<uint64_t> &l) {
  std::optional<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>>
      _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>>
      *_write = nullptr;
  MemSafetyProbe7::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      auto _value = mylist<crane::fn<uint64_t(std::monostate)>>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                      crane::fn<uint64_t(std::monostate)>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe7::
          mylist<crane::fn<uint64_t(std::monostate)>>::Mycons(
              [=](std::monostate) { return a1_value.length(); }, nullptr);
      MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &_node =
          (_write
               ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                       crane::fn<uint64_t(std::monostate)>>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe7::mylist<
          crane::fn<uint64_t(std::monostate)>>::Mycons>(_node.v_mut())
                    .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe7::sum_fns(
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(std::monostate)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_fns: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(std::monostate)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe7::mylist<
            crane::fn<uint64_t(std::monostate)>>::Mycons>(l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(std::monostate)> a0 = std::move(_f.a0);
      _result = (a0(std::monostate{}) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 2: Build closures that compute the SUM of the tail.
/// Each closure captures the entire tail sublist.
MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>
MemSafetyProbe7::build_sum_closures(
    const MemSafetyProbe7::mylist<uint64_t> &l) {
  std::optional<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>>
      _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>>>
      *_write = nullptr;
  MemSafetyProbe7::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      auto _value = mylist<crane::fn<uint64_t(std::monostate)>>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                      crane::fn<uint64_t(std::monostate)>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe7::
          mylist<crane::fn<uint64_t(std::monostate)>>::Mycons(
              [=](std::monostate) { return sum_list(a1_value); }, nullptr);
      MemSafetyProbe7::mylist<crane::fn<uint64_t(std::monostate)>> &_node =
          (_write
               ? *(*_write = std::make_shared<MemSafetyProbe7::mylist<
                       crane::fn<uint64_t(std::monostate)>>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe7::mylist<
          crane::fn<uint64_t(std::monostate)>>::Mycons>(_node.v_mut())
                    .a1;
      _loop_l = a1_value;
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
  std::optional<MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = nullptr;
  MemSafetyProbe7::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe7::
          mylist<crane::fn<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t n) { return ((a0 + sum_list(a1_value)) + n); },
              nullptr);
      MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write
               ? *(*_write = std::make_shared<
                       MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe7::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut())
                    .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe7::apply_all(
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> &l,
    uint64_t x) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    const MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified apply_all: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe7::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = x;
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe7::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
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

/// TEST 6: Stress test — large list, each closure captures
/// the entire remaining tail.
MemSafetyProbe7::mylist<uint64_t> MemSafetyProbe7::make_nat_list(uint64_t n) {
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
      _write = &std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
                    _node.v_mut())
                    .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}
