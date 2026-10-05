#include "mem_safety_probe4.h"

/// TEST 1: Partial app applied to recursive result.
/// The closure f captures tree t by &, but must survive across the
/// recursive call in the loopified version.
/// f(sum_through(xs)) requires f to be stored in a continuation frame.
uint64_t MemSafetyProbe4::sum_through(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    MemSafetyProbe4::tree a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_through: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      MemSafetyProbe4::tree a0 = std::move(_f.a0);
      _result = a0.sum_values(std::move(_result));
    }
  }
  return _result;
}

/// TEST 2: Recursive result + partial app result.
/// add_through(xs) + f(0): f might be pre-evaluated or stored in frame.
uint64_t MemSafetyProbe4::add_through(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// CraneCont_Mycons: saves [f], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> f;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified add_through: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(CraneCont_Mycons{std::move(f)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> f = std::move(_f.f);
      _result = (std::move(_result) + f(UINT64_C(0)));
    }
  }
  return _result;
}

/// TEST 3: Two partial apps from same tree, used around recursive call.
uint64_t MemSafetyProbe4::double_partial(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// CraneCont_Mycons: saves [f, g], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> f;
    crane::fn<uint64_t(uint64_t)> g;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified double_partial: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &a1_value = *a1;
        crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        crane::fn<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(CraneCont_Mycons{std::move(f), std::move(g)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> f = std::move(_f.f);
      crane::fn<uint64_t(uint64_t)> g = std::move(_f.g);
      _result = (f(std::move(_result)) + g(UINT64_C(0)));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::weighted_sum(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l,
    uint64_t w) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t w;
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// CraneCont_Mycons: saves [f, w], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> f;
    uint64_t w;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{w, &l});
  /// Loopified weighted_sum: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t w = _f.w;
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &a1_value = *a1;
        crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(CraneCont_Mycons{f, w});
        _stack.emplace_back(CraneEnter{f(UINT64_C(0)), crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> f = std::move(_f.f);
      uint64_t w = _f.w;
      _result = (f(w) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 5: Map building new trees from partial app results across recursion.
MemSafetyProbe4::mylist<uint64_t> MemSafetyProbe4::transform_list(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l) {
  std::optional<MemSafetyProbe4::mylist<uint64_t>> _root{};
  std::shared_ptr<MemSafetyProbe4::mylist<uint64_t>> *_write = nullptr;
  const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
            _loop_l->v())) {
      auto _value = mylist<uint64_t>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe4::mylist<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
          _loop_l->v());
      crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return a0.sum_values(_x0);
      };
      auto _cell = typename MemSafetyProbe4::mylist<uint64_t>::Mycons(
          f(UINT64_C(0)), nullptr);
      MemSafetyProbe4::mylist<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<MemSafetyProbe4::mylist<uint64_t>>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe4::mylist<uint64_t>::Mycons>(
                    _node.v_mut())
                    .a1;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe4::mysum(const MemSafetyProbe4::mylist<uint64_t> &
                                    l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe4::mylist<uint64_t> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified mysum: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe4::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe4::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::process_list(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// CraneCont_Mycons: saves [f], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> f;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified process_list: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &a1_value = *a1;
        crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(CraneCont_Mycons{std::move(f)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> f = std::move(_f.f);
      _result = apply_to(std::move(f), std::move(_result));
    }
  }
  return _result;
}

/// TEST 7: Nested recursion with closure capture across calls.
uint64_t MemSafetyProbe4::nested_apply(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l, uint64_t base) {
  uint64_t _loop_base = base;
  const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
            _loop_l->v())) {
      return _loop_base;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
          _loop_l->v());
      crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return a0.sum_values(_x0);
      };
      _loop_base = f(_loop_base);
      _loop_l = crane_raw(a1);
    }
  }
}
