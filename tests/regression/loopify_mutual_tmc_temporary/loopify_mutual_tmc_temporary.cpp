#include "loopify_mutual_tmc_temporary.h"

/// Tail modulo cons through a partner's body.
///
/// eb's tail call to ea continues in ea's body, where ea calls eb
/// under the constructor Su: eb is lowered tail modulo cons.  Normalize
/// binds that call to a temporary, which Loopify puts back before reading
/// the constructor around it, knowing a temporary by its name.  Inlining
/// ea renamed every local of its body, the temporary too, so it was not
/// put back, the transform found no constructor around the call and left it
/// a call, and under CRANE_CHECK_IR the plan's chains were contradicted.
/// db meets the same through da's match on an enum.
LoopifyMutualTmcTemporary::num
LoopifyMutualTmcTemporary::ea(const LoopifyMutualTmcTemporary::num &n) {
  // Explicit stack replaces the non-tail recursion of ea: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualTmcTemporary::num *n;
  };

  struct _call_eb_entry {
    LoopifyMutualTmcTemporary::num x;
    const LoopifyMutualTmcTemporary::num *n0;
  };

  struct _after_eb_entry_in_Su {};

  using _frame = std::variant<_call, _call_eb_entry, _after_eb_entry_in_Su>;
  LoopifyMutualTmcTemporary::num _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualTmcTemporary::num &n = *_f.n;
      if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
              n.v())) {
        _result = num::z();
      } else {
        const auto &[n0] =
            std::get<typename LoopifyMutualTmcTemporary::num::Su>(n.v());
        _stack.emplace_back(_after_eb_entry_in_Su{});
        _stack.emplace_back(_call_eb_entry{
            [&]() {
              auto &&_sv1 = *n0;
              if (std::holds_alternative<
                      typename LoopifyMutualTmcTemporary::num::Z>(_sv1.v())) {
                return num::z();
              } else {
                const auto &[n1] =
                    std::get<typename LoopifyMutualTmcTemporary::num::Su>(
                        _sv1.v());
                return *n1;
              }
            }(),
            crane_raw(n0)});
      }
    } else if (std::holds_alternative<_call_eb_entry>(_popped)) {
      auto _f = std::move(std::get<_call_eb_entry>(_popped));
      _stack.pop_back();
      LoopifyMutualTmcTemporary::num x = std::move(_f.x);
      const LoopifyMutualTmcTemporary::num &n0 = *_f.n0;
      if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
              n0.v())) {
        _result = std::move(x);
      } else {
        const auto &[n1] =
            std::get<typename LoopifyMutualTmcTemporary::num::Su>(n0.v());
        _stack.emplace_back(_call{crane_raw(n1)});
      }
    } else {
      auto _f = std::move(std::get<_after_eb_entry_in_Su>(_popped));
      _stack.pop_back();
      _result = num::su(std::move(_result));
    }
  }
  return _result;
}

LoopifyMutualTmcTemporary::num
LoopifyMutualTmcTemporary::eb(const LoopifyMutualTmcTemporary::num &n,
                              LoopifyMutualTmcTemporary::num x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyMutualTmcTemporary::num> _root{};
  std::shared_ptr<LoopifyMutualTmcTemporary::num> *_write = nullptr;
  LoopifyMutualTmcTemporary::num _loop_x = std::move(x);
  const LoopifyMutualTmcTemporary::num *_loop_n = &n;
  while (true) {
    if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
            _loop_n->v())) {
      auto _value = std::move(_loop_x);
      (_write ? *(*_write = std::make_shared<LoopifyMutualTmcTemporary::num>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[n0] =
          std::get<typename LoopifyMutualTmcTemporary::num::Su>(_loop_n->v());
      auto &&_sv0 = *n0;
      if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
              _sv0.v())) {
        auto _value = num::z();
        (_write ? *(*_write = std::make_shared<LoopifyMutualTmcTemporary::num>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[n1] =
            std::get<typename LoopifyMutualTmcTemporary::num::Su>(_sv0.v());
        auto _cell = typename LoopifyMutualTmcTemporary::num::Su(nullptr);
        LoopifyMutualTmcTemporary::num &_node =
            (_write ? *(*_write =
                            std::make_shared<LoopifyMutualTmcTemporary::num>(
                                std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyMutualTmcTemporary::num::Su>(
                _node.v_mut())
                .n;
        _loop_x = [&]() {
          auto &&_sv1 = *n1;
          if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
                  _sv1.v())) {
            return num::z();
          } else {
            const auto &[n2] =
                std::get<typename LoopifyMutualTmcTemporary::num::Su>(_sv1.v());
            return *n2;
          }
        }();
        _loop_n = crane_raw(n1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

LoopifyMutualTmcTemporary::num
LoopifyMutualTmcTemporary::da(LoopifyMutualTmcTemporary::Color c,
                              const LoopifyMutualTmcTemporary::num &n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyMutualTmcTemporary::num *_loop_n = &n;
  while (true) {
    if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
            _loop_n->v())) {
      return num::z();
    } else {
      const auto &[n0] =
          std::get<typename LoopifyMutualTmcTemporary::num::Su>(_loop_n->v());
      switch (c) {
      case Color::RED: {
        return db(*n0);
      }
      case Color::GREEN: {
        return num::su(db(*n0));
      }
      case Color::BLUE: {
        _loop_n = crane_raw(n0);
        c = Color::RED;
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
}

LoopifyMutualTmcTemporary::num
LoopifyMutualTmcTemporary::db(const LoopifyMutualTmcTemporary::num &n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyMutualTmcTemporary::num> _root{};
  std::shared_ptr<LoopifyMutualTmcTemporary::num> *_write = nullptr;
  const LoopifyMutualTmcTemporary::num *_loop_n = &n;
  while (true) {
    if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
            _loop_n->v())) {
      auto _value = num::su(num::z());
      (_write ? *(*_write = std::make_shared<LoopifyMutualTmcTemporary::num>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[n0] =
          std::get<typename LoopifyMutualTmcTemporary::num::Su>(_loop_n->v());
      LoopifyMutualTmcTemporary::Color c = Color::BLUE;
      auto &&_sv0 = *n0;
      if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
              _sv0.v())) {
        auto _value = num::z();
        (_write ? *(*_write = std::make_shared<LoopifyMutualTmcTemporary::num>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[n1] =
            std::get<typename LoopifyMutualTmcTemporary::num::Su>(_sv0.v());
        switch (c) {
        case Color::RED: {
          _loop_n = crane_raw(n1);
          continue;
          break;
        }
        case Color::GREEN: {
          auto _cell = typename LoopifyMutualTmcTemporary::num::Su(nullptr);
          LoopifyMutualTmcTemporary::num &_node =
              (_write ? *(*_write =
                              std::make_shared<LoopifyMutualTmcTemporary::num>(
                                  std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename LoopifyMutualTmcTemporary::num::Su>(
                  _node.v_mut())
                  .n;
          _loop_n = crane_raw(n1);
          continue;
          break;
        }
        case Color::BLUE: {
          auto _value = da(Color::RED, *n1);
          (
              _write ? *(*_write =
                             std::make_shared<LoopifyMutualTmcTemporary::num>(
                                 std::move(_value)))
                     : _root.emplace(std::move(_value)));
          return std::move(*_root);
        }
        default:
          std::unreachable();
        }
      }
    }
  }
  return std::move(*_root);
}

LoopifyMutualTmcTemporary::num LoopifyMutualTmcTemporary::of_nat(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyMutualTmcTemporary::num> _root{};
  std::shared_ptr<LoopifyMutualTmcTemporary::num> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = num::z();
      (_write ? *(*_write = std::make_shared<LoopifyMutualTmcTemporary::num>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename LoopifyMutualTmcTemporary::num::Su(nullptr);
      LoopifyMutualTmcTemporary::num &_node = (
          _write ? *(*_write = std::make_shared<LoopifyMutualTmcTemporary::num>(
                         std::move(_cell)))
                 : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyMutualTmcTemporary::num::Su>(_node.v_mut()).n;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t
LoopifyMutualTmcTemporary::to_nat(const LoopifyMutualTmcTemporary::num &n) {
  // Explicit stack replaces the non-tail recursion of to_nat: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualTmcTemporary::num *n;
  };

  struct _after_to_nat_in_Su {};

  using _frame = std::variant<_call, _after_to_nat_in_Su>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualTmcTemporary::num &n = *_f.n;
      if (std::holds_alternative<typename LoopifyMutualTmcTemporary::num::Z>(
              n.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[n0] =
            std::get<typename LoopifyMutualTmcTemporary::num::Su>(n.v());
        _stack.emplace_back(_after_to_nat_in_Su{});
        _stack.emplace_back(_call{crane_raw(n0)});
      }
    } else {
      auto _f = std::move(std::get<_after_to_nat_in_Su>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyMutualTmcTemporary::run_ea(uint64_t n) {
  return to_nat(ea(of_nat(n)));
}

uint64_t LoopifyMutualTmcTemporary::run_eb(uint64_t n, uint64_t x) {
  return to_nat(eb(of_nat(n), of_nat(x)));
}

uint64_t LoopifyMutualTmcTemporary::run_da(LoopifyMutualTmcTemporary::Color c,
                                           uint64_t n) {
  return to_nat(da(c, of_nat(n)));
}

uint64_t LoopifyMutualTmcTemporary::run_db(uint64_t n) {
  return to_nat(db(of_nat(n)));
}
