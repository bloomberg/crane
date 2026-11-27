#include "loopify_top_level_call_binding.h"

/// A recursive call bound at the top of a function's body, the rest of
/// the body after it.
///
/// csum's body matches nothing: it adds key c to a local fixpoint
/// applied to kids c, which Normalize binds first.  The machine adopts
/// the fixpoint, which calls back into csum, and reroutes the bound call
/// to it.  The machine rewrote its body one top-level statement at a time,
/// so the binding never resumed into the addition after it, and the
/// rerouted call was left naming the entry, which is no function.
uint64_t
LoopifyTopLevelCallBinding::key(const LoopifyTopLevelCallBinding::cell &c) {
  const auto &[key1, _] =
      std::get<typename LoopifyTopLevelCallBinding::cell::MkCell>(c.v());
  return key1;
}

List<LoopifyTopLevelCallBinding::cell>
LoopifyTopLevelCallBinding::kids(const LoopifyTopLevelCallBinding::cell &c) {
  const auto &[_, kids1] =
      std::get<typename LoopifyTopLevelCallBinding::cell::MkCell>(c.v());
  return *kids1;
}

uint64_t
LoopifyTopLevelCallBinding::csum(const LoopifyTopLevelCallBinding::cell &c) {
  // Explicit stack replaces the non-tail recursion of csum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    LoopifyTopLevelCallBinding::cell c;
  };

  struct _call_go {
    List<LoopifyTopLevelCallBinding::cell> l;
  };

  struct _after_csum_in_Cons {
    std::shared_ptr<List<LoopifyTopLevelCallBinding::cell>> a1;
  };

  struct _after_go {
    LoopifyTopLevelCallBinding::cell c;
  };

  struct _after_go_in_Cons {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _call_go, _after_csum_in_Cons, _after_go,
                              _after_go_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{c});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      LoopifyTopLevelCallBinding::cell c = std::move(_f.c);
      _stack.emplace_back(_after_go{c});
      _stack.emplace_back(_call_go{kids(std::move(c))});
    } else if (std::holds_alternative<_call_go>(_popped)) {
      auto _f = std::move(std::get<_call_go>(_popped));
      _stack.pop_back();
      const List<LoopifyTopLevelCallBinding::cell> &l = _f.l;
      if (std::holds_alternative<
              typename List<LoopifyTopLevelCallBinding::cell>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyTopLevelCallBinding::cell>::Cons>(
                l.v());
        _stack.emplace_back(_after_csum_in_Cons{a1});
        _stack.emplace_back(_call{a0});
      }
    } else if (std::holds_alternative<_after_csum_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_csum_in_Cons>(_popped));
      _stack.pop_back();
      std::shared_ptr<List<LoopifyTopLevelCallBinding::cell>> a1 =
          std::move(_f.a1);
      _stack.emplace_back(_after_go_in_Cons{_result});
      _stack.emplace_back(_call_go{*a1});
    } else if (std::holds_alternative<_after_go>(_popped)) {
      auto _f = std::move(std::get<_after_go>(_popped));
      _stack.pop_back();
      LoopifyTopLevelCallBinding::cell c = std::move(_f.c);
      _result = (key(std::move(c)) + _result);
    } else {
      auto _f = std::move(std::get<_after_go_in_Cons>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + _result);
    }
  }
  return _result;
}

/// A chain n cells deep, each holding k.
LoopifyTopLevelCallBinding::cell LoopifyTopLevelCallBinding::chain(uint64_t n,
                                                                   uint64_t k) {
  // Explicit stack replaces the non-tail recursion of chain: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_chain_in_S {};

  using _frame = std::variant<_call, _after_chain_in_S>;
  LoopifyTopLevelCallBinding::cell _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result =
            cell::mkcell(k, List<LoopifyTopLevelCallBinding::cell>::nil());
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_chain_in_S{});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_chain_in_S>(_popped));
      _stack.pop_back();
      _result =
          cell::mkcell(k, List<LoopifyTopLevelCallBinding::cell>::cons(
                              std::move(_result),
                              List<LoopifyTopLevelCallBinding::cell>::nil()));
    }
  }
  return _result;
}
