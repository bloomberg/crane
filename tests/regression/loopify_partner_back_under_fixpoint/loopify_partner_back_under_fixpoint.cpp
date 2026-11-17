#include "loopify_partner_back_under_fixpoint.h"

/// tree_size's partner forest_size calls it back only from a local
/// fixpoint over a list of trees, and tree_size calls forest_size as
/// the operand of an addition.  No machine can enter forest_size, so its
/// body is spliced in place of the call.  The addition is then copied into
/// the one branch of the match the body is, which applies the local
/// fixpoint where tree_size's machine runs it as a loop of its own: the
/// calls of tree_size in it are turns, and a chain of any depth runs in
/// one C++ frame.
uint64_t LoopifyPartnerBackUnderFixpoint::tree_size(
    const LoopifyPartnerBackUnderFixpoint::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_size: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPartnerBackUnderFixpoint::tree *t;
  };

  struct _call_sizes {
    const List<LoopifyPartnerBackUnderFixpoint::tree> *l;
  };

  struct _after_sizes_in_Cons {
    uint64_t _tmp2;
  };

  struct _after_sizes_in_Forest0 {
    uint64_t n0;
  };

  struct _after_tree_size_in_Cons {
    const List<LoopifyPartnerBackUnderFixpoint::tree> *a11;
  };

  using _frame =
      std::variant<_call, _call_sizes, _after_sizes_in_Cons,
                   _after_sizes_in_Forest0, _after_tree_size_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyPartnerBackUnderFixpoint::tree &t = *_f.t;
      const auto &[n0, kids0] =
          std::get<typename LoopifyPartnerBackUnderFixpoint::tree::Node>(t.v());
      auto &&_sv0 = *kids0;
      const auto &[ts0] =
          std::get<typename LoopifyPartnerBackUnderFixpoint::forest::Forest0>(
              _sv0.v());
      _stack.emplace_back(_after_sizes_in_Forest0{n0});
      _stack.emplace_back(_call_sizes{crane_raw(ts0)});
    } else if (std::holds_alternative<_call_sizes>(_popped)) {
      auto _f = std::move(std::get<_call_sizes>(_popped));
      _stack.pop_back();
      const List<LoopifyPartnerBackUnderFixpoint::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename List<LoopifyPartnerBackUnderFixpoint::tree>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a01, a11] = std::get<
            typename List<LoopifyPartnerBackUnderFixpoint::tree>::Cons>(l.v());
        _stack.emplace_back(_after_tree_size_in_Cons{crane_raw(a11)});
        _stack.emplace_back(_call{&a01});
      }
    } else if (std::holds_alternative<_after_sizes_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_sizes_in_Cons>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    } else if (std::holds_alternative<_after_sizes_in_Forest0>(_popped)) {
      auto _f = std::move(std::get<_after_sizes_in_Forest0>(_popped));
      _stack.pop_back();
      uint64_t n0 = _f.n0;
      _result = (n0 + std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_tree_size_in_Cons>(_popped));
      _stack.pop_back();
      const List<LoopifyPartnerBackUnderFixpoint::tree> &a11 = *_f.a11;
      _stack.emplace_back(_after_sizes_in_Cons{std::move(_result)});
      _stack.emplace_back(_call_sizes{&a11});
    }
  }
  return _result;
}

uint64_t LoopifyPartnerBackUnderFixpoint::forest_size(
    const LoopifyPartnerBackUnderFixpoint::forest &f) {
  const auto &[ts0] = std::get<
      typename LoopifyPartnerBackUnderFixpoint::forest::Forest0>(f.v());
  auto sizes =
      [&](const List<LoopifyPartnerBackUnderFixpoint::tree> &l) -> uint64_t {
        // Explicit stack replaces the non-tail recursion of sizes: _call frames
        // are pending calls, _after frames resume a caller.
        struct _call {
          const List<LoopifyPartnerBackUnderFixpoint::tree> *l;
        };

        struct _after_sizes_in_Cons {
          uint64_t _tmp2;
        };

        using _frame = std::variant<_call, _after_sizes_in_Cons>;
        uint64_t _result{};
        crane::small_vector<_frame> _stack;
        _stack.emplace_back(_call{&l});
        while (!_stack.empty()) {
          _frame &_popped = _stack.back();
          if (std::holds_alternative<_call>(_popped)) {
            auto _f = std::move(std::get<_call>(_popped));
            _stack.pop_back();
            const List<LoopifyPartnerBackUnderFixpoint::tree> &l = *_f.l;
            if (std::holds_alternative<
                    typename List<LoopifyPartnerBackUnderFixpoint::tree>::Nil>(
                    l.v())) {
              _result = UINT64_C(0);
            } else {
              const auto &[a00, a10] = std::get<
                  typename List<LoopifyPartnerBackUnderFixpoint::tree>::Cons>(
                  l.v());
              _stack.emplace_back(_after_sizes_in_Cons{tree_size(a00)});
              _stack.emplace_back(_call{crane_raw(a10)});
            }
          } else {
            auto _f = std::move(std::get<_after_sizes_in_Cons>(_popped));
            _stack.pop_back();
            _result = (_f._tmp2 + std::move(_result));
          }
        }
        return _result;
      };
  return sizes(*ts0);
}

LoopifyPartnerBackUnderFixpoint::tree LoopifyPartnerBackUnderFixpoint::chain(
    uint64_t k, LoopifyPartnerBackUnderFixpoint::tree t) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyPartnerBackUnderFixpoint::tree _loop_t = std::move(t);
  uint64_t _loop_k = k;
  while (true) {
    if (_loop_k <= 0) {
      return _loop_t;
    } else {
      uint64_t k_ = _loop_k - 1;
      _loop_t = tree::node(
          UINT64_C(1),
          forest::forest0(List<LoopifyPartnerBackUnderFixpoint::tree>::cons(
              std::move(_loop_t),
              List<LoopifyPartnerBackUnderFixpoint::tree>::cons(
                  tree::node(
                      UINT64_C(1),
                      forest::forest0(
                          List<LoopifyPartnerBackUnderFixpoint::tree>::nil())),
                  List<LoopifyPartnerBackUnderFixpoint::tree>::nil()))));
      _loop_k = k_;
    }
  }
}
