#include "loopify_mutual_frame_untyped_binder.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// Under Loopify, a mutual fixpoint whose recursive branch nests a non-tail
/// local fixpoint (its base read by an inner local fixpoint) under mod fails
/// the frame-plan check under CRANE_CHECK_IR=1: "a frame keeps a binder whose
/// local was declared at no type".
///
/// go16's machine kept n12, a capture of the enclosing function, which
/// the rest reads through go22's call: the inner loop dropped the
/// argument that named it, so the machine's body no longer did, and only
/// what the body names counted as bound outside the machine.  Its handler
/// even assigned the frame's copy back to the captured n12.  A local
/// fixpoint's captures now count as invariant whether or not the body
/// names them.
uint64_t LoopifyMutualFrameUntypedBinder::tree_obs(
    const LoopifyMutualFrameUntypedBinder::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_obs: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualFrameUntypedBinder::tree *t;
  };

  struct _after_tree_obs_in_Node {
    uint64_t a1;
    const LoopifyMutualFrameUntypedBinder::tree *a2;
  };

  struct _after_tree_obs_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tree_obs_in_Node, _after_tree_obs_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualFrameUntypedBinder::tree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMutualFrameUntypedBinder::tree::Leaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMutualFrameUntypedBinder::tree::Node>(
                t.v());
        _stack.emplace_back(_after_tree_obs_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_obs_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_obs_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyMutualFrameUntypedBinder::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_obs_in_Node_2{a1, _result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_obs_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      auto _once1 = (((_f._tmp2 * UINT64_C(7)) + a1) + (_result * UINT64_C(3)));
      _result = (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
    }
  }
  return _result;
}

std::optional<Sum<uint64_t, String>>
LoopifyMutualFrameUntypedBinder::h1a(uint64_t,
                                     const std::pair<List<String>, bool> &) {
  return std::optional<Sum<uint64_t, String>>();
}

uint64_t
LoopifyMutualFrameUntypedBinder::h1b(uint64_t n12,
                                     const List<std::optional<uint64_t>> &) {
  if (n12 <= 0) {
    auto _once1 = [&]() -> uint64_t {
      if (n12 <= 0) {
        return UINT64_C(260);
      } else {
        uint64_t _x0 = n12 - 1;
        return tree_obs(tree::node(tree::leaf(), UINT64_C(272), tree::leaf()));
      }
    }();
    auto _once2 = tree_obs([&]() -> LoopifyMutualFrameUntypedBinder::tree {
      if (n12 <= 0) {
        return tree::node(tree::leaf(), UINT64_C(12), tree::leaf());
      } else {
        uint64_t _x0 = n12 - 1;
        return tree::node(tree::leaf(), UINT64_C(11), tree::leaf());
      }
    }());
    return (((_once1 - _once2) > _once1 ? 0 : (_once1 - _once2)));
  } else {
    uint64_t m15 = n12 - 1;
    auto _once3 = [&]() {
      auto go16 = [&](const List<bool> &l17, uint64_t) -> uint64_t {
        // Explicit stack replaces the non-tail recursion of go16: _call frames
        // are pending calls, _after frames resume a caller.
        struct _call {
          const List<bool> *l17;
        };

        struct _after_go16_in_Cons {};

        using _frame = std::variant<_call, _after_go16_in_Cons>;
        uint64_t _result{};
        crane::small_vector<_frame> _stack;
        _stack.emplace_back(_call{&l17});
        while (!_stack.empty()) {
          _frame &_popped = _stack.back();
          if (std::holds_alternative<_call>(_popped)) {
            auto _f = std::move(std::get<_call>(_popped));
            _stack.pop_back();
            const List<bool> &l17 = *_f.l17;
            if (std::holds_alternative<typename List<bool>::Nil>(l17.v())) {
              _result = tree_obs(
                  tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
            } else {
              const auto &[_, a1] =
                  std::get<typename List<bool>::Cons>(l17.v());
              _stack.emplace_back(_after_go16_in_Cons{});
              _stack.emplace_back(_call{crane_raw(a1)});
            }
          } else {
            auto _f = std::move(std::get<_after_go16_in_Cons>(_popped));
            _stack.pop_back();
            uint64_t rv21 = _result;
            auto go22 = [&](const List<String> &l23, uint64_t) -> uint64_t {
              // Loop replaces the tail recursion: each recursive call updates
              // the loop variables.
              const List<String> *_loop_l23 = &l23;
              while (true) {
                if (std::holds_alternative<typename List<String>::Nil>(
                        _loop_l23->v())) {
                  return rv21;
                } else {
                  const auto &[_, a10] =
                      std::get<typename List<String>::Cons>(_loop_l23->v());
                  _loop_l23 = crane_raw(a10);
                }
              }
            };
            _result = go22(List<String>::cons(
                String::emptystring(),
                List<String>::cons(String::string0(
                    Ascii::ascii0(false, false, false, true, false, true, true,
                                  false),
                    String::string0(
                        Ascii::ascii0(true, false, true, false, false, true,
                                      true, false),
                        String::string0(
                            Ascii::ascii0(false, false, true, true, false, true,
                                          true, false),
                            String::string0(
                                Ascii::ascii0(false, false, true, true, false,
                                              true, true, false),
                                String::string0(
                                    Ascii::ascii0(true, true, true, true, false,
                                                  true, true, false),
                                    String::emptystring()))))),
                                   List<String>::nil())),
                           UINT64_C(11));
          }
        }
        return _result;
      };
      return go16(mon_list<bool>::mop(
          List<bool>::cons(
              true,
              List<bool>::cons(true,
                               List<bool>::cons(false, List<bool>::nil()))),
          List<bool>::cons(false, List<bool>::cons(true, List<bool>::nil()))),
                  n12);
    }();
    auto _once4 = [&]() -> uint64_t {
      if (n12 <= 0) {
        return m15;
      } else {
        uint64_t m28 = n12 - 1;
        return m28;
      }
    }();
    return (_once4 ? _once3 % _once4 : _once3);
  }
}
