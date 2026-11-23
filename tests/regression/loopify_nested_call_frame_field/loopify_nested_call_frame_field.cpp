#include "loopify_nested_call_frame_field.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Loopify, g r (g r a) in two places of the same branch (one under a
/// pair match, one inside a filter predicate): the second continuation frame
/// is built as _after_g_in_pair_2{a, a1} with the const List & where its
/// field is a std::shared_ptr: "no viable conversion from 'const List<...>'
/// to 'std::shared_ptr<List<...>>'".
List<uint64_t>
LoopifyNestedCallFrameField::g(const List<std::pair<uint64_t, bool>> &l,
                               const List<uint64_t> &a) {
  // Explicit stack replaces the non-tail recursion of g: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> a;
    const List<std::pair<uint64_t, bool>> *l;
  };

  struct _after_g_in_pair {
    List<uint64_t> a;
    std::shared_ptr<List<std::pair<uint64_t, bool>>> a1;
  };

  struct _after_g_in_pair_2 {
    List<uint64_t> a;
    std::shared_ptr<List<std::pair<uint64_t, bool>>> a1;
  };

  using _frame = std::variant<_call, _after_g_in_pair, _after_g_in_pair_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{a, &l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      List<uint64_t> a = std::move(_f.a);
      const List<std::pair<uint64_t, bool>> &l = *_f.l;
      if (std::holds_alternative<typename List<std::pair<uint64_t, bool>>::Nil>(
              l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, bool>>::Cons>(l.v());
        const List<std::pair<uint64_t, bool>> &a1_value = *a1;
        const auto &[_x, _x0] = a0;
        _stack.emplace_back(_after_g_in_pair{a, a1});
        _stack.emplace_back(_call{std::move(a), crane_raw(a1)});
      }
    } else if (std::holds_alternative<_after_g_in_pair>(_popped)) {
      auto _f = std::move(std::get<_after_g_in_pair>(_popped));
      _stack.pop_back();
      List<uint64_t> a = std::move(_f.a);
      std::shared_ptr<List<std::pair<uint64_t, bool>>> a1 = std::move(_f.a1);
      const List<std::pair<uint64_t, bool>> &a1_value = *a1;
      List<uint64_t> _tmp3 = std::move(_result);
      _stack.emplace_back(_after_g_in_pair_2{std::move(a), a1});
      _stack.emplace_back(_call{std::move(_tmp3), crane_raw(a1)});
    } else {
      auto _f = std::move(std::get<_after_g_in_pair_2>(_popped));
      _stack.pop_back();
      List<uint64_t> a = std::move(_f.a);
      std::shared_ptr<List<std::pair<uint64_t, bool>>> a1 = std::move(_f.a1);
      const List<std::pair<uint64_t, bool>> &a1_value = *a1;
      _result = _result.filter([=, a1_value = a1_value, a = std::move(a)](
          uint64_t y) { return g(a1_value, g(a1_value, a)).length() == y; });
    }
  }
  return _result;
}
