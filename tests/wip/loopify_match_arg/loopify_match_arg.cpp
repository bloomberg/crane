#include <loopify_match_arg.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Count the number of Dot cells in a list.
/// The match on c inside the Cons branch triggers bug 2.
__attribute__((pure)) unsigned int LoopifyMatchArg::count_dots(
    const std::shared_ptr<List<LoopifyMatchArg::Cell>> &xs) {
  struct _Enter {
    const std::shared_ptr<List<LoopifyMatchArg::Cell>> xs;
  };

  using _Frame = std::variant<_Enter>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{xs});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
          const std::shared_ptr<List<LoopifyMatchArg::Cell>> xs = _f.xs;
          std::visit(
              Overloaded{
                  [&](const typename List<LoopifyMatchArg::Cell>::Nil _args)
                      -> void { _result = 0u; },
                  [](const typename List<LoopifyMatchArg::Cell>::Cons _args)
                      -> void {
                    switch (_args.d_a0) {
                    case Cell::e_DOT: {
                      return (1u + count_dots(_args.d_a1));
                    }
                    default: {
                      return count_dots(_args.d_a1);
                    }
                    }
                  }},
              xs->v());
        }},
        _frame);
  }
  return _result;
}

/// A plain recursive length — triggers bug 1 (missing <vector>)
/// when loopify converts it to an explicit-stack loop.
__attribute__((pure)) unsigned int LoopifyMatchArg::my_length(
    const std::shared_ptr<List<LoopifyMatchArg::Cell>> &xs) {
  struct _Enter {
    const std::shared_ptr<List<LoopifyMatchArg::Cell>> xs;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{xs});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<LoopifyMatchArg::Cell>> xs = _f.xs;
              std::visit(
                  Overloaded{
                      [&](const typename List<LoopifyMatchArg::Cell>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<LoopifyMatchArg::Cell>::Cons
                              _args) -> void {
                        _stack.push_back(_Call1{1u});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  xs->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}
