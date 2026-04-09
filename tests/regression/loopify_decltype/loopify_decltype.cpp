#include <loopify_decltype.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
__attribute__((pure)) unsigned int
LoopifyDecltype::count_true(const std::shared_ptr<List<bool>> &xs) {
  struct _Enter {
    const std::shared_ptr<List<bool>> xs;
  };

  struct _Call1 {
    unsigned int _s0;
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
              const std::shared_ptr<List<bool>> xs = _f.xs;
              std::visit(
                  Overloaded{
                      [&](const typename List<bool>::Nil _args) -> void {
                        _result = 0u;
                      },
                      [&](const typename List<bool>::Cons _args) -> void {
                        _stack.push_back(_Call1{[&]() -> unsigned int {
                          if (_args.d_a0) {
                            return 1u;
                          } else {
                            return 0u;
                          }
                        }()});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  xs->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyDecltype::sum_flagged(
    const std::shared_ptr<List<std::shared_ptr<LoopifyDecltype::item>>> &xs) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyDecltype::item>>> xs;
  };

  struct _Call1 {
    unsigned int _s0;
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
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyDecltype::item>>>
                  xs = _f.xs;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyDecltype::item>>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<LoopifyDecltype::item>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{[&]() -> unsigned int {
                          if (_args.d_a0->item_flag) {
                            return _args.d_a0->item_val;
                          } else {
                            return 0u;
                          }
                        }()});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  xs->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}
