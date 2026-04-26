#include <loopify_decltype.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
__attribute__((pure)) unsigned int
LoopifyDecltype::count_true(const List<bool> &xs) {
  struct _Enter {
    const List<bool> xs;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{xs});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<bool> xs = _f.xs;
      if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<bool>::Cons>(xs.v());
        _stack.emplace_back(_Call1{[&]() -> unsigned int {
          if (d_a0) {
            return 1u;
          } else {
            return 0u;
          }
        }()});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyDecltype::sum_flagged(const List<LoopifyDecltype::item> &xs) {
  struct _Enter {
    const List<LoopifyDecltype::item> xs;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{xs});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyDecltype::item> xs = _f.xs;
      if (std::holds_alternative<typename List<LoopifyDecltype::item>::Nil>(
              xs.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyDecltype::item>::Cons>(xs.v());
        _stack.emplace_back(_Call1{[&]() -> unsigned int {
          if (d_a0.item_flag) {
            return d_a0.item_val;
          } else {
            return 0u;
          }
        }()});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
