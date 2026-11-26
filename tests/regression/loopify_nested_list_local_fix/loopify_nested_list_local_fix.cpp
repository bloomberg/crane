#include "loopify_nested_list_local_fix.h"

LoopifyNestedListLocalFix::mterm LoopifyNestedListLocalFix::h(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyNestedListLocalFix::mterm> _root{};
  std::shared_ptr<LoopifyNestedListLocalFix::mterm> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = mterm::mlit(UINT64_C(0));
      (_write ? *(*_write = std::make_shared<LoopifyNestedListLocalFix::mterm>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename LoopifyNestedListLocalFix::mterm::MAdd(
          nullptr,
          std::make_shared<List<LoopifyNestedListLocalFix::mterm>>(List<
              LoopifyNestedListLocalFix::mterm>::cons(
              []() {
                auto go =
                    [](const List<uint64_t> &l) -> LoopifyNestedListLocalFix::mterm {
                      // Loop replaces the tail recursion: each recursive call
                      // updates the loop variables.
                      const List<uint64_t> *_loop_l = &l;
                      while (true) {
                        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                                _loop_l->v())) {
                          return mterm::mlit(UINT64_C(1));
                        } else {
                          const auto &[_, a1] =
                              std::get<typename List<uint64_t>::Cons>(
                                  _loop_l->v());
                          _loop_l = crane_raw(a1);
                        }
                      }
                    };
                return go(List<uint64_t>::nil());
              }(),
              List<LoopifyNestedListLocalFix::mterm>::nil())));
      LoopifyNestedListLocalFix::mterm &_node =
          (_write ? *(*_write =
                          std::make_shared<LoopifyNestedListLocalFix::mterm>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyNestedListLocalFix::mterm::MAdd>(
              _node.v_mut())
              .a0;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}

LoopifyNestedListLocalFix::mterm LoopifyNestedListLocalFix::h2(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyNestedListLocalFix::mterm> _root{};
  std::shared_ptr<LoopifyNestedListLocalFix::mterm> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = mterm::mlit(UINT64_C(0));
      (_write ? *(*_write = std::make_shared<LoopifyNestedListLocalFix::mterm>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename LoopifyNestedListLocalFix::mterm::MAdd(
          nullptr,
          std::make_shared<List<LoopifyNestedListLocalFix::mterm>>(
              List<LoopifyNestedListLocalFix::mterm>::cons(
                  mterm::mlit(UINT64_C(0)),
                  List<LoopifyNestedListLocalFix::mterm>::cons(
                      List<bool>::cons(true,
                                       List<bool>::nil())
                          .template fold_left<LoopifyNestedListLocalFix::mterm>(
                          [](LoopifyNestedListLocalFix::mterm acc,
                             bool) { return acc; },
                          mterm::mlit(UINT64_C(0))),
                      List<LoopifyNestedListLocalFix::mterm>::nil()))));
      LoopifyNestedListLocalFix::mterm &_node =
          (_write ? *(*_write =
                          std::make_shared<LoopifyNestedListLocalFix::mterm>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyNestedListLocalFix::mterm::MAdd>(
              _node.v_mut())
              .a0;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t
LoopifyNestedListLocalFix::size(const LoopifyNestedListLocalFix::mterm &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyNestedListLocalFix::mterm *t;
  };

  struct _after_size_in_MAdd {
    std::shared_ptr<List<LoopifyNestedListLocalFix::mterm>> a1;
  };

  using _frame = std::variant<_call, _after_size_in_MAdd>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyNestedListLocalFix::mterm &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyNestedListLocalFix::mterm::MLit>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyNestedListLocalFix::mterm::MAdd>(t.v());
        const LoopifyNestedListLocalFix::mterm &a0_value = *a0;
        const List<LoopifyNestedListLocalFix::mterm> &a1_value = *a1;
        _stack.emplace_back(_after_size_in_MAdd{a1});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_after_size_in_MAdd>(_popped));
      _stack.pop_back();
      std::shared_ptr<List<LoopifyNestedListLocalFix::mterm>> a1 =
          std::move(_f.a1);
      const List<LoopifyNestedListLocalFix::mterm> &a1_value = *a1;
      _result = ((_result + a1_value.template fold_right<uint64_t>(
                                [](const LoopifyNestedListLocalFix::mterm &x,
                                   uint64_t acc) { return (size(x) + acc); },
                                UINT64_C(0))) +
                 1);
    }
  }
  return _result;
}
