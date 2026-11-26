#include "loopify_list_generation.h"

List<uint64_t> LoopifyListGeneration::replicate(uint64_t n, uint64_t x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = n - 1;
      auto _cell = typename List<uint64_t>::Cons(x, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::stutter(const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell1 = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      auto _cell = typename List<uint64_t>::Cons(a0, std::move(_cell1));
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename List<uint64_t>::Cons>(
              std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l->v_mut())
              .l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::cycle(uint64_t n,
                                            const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of cycle: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_cycle_in_S {};

  using _frame = std::variant<_call, _after_cycle_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_cycle_in_S{});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_cycle_in_S>(_popped));
      _stack.pop_back();
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::iterate(uint64_t n, uint64_t x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = n - 1;
      auto _cell = typename List<uint64_t>::Cons(x, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      x = (x + UINT64_C(1));
      n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::replicate_list(
    const List<std::pair<uint64_t, uint64_t>> &l) {
  // Explicit stack replaces the non-tail recursion of replicate_list: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  struct _after_replicate_list_in_pair {
    List<uint64_t> rep;
  };

  using _frame = std::variant<_call, _after_replicate_list_in_pair>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const auto &[n, x] = a0;
        List<uint64_t> rep = replicate(n, x);
        _stack.emplace_back(_after_replicate_list_in_pair{std::move(rep)});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_replicate_list_in_pair>(_popped));
      _stack.pop_back();
      List<uint64_t> rep = std::move(_f.rep);
      _result = rep.app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::repeat_with_sep(uint64_t sep, uint64_t n,
                                                      uint64_t x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = n - 1;
      if (n_ <= 0) {
        auto _value = List<uint64_t>::cons(x, List<uint64_t>::nil());
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t _x = n_ - 1;
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        auto _cell = typename List<uint64_t>::Cons(x, std::move(_cell1));
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<uint64_t>::Cons>(std::get<
                typename List<uint64_t>::Cons>(_node.v_mut()).l->v_mut())
                .l;
        n = n_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::range(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len_ = len - 1;
      auto _cell = typename List<uint64_t>::Cons(start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      len = len_;
      start = (start + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_root);
}
