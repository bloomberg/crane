#include "loopify_list_generation.h"

List<uint64_t> LoopifyListGeneration::replicate(uint64_t n, uint64_t x) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(x, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::stutter(const List<uint64_t> &l) {
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
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(
                    std::get<typename List<uint64_t>::Cons>(_node.v_mut())
                        .l->v_mut())
                    .l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::cycle(
    uint64_t n,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: resumes after recursive call, then processes rest.
  struct CraneCont_n_ {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified cycle: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::iterate(uint64_t n, uint64_t x) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_x = x;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_x, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_x = (_loop_x + UINT64_C(1));
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::replicate_list(
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// CraneCont_n: saves [rep], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n {
    List<uint64_t> rep;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified replicate_list: CraneEnter -> CraneCont_n.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const auto &[n, x] = a0;
        List<uint64_t> rep = replicate(n, x);
        _stack.emplace_back(CraneCont_n{std::move(rep)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n>(_frame));
      List<uint64_t> rep = std::move(_f.rep);
      _result = std::move(rep).app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::repeat_with_sep(uint64_t sep, uint64_t n,
                                                      uint64_t x) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (n_ <= 0) {
        auto _value = List<uint64_t>::cons(x, List<uint64_t>::nil());
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
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
        _write = &std::get<typename List<uint64_t>::Cons>(
                      std::get<typename List<uint64_t>::Cons>(_node.v_mut())
                          .l->v_mut())
                      .l;
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGeneration::range(uint64_t start, uint64_t len) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len_ = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len_;
      _loop_start = (_loop_start + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_root);
}
