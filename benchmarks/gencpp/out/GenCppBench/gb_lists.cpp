#include "gb_lists.h"

uint64_t GbLists::next(uint64_t s) {
  auto &&_once1 = ((s * UINT64_C(75)) + UINT64_C(74));
  auto &&_once2 = UINT64_C(65537);
  return (_once2 ? _once1 % _once2 : _once1);
}

List<uint64_t> GbLists::randoms(uint64_t n, uint64_t s) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_s, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = next(_loop_s);
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> GbLists::merge(List<uint64_t> l1, const List<uint64_t> &x0_) {
  // Explicit stack replaces the non-tail recursion of merge: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *x0_;
    List<uint64_t> l1;
  };

  struct _call_merge_aux {
    const List<uint64_t> *l2;
    List<uint64_t> l1;
  };

  struct _after_merge_aux_in_false {
    uint64_t a00;
  };

  struct _after_merge_in_true {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _call_merge_aux, _after_merge_aux_in_false,
                              _after_merge_in_true>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x0_, std::move(l1)});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &x0_ = *_f.x0_;
      List<uint64_t> l1 = std::move(_f.l1);
      _stack.emplace_back(_call_merge_aux{&x0_, std::move(l1)});
    } else if (std::holds_alternative<_call_merge_aux>(_popped)) {
      auto _f = std::move(std::get<_call_merge_aux>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l2 = *_f.l2;
      List<uint64_t> l1 = std::move(_f.l1);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v_mut())) {
        _result = std::move(l2);
      } else {
        auto &[a0, a2] = std::get<typename List<uint64_t>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = std::move(l1);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          if (a0 <= a00) {
            _stack.emplace_back(_after_merge_in_true{a0});
            _stack.emplace_back(_call{&l2, *a2});
          } else {
            _stack.emplace_back(_after_merge_aux_in_false{a00});
            _stack.emplace_back(_call_merge_aux{crane_raw(a10), std::move(l1)});
          }
        }
      }
    } else if (std::holds_alternative<_after_merge_aux_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_merge_aux_in_false>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = List<uint64_t>::cons(a00, std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_merge_in_true>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = List<uint64_t>::cons(a0, std::move(_result));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>>
GbLists::split(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of split: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_split_in_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _frame = std::variant<_call, _after_split_in_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(l, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          _result = std::make_pair(l, List<uint64_t>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          _stack.emplace_back(_after_split_in_Cons{a0, a00});
          _stack.emplace_back(_call{crane_raw(a10)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_split_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      auto [x, y] = std::move(_result);
      _result = std::make_pair(List<uint64_t>::cons(a0, std::move(x)),
                               List<uint64_t>::cons(a00, std::move(y)));
    }
  }
  return _result;
}

List<uint64_t> GbLists::msort(uint64_t fuel, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of msort: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> l;
    uint64_t fuel;
  };

  struct _after_msort_in_pair {
    uint64_t f;
    List<uint64_t> y;
  };

  struct _after_msort_in_pair_2 {
    List<uint64_t> _tmp2;
  };

  using _frame =
      std::variant<_call, _after_msort_in_pair, _after_msort_in_pair_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = std::move(l);
        } else {
          const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(l);
          } else {
            auto [x, y] = split(l);
            _stack.emplace_back(_after_msort_in_pair{f, std::move(y)});
            _stack.emplace_back(_call{std::move(x), f});
          }
        }
      }
    } else if (std::holds_alternative<_after_msort_in_pair>(_popped)) {
      auto _f = std::move(std::get<_after_msort_in_pair>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      List<uint64_t> y = std::move(_f.y);
      _stack.emplace_back(_after_msort_in_pair_2{std::move(_result)});
      _stack.emplace_back(_call{std::move(y), f});
    } else {
      auto _f = std::move(std::get<_after_msort_in_pair_2>(_popped));
      _stack.pop_back();
      _result = merge(std::move(_f._tmp2), std::move(_result));
    }
  }
  return _result;
}

uint64_t GbLists::checksum(const List<uint64_t> &l, uint64_t acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_acc = acc;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_once1 = ((_loop_acc * UINT64_C(31)) + a0);
      auto &&_once2 = UINT64_C(65535);
      _loop_acc = (_once2 ? _once1 % _once2 : _once1);
      _loop_l = crane_raw(a1);
    }
  }
}

uint64_t GbLists::lists(uint64_t n, uint64_t rounds) {
  return ListDef::seq(UINT64_C(0), rounds).template fold_left<uint64_t>(
      [=](uint64_t acc, uint64_t i) {
        List<uint64_t> l =
            randoms(n, (i + UINT64_C(1))).template map<uint64_t>(
                                [=](uint64_t x) {
                                  auto &&_once1 = UINT64_C(4096);
                                  return ((_once1 ? x % _once1 : x) + i);
                                });
        List<uint64_t> l0 = l.filter([](uint64_t x) {
          return !((UINT64_C(3) ? x % UINT64_C(3) : x) == UINT64_C(0));
        });
        List<uint64_t> s = msort(UINT64_C(64), l0.app(l0.rev()));
        return (checksum(std::move(s), acc) +
                l0.template fold_right<uint64_t>(
                    [](uint64_t _x0,
                       uint64_t _x1)
                         -> uint64_t { return (_x0 + _x1); },
                    UINT64_C(0)));
      },
      UINT64_C(0));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
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
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
