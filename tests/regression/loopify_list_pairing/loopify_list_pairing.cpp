#include <loopify_list_pairing.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::unzip(
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> l =
          _f.l;
      if (std::holds_alternative<
              typename List<std::pair<unsigned int, unsigned int>>::Nil>(
              l->v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] = std::get<
            typename List<std::pair<unsigned int, unsigned int>>::Cons>(l->v());
        const unsigned int &a = d_a0.first;
        const unsigned int &b = d_a0.second;
        _stack.emplace_back(_Call1{b, a});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int b = _f._s0;
      unsigned int a = _f._s1;
      const std::shared_ptr<List<unsigned int>> &xs = _result.first;
      const std::shared_ptr<List<unsigned int>> &ys = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(a, xs),
                               List<unsigned int>::cons(b, ys));
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::swizzle(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
      const std::shared_ptr<List<unsigned int>> &odds = _result.first;
      const std::shared_ptr<List<unsigned int>> &evens = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(d_a0, evens), odds);
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::partition(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
      const std::shared_ptr<List<unsigned int>> &yes = _result.first;
      const std::shared_ptr<List<unsigned int>> &no = _result.second;
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_pair(List<unsigned int>::cons(d_a0, yes), no);
      } else {
        _result = std::make_pair(yes, List<unsigned int>::cons(d_a0, no));
      }
    }
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListPairing::zip_longest_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2,
    const unsigned int default0) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        _head = List<std::pair<unsigned int, unsigned int>>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1->v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
          } else {
            _head = List<std::pair<unsigned int, unsigned int>>::nil();
          }
          _continue = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
          auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(default0, d_a00), nullptr);
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
          std::shared_ptr<List<unsigned int>> _next_l1 =
              List<unsigned int>::nil();
          unsigned int _next_fuel = fuel_;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(d_a0, default0), nullptr);
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l2 =
              List<unsigned int>::nil();
          std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
          unsigned int _next_fuel = fuel_;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
          auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(d_a0, d_a00), nullptr);
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
          std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
          unsigned int _next_fuel = fuel_;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListPairing::zip_longest(const std::shared_ptr<List<unsigned int>> &l1,
                                const std::shared_ptr<List<unsigned int>> &l2,
                                const unsigned int default0) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  unsigned int maxlen;
  if (len1 < len2) {
    maxlen = len2;
  } else {
    maxlen = len1;
  }
  return zip_longest_fuel(maxlen, l1, l2, default0);
}

std::shared_ptr<List<unsigned int>>
LoopifyListPairing::zipWith(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        auto _cell = List<unsigned int>::cons((d_a0 + d_a00), nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
        std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::split_even_odd(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
      const std::shared_ptr<List<unsigned int>> &evens = _result.first;
      const std::shared_ptr<List<unsigned int>> &odds = _result.second;
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_pair(List<unsigned int>::cons(d_a0, evens), odds);
      } else {
        _result = std::make_pair(evens, List<unsigned int>::cons(d_a0, odds));
      }
    }
  }
  return _result;
}
