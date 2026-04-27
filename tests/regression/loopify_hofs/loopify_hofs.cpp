#include <loopify_hofs.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool
LoopifyHofs::is_prefix_of(const List<unsigned int> &l1,
                          const List<unsigned int> &l2) {
  bool _result;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
        if (d_a0 == d_a00) {
          List<unsigned int> _next_l2 = *(d_a10);
          List<unsigned int> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
        } else {
          _result = false;
          break;
        }
      }
    }
  }
  return _result;
}

/// lookup_all key l finds all values associated with key in association list.
__attribute__((pure)) List<unsigned int>
LoopifyHofs::lookup_all(const unsigned int &key,
                        const List<std::pair<unsigned int, unsigned int>> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<std::pair<unsigned int, unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l.v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(v, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      } else {
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// Helper: get head of list with default.
__attribute__((pure)) unsigned int
LoopifyHofs::head_default(unsigned int default0, const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return d_a0;
  }
}

/// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
__attribute__((pure)) List<List<unsigned int>>
LoopifyHofs::subsequences(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        List<unsigned int> d_a1_value = *(d_a1);
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1_value});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      List<List<unsigned int>> rest = _result;
      std::function<List<List<unsigned int>>(List<List<unsigned int>>)>
          map_cons_x;
      map_cons_x =
          [&](List<List<unsigned int>> lsts) -> List<List<unsigned int>> {
        struct _Enter {
          List<List<unsigned int>> lsts;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<List<unsigned int> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        List<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{lsts});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<List<unsigned int>> lsts = _f.lsts;
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    lsts.v())) {
              _result = List<List<unsigned int>>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<List<unsigned int>>::Cons>(lsts.v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Call1>(_frame));
            _result = List<List<unsigned int>>::cons(_f._s0, _result);
          }
        }
        return _result;
      };
      _result = rest.app(map_cons_x(rest));
    }
  }
  return _result;
}

/// Helper: pair element with all elements in list.
__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyHofs::pair_with_all(unsigned int x, const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto _cell =
          std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
              typename List<std::pair<unsigned int, unsigned int>>::Cons(
                  std::make_pair(x, d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
               (*_write)->v_mut())
               .d_a1;
      _loop_l = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

/// cartesian l1 l2 computes cartesian product of two lists.
__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyHofs::cartesian(const List<unsigned int> &l1,
                       const List<unsigned int> &l2) {
  struct _Enter {
    const List<unsigned int> l1;
  };

  struct _Call1 {
    decltype(pair_with_all(std::declval<unsigned int &>(),
                           std::declval<const List<unsigned int> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<std::pair<unsigned int, unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l1 = _f.l1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        _result = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        _stack.emplace_back(_Call1{pair_with_all(d_a0, l2)});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// longest_run l finds the longest consecutive run of equal elements.
/// Matches on recursive result to decide behavior.
__attribute__((pure)) List<unsigned int>
LoopifyHofs::longest_run_fuel(const unsigned int &fuel, List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<unsigned int>>(_loop_l);
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          *(_write) = std::make_unique<List<unsigned int>>(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (d_a0 == d_a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l =
                List<unsigned int>::cons(d_a00, *(d_a10));
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            List<unsigned int> rec_result =
                longest_run_fuel(f, List<unsigned int>::cons(d_a00, *(d_a10)));
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    rec_result.v())) {
              *(_write) = std::make_unique<List<unsigned int>>(
                  List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
              break;
            } else {
              const auto &[d_a01, d_a11] =
                  std::get<typename List<unsigned int>::Cons>(rec_result.v());
              if (d_a0 == d_a01) {
                *(_write) = std::make_unique<List<unsigned int>>(rec_result);
                break;
              } else {
                *(_write) = std::make_unique<List<unsigned int>>(rec_result);
                break;
              }
            }
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyHofs::longest_run(const List<unsigned int> &l) {
  return longest_run_fuel(l.length(), l);
}

/// power_set l generates all subsets.
__attribute__((pure)) List<List<unsigned int>>
LoopifyHofs::power_set(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        List<unsigned int> d_a1_value = *(d_a1);
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1_value});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      List<List<unsigned int>> sub = _result;
      std::function<List<List<unsigned int>>(List<List<unsigned int>>)>
          map_cons_x;
      map_cons_x =
          [&](List<List<unsigned int>> lsts) -> List<List<unsigned int>> {
        struct _Enter {
          List<List<unsigned int>> lsts;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<List<unsigned int> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        List<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{lsts});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<List<unsigned int>> lsts = _f.lsts;
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    lsts.v())) {
              _result = List<List<unsigned int>>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<List<unsigned int>>::Cons>(lsts.v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Call1>(_frame));
            _result = List<List<unsigned int>>::cons(_f._s0, _result);
          }
        }
        return _result;
      };
      _result = sub.app(map_cons_x(sub));
    }
  }
  return _result;
}
