#include "loopify_algorithms.h"

/// Consolidated UNIQUE list/sequence algorithms.
uint64_t LoopifyAlgorithms::len_impl(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of len_impl: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_len_impl_in_Cons {};

  using _frame = std::variant<_call, _after_len_impl_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_len_impl_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_len_impl_in_Cons>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

/// sieve l Sieve of Eratosthenes - filters out multiples.
List<uint64_t> LoopifyAlgorithms::sieve_fuel(uint64_t fuel,
                                             const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l = l;
  while (true) {
    if (fuel <= 0) {
      auto _value = _loop_l;
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto filter_multiples =
            [&](const List<uint64_t> &rest) -> List<uint64_t> {
              // Explicit stack replaces the non-tail recursion of
              // filter_multiples: _call frames are pending calls, _after frames
              // resume a caller.
              struct _call {
                const List<uint64_t> *rest;
              };

              struct _after_filter_multiples_in_false {
                uint64_t a00;
              };

              using _frame =
                  std::variant<_call, _after_filter_multiples_in_false>;
              List<uint64_t> _result{};
              crane::small_vector<_frame> _stack;
              _stack.emplace_back(_call{&rest});
              while (!_stack.empty()) {
                _frame &_popped = _stack.back();
                if (std::holds_alternative<_call>(_popped)) {
                  auto _f = std::move(std::get<_call>(_popped));
                  _stack.pop_back();
                  const List<uint64_t> &rest = *_f.rest;
                  if (std::holds_alternative<typename List<uint64_t>::Nil>(
                          rest.v())) {
                    _result = List<uint64_t>::nil();
                  } else {
                    const auto &[a00, a10] =
                        std::get<typename List<uint64_t>::Cons>(rest.v());
                    if ((a0 ? a00 % a0 : a00) == UINT64_C(0)) {
                      _stack.emplace_back(_call{crane_raw(a10)});
                    } else {
                      _stack.emplace_back(_after_filter_multiples_in_false{a00});
                      _stack.emplace_back(_call{crane_raw(a10)});
                    }
                  }
                } else {
                  auto _f = std::move(
                      std::get<_after_filter_multiples_in_false>(_popped));
                  _stack.pop_back();
                  uint64_t a00 = _f.a00;
                  _result = List<uint64_t>::cons(a00, std::move(_result));
                }
              }
              return _result;
            };
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = filter_multiples(*a1);
        fuel = f;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyAlgorithms::sieve(const List<uint64_t> &l) {
  return sieve_fuel(len_impl(l), l);
}

/// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
/// (1,2),(2,1),(3,3).
List<std::pair<uint64_t, uint64_t>>
LoopifyAlgorithms::run_length_encode(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of run_length_encode: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_run_length_encode_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_run_length_encode_in_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_run_length_encode_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_run_length_encode_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<std::pair<uint64_t, uint64_t>> _tmp1 = std::move(_result);
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(_tmp1.v_mut())) {
        _result = List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(a0, UINT64_C(1)),
            List<std::pair<uint64_t, uint64_t>>::nil());
      } else {
        auto &[a00, a10] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                _tmp1.v_mut());
        auto [y, n] = std::move(a00);
        if (a0 == y) {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(y, (n + 1)), crane::shared_child(a10));
        } else {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::cons(
                  std::make_pair(y, n), crane::shared_child(a10)));
        }
      }
    }
  }
  return _result;
}

/// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
List<uint64_t> LoopifyAlgorithms::prefix_sums(uint64_t acc,
                                              const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = typename List<uint64_t>::Cons(acc, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      acc = acc + a0;
      continue;
    }
  }
  return std::move(*_root);
}

/// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
List<uint64_t> LoopifyAlgorithms::differences(const List<uint64_t> &l) {
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
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, _] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = typename List<uint64_t>::Cons(
            (a00 - a0 > a00 ? 0 : a00 - a0), nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// rotate_left n l rotates list left by n positions.
List<uint64_t> LoopifyAlgorithms::rotate_left_fuel(uint64_t fuel, uint64_t n,
                                                   const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_l = l;
  while (true) {
    if (fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t f = fuel - 1;
      if (n <= UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          return List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v());
          _loop_l = a1->app(List<uint64_t>::cons(a0, List<uint64_t>::nil()));
          n = (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1));
          fuel = f;
        }
      }
    }
  }
}

List<uint64_t> LoopifyAlgorithms::rotate_left(uint64_t n,
                                              const List<uint64_t> &l) {
  return rotate_left_fuel(n, n, l);
}

/// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
List<uint64_t> LoopifyAlgorithms::nub_aux(const List<uint64_t> &l,
                                          uint64_t fuel) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l = l;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto filter_out = [&](const List<uint64_t> &rest) -> List<uint64_t> {
          // Explicit stack replaces the non-tail recursion of filter_out: _call
          // frames are pending calls, _after frames resume a caller.
          struct _call {
            const List<uint64_t> *rest;
          };

          struct _after_filter_out_in_false {
            uint64_t a00;
          };

          using _frame = std::variant<_call, _after_filter_out_in_false>;
          List<uint64_t> _result{};
          crane::small_vector<_frame> _stack;
          _stack.emplace_back(_call{&rest});
          while (!_stack.empty()) {
            _frame &_popped = _stack.back();
            if (std::holds_alternative<_call>(_popped)) {
              auto _f = std::move(std::get<_call>(_popped));
              _stack.pop_back();
              const List<uint64_t> &rest = *_f.rest;
              if (std::holds_alternative<typename List<uint64_t>::Nil>(rest.v())) {
                _result = List<uint64_t>::nil();
              } else {
                const auto &[a00, a10] =
                    std::get<typename List<uint64_t>::Cons>(rest.v());
                if (a0 == a00) {
                  _stack.emplace_back(_call{crane_raw(a10)});
                } else {
                  _stack.emplace_back(_after_filter_out_in_false{a00});
                  _stack.emplace_back(_call{crane_raw(a10)});
                }
              }
            } else {
              auto _f =
                  std::move(std::get<_after_filter_out_in_false>(_popped));
              _stack.pop_back();
              uint64_t a00 = _f.a00;
              _result = List<uint64_t>::cons(a00, std::move(_result));
            }
          }
          return _result;
        };
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        fuel = f;
        _loop_l = filter_out(*a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyAlgorithms::nub(const List<uint64_t> &l) {
  return nub_aux(l, len_impl(l));
}

/// Internal helpers for palindrome check.
List<uint64_t> LoopifyAlgorithms::rev_impl(List<uint64_t> acc,
                                           const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  List<uint64_t> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      _loop_l = crane_raw(a1);
      _loop_acc = List<uint64_t>::cons(a0, std::move(_loop_acc));
    }
  }
}

bool LoopifyAlgorithms::list_eq_impl(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return true;
      } else {
        return false;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        if (a0 == a00) {
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
        } else {
          return false;
        }
      }
    }
  }
}

/// is_palindrome l checks if list reads same forwards and backwards.
bool LoopifyAlgorithms::is_palindrome(const List<uint64_t> &l) {
  return list_eq_impl(l, rev_impl(List<uint64_t>::nil(), l));
}

/// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
/// [1,2],[2,3],[3,4].
List<uint64_t> LoopifyAlgorithms::take_impl(uint64_t k,
                                            const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (k <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = k - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        k = m;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>>
LoopifyAlgorithms::windows_aux(uint64_t n, const List<uint64_t> &l,
                               uint64_t fuel) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[_, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (len_impl(*_loop_l) < n) {
          auto _value = List<List<uint64_t>>::nil();
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell = typename List<List<uint64_t>>::Cons(
              take_impl(n, *_loop_l), nullptr);
          List<List<uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
          fuel = f;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyAlgorithms::windows(uint64_t n,
                                                const List<uint64_t> &l) {
  return windows_aux(n, l, (len_impl(l) + 1));
}

/// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
List<std::pair<uint64_t, uint64_t>>
LoopifyAlgorithms::sliding_pairs(const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                          std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, _] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
            std::make_pair(a0, a00), nullptr);
        List<std::pair<uint64_t, uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<
                            List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
uint64_t LoopifyAlgorithms::max_prefix_sum(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of max_prefix_sum: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_max_prefix_sum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_max_prefix_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_max_prefix_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_max_prefix_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t rest = _result;
      uint64_t sum = a0 + rest;
      if (rest == UINT64_C(0)) {
        _result = UINT64_C(0);
      } else if (rest < sum) {
        _result = sum;
      } else {
        _result = rest;
      }
    }
  }
  return _result;
}

/// weighted_sum i l computes weighted sum with increasing index.
uint64_t LoopifyAlgorithms::weighted_sum(uint64_t i, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of weighted_sum: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    uint64_t i;
  };

  struct _after_weighted_sum_in_Cons {
    uint64_t i;
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_weighted_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, i});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      uint64_t i = _f.i;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_weighted_sum_in_Cons{i, a0});
        _stack.emplace_back(_call{crane_raw(a1), (i + 1)});
      }
    } else {
      auto _f = std::move(std::get<_after_weighted_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t i = _f.i;
      uint64_t a0 = _f.a0;
      _result = i * a0 + _result;
    }
  }
  return _result;
}

/// step_sum l sums with conditional doubling for odd numbers.
uint64_t LoopifyAlgorithms::step_sum(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of step_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_step_sum_in_Cons {
    uint64_t contribution;
  };

  using _frame = std::variant<_call, _after_step_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        uint64_t contribution;
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          contribution = a0;
        } else {
          contribution = a0 * UINT64_C(2);
        }
        _stack.emplace_back(_after_step_sum_in_Cons{contribution});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_step_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t contribution = _f.contribution;
      _result = contribution + _result;
    }
  }
  return _result;
}

/// Helper: get head with default value.
uint64_t LoopifyAlgorithms::head_nat(uint64_t d, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return d;
  } else {
    const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// suffix_sums l computes suffix sums (reverse of prefix sums).
List<uint64_t> LoopifyAlgorithms::suffix_sums(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of suffix_sums: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_suffix_sums_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_suffix_sums_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_suffix_sums_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_suffix_sums_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(a0 + head_nat(UINT64_C(0), rest), rest);
    }
  }
  return _result;
}
