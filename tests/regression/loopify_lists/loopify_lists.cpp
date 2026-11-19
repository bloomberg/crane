#include "loopify_lists.h"

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
LoopifyLists::list<uint64_t> LoopifyLists::range(uint64_t start,
                                                 uint64_t count0) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  uint64_t _loop_count0 = count0;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_count0 <= 0) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t c = _loop_count0 - 1;
      auto _cell =
          typename LoopifyLists::list<uint64_t>::Cons(_loop_start, nullptr);
      LoopifyLists::list<uint64_t> &_node =
          (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyLists::list<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_count0 = c;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}

/// step_sum l sums with conditional contributions: even values as-is, odd
/// doubled.
uint64_t LoopifyLists::step_sum(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of step_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
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
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        uint64_t contribution;
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          contribution = a0;
        } else {
          contribution = (a0 * UINT64_C(2));
        }
        _stack.emplace_back(_after_step_sum_in_Cons{contribution});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_step_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t contribution = _f.contribution;
      _result = (contribution + std::move(_result));
    }
  }
  return _result;
}

/// sum_abs l sums absolute values (using monus for nat).
uint64_t LoopifyLists::sum_abs(const LoopifyLists::list<uint64_t> &l,
                               uint64_t base) {
  // Explicit stack replaces the non-tail recursion of sum_abs: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_sum_abs_in_Cons {
    uint64_t abs_val;
  };

  using _frame = std::variant<_call, _after_sum_abs_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        uint64_t abs_val;
        if (base <= a0) {
          abs_val = (((a0 - base) > a0 ? 0 : (a0 - base)));
        } else {
          abs_val = (((base - a0) > base ? 0 : (base - a0)));
        }
        _stack.emplace_back(_after_sum_abs_in_Cons{abs_val});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_abs_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t abs_val = _f.abs_val;
      _result = (abs_val + std::move(_result));
    }
  }
  return _result;
}

/// four_elem l multi-case pattern matching on list structure.
uint64_t LoopifyLists::four_elem(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of four_elem: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_four_elem_in_Cons {
    uint64_t a0;
    uint64_t a00;
    uint64_t a01;
    uint64_t a02;
  };

  using _frame = std::variant<_call, _after_four_elem_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = UINT64_C(1);
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          auto &&_sv1 = *a10;
          if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                  _sv1.v())) {
            _result = UINT64_C(2);
          } else {
            const auto &[a01, a11] =
                std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv1.v());
            auto &&_sv2 = *a11;
            if (std::holds_alternative<
                    typename LoopifyLists::list<uint64_t>::Nil>(_sv2.v())) {
              _result = UINT64_C(3);
            } else {
              const auto &[a02, a12] =
                  std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_after_four_elem_in_Cons{a0, a00, a01, a02});
              _stack.emplace_back(_call{crane_raw(a12)});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_after_four_elem_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      uint64_t a01 = _f.a01;
      uint64_t a02 = _f.a02;
      _result = ((a0 + a00) + ((a01 + a02) + std::move(_result)));
    }
  }
  return _result;
}

/// between lo hi l filters elements in range lo, hi.
LoopifyLists::list<uint64_t>
LoopifyLists::between(uint64_t lo, uint64_t hi,
                      const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if ((lo <= a0 && a0 <= hi)) {
        auto _cell = typename LoopifyLists::list<uint64_t>::Cons(a0, nullptr);
        LoopifyLists::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
uint64_t LoopifyLists::categorize(uint64_t k,
                                  const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of categorize: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_categorize_in_Cons {
    uint64_t score;
  };

  using _frame = std::variant<_call, _after_categorize_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        uint64_t score;
        if (k < a0) {
          score = UINT64_C(3);
        } else {
          if (a0 == k) {
            score = UINT64_C(2);
          } else {
            score = UINT64_C(1);
          }
        }
        _stack.emplace_back(_after_categorize_in_Cons{score});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_categorize_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t score = _f.score;
      _result = (score + std::move(_result));
    }
  }
  return _result;
}

/// max_prefix_sum l maximum prefix sum (Kadane-like).
uint64_t LoopifyLists::max_prefix_sum(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of max_prefix_sum: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
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
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_max_prefix_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_max_prefix_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t rest = std::move(_result);
      uint64_t sum = (a0 + rest);
      if (UINT64_C(0) <= sum) {
        _result = std::move(sum);
      } else {
        _result = UINT64_C(0);
      }
    }
  }
  return _result;
}

/// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
LoopifyLists::list<uint64_t>
LoopifyLists::pairwise_sum(const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        auto _value = list<uint64_t>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        auto _cell =
            typename LoopifyLists::list<uint64_t>::Cons((a0 + a00), nullptr);
        LoopifyLists::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a10);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// weighted_sum i l weighted sum with increasing weights.
uint64_t LoopifyLists::weighted_sum(uint64_t i,
                                    const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of weighted_sum: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
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
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t i = _f.i;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_weighted_sum_in_Cons{i, a0});
        _stack.emplace_back(_call{crane_raw(a1), (i + 1)});
      }
    } else {
      auto _f = std::move(std::get<_after_weighted_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t i = _f.i;
      uint64_t a0 = _f.a0;
      _result = ((i * a0) + std::move(_result));
    }
  }
  return _result;
}

/// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
LoopifyLists::list<uint64_t>
LoopifyLists::prefix_sums(uint64_t acc, const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::cons(_loop_acc, list<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto _cell =
          typename LoopifyLists::list<uint64_t>::Cons(_loop_acc, nullptr);
      LoopifyLists::list<uint64_t> &_node =
          (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyLists::list<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_root);
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
LoopifyLists::list<uint64_t>
LoopifyLists::uniq_sorted(const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        auto _value = list<uint64_t>::cons(a0, list<uint64_t>::nil());
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, _] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = typename LoopifyLists::list<uint64_t>::Cons(a0, nullptr);
          LoopifyLists::list<uint64_t> &_node =
              (_write ? *(*_write =
                              std::make_shared<LoopifyLists::list<uint64_t>>(
                                  std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

/// Helper: take first n elements.
LoopifyLists::list<uint64_t>
LoopifyLists::take_n(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l->v())) {
        auto _value = list<uint64_t>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
        auto _cell = typename LoopifyLists::list<uint64_t>::Cons(a0, nullptr);
        LoopifyLists::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a1);
        _loop_n = m;
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// Helper: list length.
uint64_t LoopifyLists::len_list(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of len_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_len_list_in_Cons {};

  using _frame = std::variant<_call, _after_len_list_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_len_list_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_len_list_in_Cons>(_popped));
      _stack.pop_back();
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

/// windows n l returns all sliding windows of size n.
LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::windows_aux(uint64_t fuel, uint64_t n,
                          const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<LoopifyLists::list<uint64_t>>> _root{};
  std::shared_ptr<LoopifyLists::list<LoopifyLists::list<uint64_t>>> *_write =
      nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = list<LoopifyLists::list<uint64_t>>::nil();
      (_write ? *(*_write = std::make_shared<
                      LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l->v())) {
        auto _value = list<LoopifyLists::list<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<
                        LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[_, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
        if (len_list(*_loop_l) < n) {
          auto _value = list<LoopifyLists::list<uint64_t>>::nil();
          (_write ? *(*_write = std::make_shared<
                          LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          LoopifyLists::list<uint64_t> window = take_n(n, *_loop_l);
          if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                  window.v())) {
            auto _value = list<LoopifyLists::list<uint64_t>>::nil();
            (_write ? *(*_write = std::make_shared<
                            LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                            std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            auto _cell =
                typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons(
                    window, nullptr);
            LoopifyLists::list<LoopifyLists::list<uint64_t>> &_node =
                (
                    _write ? *(*_write = std::make_shared<LoopifyLists::list<
                                   LoopifyLists::list<uint64_t>>>(
                                   std::move(_cell)))
                           : _root.emplace(std::move(_cell)));
            _write =
                &std::get<typename LoopifyLists::list<
                    LoopifyLists::list<uint64_t>>::Cons>(_node.v_mut()).l;
            _loop_l = crane_raw(a1);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::windows(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifyLists::is_prefix_of(const LoopifyLists::list<uint64_t> &l1,
                                const LoopifyLists::list<uint64_t> &l2) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l2 = &l2;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] = std::get<
            typename LoopifyLists::list<uint64_t>::Cons>(_loop_l2->v());
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

/// lookup_all key l finds all values for key in association list.
LoopifyLists::list<uint64_t> LoopifyLists::lookup_all(
    uint64_t key, const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        auto _cell = typename LoopifyLists::list<uint64_t>::Cons(v, nullptr);
        LoopifyLists::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// member x l checks if x is in the list.
bool LoopifyLists::member(uint64_t x, const LoopifyLists::list<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return true;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

/// product l multiplies all elements in the list.
uint64_t LoopifyLists::product(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of product: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_product_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_product_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_product_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_product_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 * std::move(_result));
    }
  }
  return _result;
}

/// sum_list l sums all elements in the list.
uint64_t LoopifyLists::sum_list(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_sum_list_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_list_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// flatten_nested l alternative flatten with different pattern: flattens one
/// level at a time.
/// Pattern: :: rest -> flatten rest, (x :: xs) :: rest -> x :: flatten (xs ::
/// rest).
LoopifyLists::list<uint64_t> LoopifyLists::flatten_nested_fuel(
    uint64_t fuel, const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  LoopifyLists::list<LoopifyLists::list<uint64_t>> _loop_l = l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              _loop_l.v())) {
        auto _value = list<uint64_t>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            _loop_l.v());
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                a0.v())) {
          _loop_l = LoopifyLists::list<LoopifyLists::list<uint64_t>>(*a1);
          _loop_fuel = f;
          continue;
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(a0.v());
          auto _cell =
              typename LoopifyLists::list<uint64_t>::Cons(a00, nullptr);
          LoopifyLists::list<uint64_t> &_node =
              (_write ? *(*_write =
                              std::make_shared<LoopifyLists::list<uint64_t>>(
                                  std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l = list<LoopifyLists::list<uint64_t>>::cons(
              *a10, crane::shared_child(a1));
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyLists::sum_list_lengths(
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list_lengths: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> *l;
  };

  struct _after_sum_list_lengths_in_Cons {
    LoopifyLists::list<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_sum_list_lengths_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            l.v());
        _stack.emplace_back(_after_sum_list_lengths_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_lengths_in_Cons>(_popped));
      _stack.pop_back();
      LoopifyLists::list<uint64_t> a0 = std::move(_f.a0);
      _result = (len_list(std::move(a0)) + std::move(_result));
    }
  }
  return _result;
}

LoopifyLists::list<uint64_t> LoopifyLists::flatten_nested(
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
LoopifyLists::list<uint64_t>
LoopifyLists::compress(const LoopifyLists::list<uint64_t> &l) {
  return uniq_sorted(l);
}

/// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
/// (1,2),(3,4).
LoopifyLists::list<std::pair<uint64_t, uint64_t>>
LoopifyLists::group_pairs(const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<LoopifyLists::list<std::pair<uint64_t, uint64_t>>> *_write =
      nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write = std::make_shared<
                      LoopifyLists::list<std::pair<uint64_t, uint64_t>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        auto _value = list<std::pair<uint64_t, uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<
                        LoopifyLists::list<std::pair<uint64_t, uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        auto _cell =
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons(
                std::make_pair(a0, a00), nullptr);
        LoopifyLists::list<std::pair<uint64_t, uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<
                            LoopifyLists::list<std::pair<uint64_t, uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<std::pair<uint64_t,
                                                            uint64_t>>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a10);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::swizzle(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of swizzle: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_swizzle_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_swizzle_in_Cons>;
  std::pair<LoopifyLists::list<uint64_t>,
            LoopifyLists::list<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_swizzle_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_swizzle_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto [odds, evens] = std::move(_result);
      _result = std::make_pair(list<uint64_t>::cons(a0, std::move(evens)),
                               std::move(odds));
    }
  }
  return _result;
}

/// index_of_aux x l i finds first index of x in l starting from i.
uint64_t
LoopifyLists::index_of_aux(uint64_t x, const LoopifyLists::list<uint64_t> &l,
                           uint64_t i) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_i = i;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return _loop_i;
      } else {
        _loop_i = (_loop_i + 1);
        _loop_l = crane_raw(a1);
      }
    }
  }
}

uint64_t LoopifyLists::index_of(uint64_t x,
                                const LoopifyLists::list<uint64_t> &l) {
  return index_of_aux(x, l, UINT64_C(0));
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
LoopifyLists::list<uint64_t>
LoopifyLists::interleave(const LoopifyLists::list<uint64_t> &l1,
                         const LoopifyLists::list<uint64_t> &l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l2 = &l2;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      auto _value = *_loop_l2;
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2->v())) {
        auto _value = *_loop_l1;
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] = std::get<
            typename LoopifyLists::list<uint64_t>::Cons>(_loop_l2->v());
        auto _cell1 = std::make_shared<LoopifyLists::list<uint64_t>>(
            typename LoopifyLists::list<uint64_t>::Cons(a00, nullptr));
        auto _cell =
            typename LoopifyLists::list<uint64_t>::Cons(a0, std::move(_cell1));
        LoopifyLists::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                    _node.v_mut())
                    .l->v_mut())
                .l;
        _loop_l2 = crane_raw(a10);
        _loop_l1 = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// lookup key l finds value for key in association list.
uint64_t LoopifyLists::lookup(
    uint64_t key, const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        return v;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

/// group l groups consecutive equal elements: 1,1,2,2,2,3 -> [1,1],[2,2,2],[3].
LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::group_fuel(uint64_t fuel, const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of group_fuel: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
    uint64_t fuel;
  };

  struct _after_group_fuel_in_false {
    uint64_t a0;
  };

  struct _after_group_fuel_in_true {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_group_fuel_in_false,
                              _after_group_fuel_in_true>;
  LoopifyLists::list<LoopifyLists::list<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = list<LoopifyLists::list<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                l.v())) {
          _result = list<LoopifyLists::list<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                  _sv0.v())) {
            _result = list<LoopifyLists::list<uint64_t>>::cons(
                list<uint64_t>::cons(a0, list<uint64_t>::nil()),
                list<LoopifyLists::list<uint64_t>>::nil());
          } else {
            const auto &[a00, _] =
                std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
            if (a0 == a00) {
              _stack.emplace_back(_after_group_fuel_in_true{a0});
              _stack.emplace_back(_call{crane_raw(a1), f});
            } else {
              _stack.emplace_back(_after_group_fuel_in_false{a0});
              _stack.emplace_back(_call{crane_raw(a1), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_after_group_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_group_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = list<LoopifyLists::list<uint64_t>>::cons(
          list<uint64_t>::cons(a0, list<uint64_t>::nil()), std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_group_fuel_in_true>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      LoopifyLists::list<LoopifyLists::list<uint64_t>> _tmp1 =
          std::move(_result);
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              _tmp1.v_mut())) {
        _result = list<LoopifyLists::list<uint64_t>>::cons(
            list<uint64_t>::cons(a0, list<uint64_t>::nil()),
            list<LoopifyLists::list<uint64_t>>::nil());
      } else {
        auto &[a01, a11] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            _tmp1.v_mut());
        _result = list<LoopifyLists::list<uint64_t>>::cons(
            list<uint64_t>::cons(a0, std::move(a01)), crane::shared_child(a11));
      }
    }
  }
  return _result;
}

LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::group(const LoopifyLists::list<uint64_t> &l) {
  return group_fuel((len_list(l) + 1), l);
}

/// Internal helper: reverse a list.
LoopifyLists::list<uint64_t>
LoopifyLists::rev_helper(LoopifyLists::list<uint64_t> acc,
                         const LoopifyLists::list<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  LoopifyLists::list<uint64_t> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      _loop_l = crane_raw(a1);
      _loop_acc = list<uint64_t>::cons(a0, std::move(_loop_acc));
    }
  }
}

/// reverse_insert x l inserts x and reverses at each step.
LoopifyLists::list<uint64_t>
LoopifyLists::reverse_insert(uint64_t x,
                             const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of reverse_insert: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_reverse_insert_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_reverse_insert_in_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::cons(x, list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_reverse_insert_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_reverse_insert_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = rev_helper(list<uint64_t>::nil(),
                           list<uint64_t>::cons(a0, std::move(_result)));
    }
  }
  return _result;
}

/// Internal helper: append lists.
LoopifyLists::list<uint64_t>
LoopifyLists::app_helper(const LoopifyLists::list<uint64_t> &l1,
                         LoopifyLists::list<uint64_t> l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      auto _value = std::move(l2);
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = typename LoopifyLists::list<uint64_t>::Cons(a0, nullptr);
      LoopifyLists::list<uint64_t> &_node =
          (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyLists::list<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
LoopifyLists::list<uint64_t>
LoopifyLists::double_append(const LoopifyLists::list<uint64_t> &l1,
                            LoopifyLists::list<uint64_t> l2) {
  // Explicit stack replaces the non-tail recursion of double_append: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l1;
  };

  struct _after_double_append_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_double_append_in_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l1.v())) {
        _result = l2;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_after_double_append_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_double_append_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      LoopifyLists::list<uint64_t> rest = std::move(_result);
      _result = list<uint64_t>::cons(a0, app_helper(rest, rest));
    }
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
LoopifyLists::list<uint64_t>
LoopifyLists::remove_if_sum_even(const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        auto _value = list<uint64_t>::cons(a0, list<uint64_t>::nil());
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, _] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        if ((UINT64_C(2) ? (a0 + a00) % UINT64_C(2) : (a0 + a00)) ==
            UINT64_C(0)) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = typename LoopifyLists::list<uint64_t>::Cons(a0, nullptr);
          LoopifyLists::list<uint64_t> &_node =
              (_write ? *(*_write =
                              std::make_shared<LoopifyLists::list<uint64_t>>(
                                  std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

/// split_at n l splits list at index n into (prefix, suffix).
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::split_at(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of split_at: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
    uint64_t n;
  };

  struct _after_split_at_in_false {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_split_at_in_false>;
  std::pair<LoopifyLists::list<uint64_t>,
            LoopifyLists::list<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t n = _f.n;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        if (n == UINT64_C(0)) {
          _result = std::make_pair(list<uint64_t>::nil(), l);
        } else {
          _stack.emplace_back(_after_split_at_in_false{a0});
          _stack.emplace_back(_call{
              crane_raw(a1),
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_split_at_in_false>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto [a, b] = std::move(_result);
      _result =
          std::make_pair(list<uint64_t>::cons(a0, std::move(a)), std::move(b));
    }
  }
  return _result;
}

/// unzip l splits list of pairs into two lists.
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::unzip(const LoopifyLists::list<std::pair<uint64_t,
                                                       uint64_t>> &l) {
  // Explicit stack replaces the non-tail recursion of unzip: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *l;
  };

  struct _after_unzip_in_pair {
    uint64_t a;
    uint64_t b;
  };

  using _frame = std::variant<_call, _after_unzip_in_pair>;
  std::pair<LoopifyLists::list<uint64_t>,
            LoopifyLists::list<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const auto &[a, b] = a0;
        _stack.emplace_back(_after_unzip_in_pair{a, b});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_unzip_in_pair>(_popped));
      _stack.pop_back();
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      auto [xs, ys] = std::move(_result);
      _result = std::make_pair(list<uint64_t>::cons(a, std::move(xs)),
                               list<uint64_t>::cons(b, std::move(ys)));
    }
  }
  return _result;
}

/// nth n l default returns nth element or default if out of bounds.
uint64_t LoopifyLists::nth(uint64_t n, const LoopifyLists::list<uint64_t> &l,
                           uint64_t default0) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return a0;
      } else {
        _loop_l = crane_raw(a1);
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

/// last l default returns last element or default if empty.
uint64_t LoopifyLists::last(const LoopifyLists::list<uint64_t> &l,
                            uint64_t default0) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv.v())) {
        return a0;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

/// drop n l drops first n elements.
LoopifyLists::list<uint64_t>
LoopifyLists::drop(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return list<uint64_t>::nil();
    } else {
      const auto &[_, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return *_loop_l;
      } else {
        _loop_l = crane_raw(a1);
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

/// init l returns all but last element.
LoopifyLists::list<uint64_t>
LoopifyLists::init(const LoopifyLists::list<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyLists::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyLists::list<uint64_t>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv.v())) {
        auto _value = list<uint64_t>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell = typename LoopifyLists::list<uint64_t>::Cons(a0, nullptr);
        LoopifyLists::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// count x l counts occurrences of x in l.
uint64_t LoopifyLists::count(uint64_t x,
                             const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of count: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_count_in_true {};

  using _frame = std::variant<_call, _after_count_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        if (x == a0) {
          _stack.emplace_back(_after_count_in_true{});
          _stack.emplace_back(_call{crane_raw(a1)});
        } else {
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_count_in_true>(_popped));
      _stack.pop_back();
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

/// maximum l finds maximum element (returns 0 for empty list).
uint64_t LoopifyLists::maximum(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of maximum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_maximum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_maximum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_maximum_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_maximum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t max_rest = std::move(_result);
      if (max_rest <= a0) {
        _result = std::move(a0);
      } else {
        _result = std::move(max_rest);
      }
    }
  }
  return _result;
}

/// minmax l finds both minimum and maximum in one pass.
std::pair<uint64_t, uint64_t>
LoopifyLists::minmax(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of minmax: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_minmax_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_minmax_in_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::make_pair(a0, a0);
        } else {
          _stack.emplace_back(_after_minmax_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_minmax_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[lo, hi] = _tmp1;
      _result = std::make_pair((a0 <= lo ? a0 : lo), (hi <= a0 ? a0 : hi));
    }
  }
  return _result;
}

/// Helper for rotate_left.
LoopifyLists::list<uint64_t>
LoopifyLists::rotate_left_fuel(uint64_t fuel, uint64_t n,
                               const LoopifyLists::list<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyLists::list<uint64_t> _loop_l = l;
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _loop_l.v())) {
          return list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<
              typename LoopifyLists::list<uint64_t>::Cons>(_loop_l.v());
          _loop_l =
              app_helper(*a1, list<uint64_t>::cons(a0, list<uint64_t>::nil()));
          _loop_n =
              (((_loop_n - UINT64_C(1)) > _loop_n ? 0
                                                  : (_loop_n - UINT64_C(1))));
          _loop_fuel = f;
        }
      }
    }
  }
}

/// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
/// 3,4,1,2.
LoopifyLists::list<uint64_t>
LoopifyLists::rotate_left(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  return rotate_left_fuel((n + 1), n, l);
}

/// intercalate sep lists joins lists with separator: intercalate 0 [1,2],[3,4]
/// -> 1,2,0,3,4.
LoopifyLists::list<uint64_t> LoopifyLists::intercalate(
    const LoopifyLists::list<uint64_t> &sep,
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> &lists) {
  // Explicit stack replaces the non-tail recursion of intercalate: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> *lists;
  };

  struct _after_intercalate_in_Cons {
    LoopifyLists::list<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_intercalate_in_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&lists});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<LoopifyLists::list<uint64_t>> &lists = *_f.lists;
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              lists.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            lists.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<
                typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_intercalate_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_intercalate_in_Cons>(_popped));
      _stack.pop_back();
      LoopifyLists::list<uint64_t> a0 = std::move(_f.a0);
      _result = app_helper(std::move(a0), app_helper(sep, std::move(_result)));
    }
  }
  return _result;
}

/// majority l finds majority element using Boyer-Moore voting algorithm.
/// Returns (candidate, count).
std::pair<uint64_t, uint64_t>
LoopifyLists::majority(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of majority: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_majority_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_majority_in_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::make_pair(a0, UINT64_C(1));
        } else {
          _stack.emplace_back(_after_majority_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_majority_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[cand, cnt] = _tmp1;
      if (a0 == cand) {
        _result = std::make_pair(cand, (cnt + 1));
      } else {
        if (cnt == UINT64_C(0)) {
          _result = std::make_pair(a0, UINT64_C(1));
        } else {
          _result = std::make_pair(
              cand, (((cnt - UINT64_C(1)) > cnt ? 0 : (cnt - UINT64_C(1)))));
        }
      }
    }
  }
  return _result;
}

/// zip3 l1 l2 l3 zips three lists into triples.
LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
LoopifyLists::zip3(const LoopifyLists::list<uint64_t> &l1,
                   const LoopifyLists::list<uint64_t> &l2,
                   const LoopifyLists::list<uint64_t> &l3) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<
      LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>,
                                   uint64_t>>> _root{};
  std::shared_ptr<
      LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>,
                                   uint64_t>>> *_write = nullptr;
  const LoopifyLists::list<uint64_t> *_loop_l3 = &l3;
  const LoopifyLists::list<uint64_t> *_loop_l2 = &l2;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      auto _value =
          list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyLists::list<
                      std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2->v())) {
        auto _value =
            list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyLists::list<
                        std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] = std::get<
            typename LoopifyLists::list<uint64_t>::Cons>(_loop_l2->v());
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _loop_l3->v())) {
          auto _value =
              list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
          (_write ? *(*_write = std::make_shared<LoopifyLists::list<
                          std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                  _loop_l3->v());
          auto _cell = typename LoopifyLists::list<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Cons(
              std::make_pair(std::make_pair(a0, a00), a01), nullptr);
          LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>,
                                       uint64_t>> &_node =
              (_write ? *(*_write =
                              std::make_shared<LoopifyLists::list<std::pair<
                                  std::pair<uint64_t, uint64_t>, uint64_t>>>(
                                  std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename LoopifyLists::list<
                  std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l3 = crane_raw(a11);
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

/// sum_and_count l returns both sum and count in one pass.
std::pair<uint64_t, uint64_t>
LoopifyLists::sum_and_count(const LoopifyLists::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_and_count: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyLists::list<uint64_t> *l;
  };

  struct _after_sum_and_count_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_and_count_in_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_and_count_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_and_count_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[s, c] = _tmp1;
      _result = std::make_pair((a0 + s), (c + 1));
    }
  }
  return _result;
}

/// elem_at n l returns element at index n (like nth but with different name).
std::optional<uint64_t>
LoopifyLists::elem_at(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return std::make_optional<uint64_t>(a0);
      } else {
        _loop_l = crane_raw(a1);
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}
