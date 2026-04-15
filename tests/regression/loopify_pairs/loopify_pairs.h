#ifndef INCLUDED_LOOPIFY_PAIRS
#define INCLUDED_LOOPIFY_PAIRS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

/// Consolidated UNIQUE pair/tuple operations.
struct LoopifyPairs {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      std::shared_ptr<list<T1>> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l->v());
          _stack.emplace_back(_Call1{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      std::shared_ptr<list<T1>> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l->v());
          _stack.emplace_back(_Call1{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// partition p l splits into (satisfies p, doesn't satisfy p).
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<list<T1>>,
                                         std::shared_ptr<list<T1>>>
  partition(F0 &&p, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      F0 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<list<T1>>, std::shared_ptr<list<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l->v());
          _stack.emplace_back(_Call1{p, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        F0 p = _f._s0;
        T1 d_a0 = _f._s1;
        const std::shared_ptr<list<T1>> &yes = _result.first;
        const std::shared_ptr<list<T1>> &no = _result.second;
        if (p(d_a0)) {
          _result = std::make_pair(list<T1>::cons(d_a0, yes), no);
        } else {
          _result = std::make_pair(yes, list<T1>::cons(d_a0, no));
        }
      }
    }
    return _result;
  }

  /// unzip l splits list of nat pairs into pair of lists.
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  unzip(const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);

  /// zip combines two lists into pairs.
  template <typename T1, typename T2>
  static std::shared_ptr<list<std::pair<T1, T2>>>
  zip(const std::shared_ptr<list<T1>> &l1,
      const std::shared_ptr<list<T2>> &l2) {
    std::shared_ptr<list<std::pair<T1, T2>>> _head{};
    std::shared_ptr<list<std::pair<T1, T2>>> _last{};
    std::shared_ptr<list<T2>> _loop_l2 = l2;
    std::shared_ptr<list<T1>> _loop_l1 = l1;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        if (_last) {
          std::get<typename list<std::pair<T1, T2>>::Cons>(_last->v_mut())
              .d_a1 = list<std::pair<T1, T2>>::nil();
        } else {
          _head = list<std::pair<T1, T2>>::nil();
        }
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          if (_last) {
            std::get<typename list<std::pair<T1, T2>>::Cons>(_last->v_mut())
                .d_a1 = list<std::pair<T1, T2>>::nil();
          } else {
            _head = list<std::pair<T1, T2>>::nil();
          }
          _continue = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = list<std::pair<T1, T2>>::cons(
              std::make_pair(d_a0, d_a00), nullptr);
          if (_last) {
            std::get<typename list<std::pair<T1, T2>>::Cons>(_last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<list<T2>> _next_l2 = d_a10;
          std::shared_ptr<list<T1>> _next_l1 = d_a1;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return _head;
  } /// zip3 combines three lists.

  template <typename T1, typename T2, typename T3>
  static std::shared_ptr<list<std::pair<T1, std::pair<T2, T3>>>>
  zip3(const std::shared_ptr<list<T1>> &l1, const std::shared_ptr<list<T2>> &l2,
       const std::shared_ptr<list<T3>> &l3) {
    std::shared_ptr<list<std::pair<T1, std::pair<T2, T3>>>> _head{};
    std::shared_ptr<list<std::pair<T1, std::pair<T2, T3>>>> _last{};
    std::shared_ptr<list<T3>> _loop_l3 = l3;
    std::shared_ptr<list<T2>> _loop_l2 = l2;
    std::shared_ptr<list<T1>> _loop_l1 = l1;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        if (_last) {
          std::get<typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
              _last->v_mut())
              .d_a1 = list<std::pair<T1, std::pair<T2, T3>>>::nil();
        } else {
          _head = list<std::pair<T1, std::pair<T2, T3>>>::nil();
        }
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          if (_last) {
            std::get<typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
                _last->v_mut())
                .d_a1 = list<std::pair<T1, std::pair<T2, T3>>>::nil();
          } else {
            _head = list<std::pair<T1, std::pair<T2, T3>>>::nil();
          }
          _continue = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          if (std::holds_alternative<typename list<T3>::Nil>(_loop_l3->v())) {
            if (_last) {
              std::get<typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
                  _last->v_mut())
                  .d_a1 = list<std::pair<T1, std::pair<T2, T3>>>::nil();
            } else {
              _head = list<std::pair<T1, std::pair<T2, T3>>>::nil();
            }
            _continue = false;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename list<T3>::Cons>(_loop_l3->v());
            auto _cell = list<std::pair<T1, std::pair<T2, T3>>>::cons(
                std::make_pair(d_a0, std::make_pair(d_a00, d_a01)), nullptr);
            if (_last) {
              std::get<typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
                  _last->v_mut())
                  .d_a1 = _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<list<T3>> _next_l3 = d_a11;
            std::shared_ptr<list<T2>> _next_l2 = d_a10;
            std::shared_ptr<list<T1>> _next_l1 = d_a1;
            _loop_l3 = std::move(_next_l3);
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
            continue;
          }
        }
      }
    }
    return _head;
  } /// split_at n l splits at position n.

  template <typename T1>
  __attribute__((pure)) static std::pair<std::shared_ptr<list<T1>>,
                                         std::shared_ptr<list<T1>>>
  split_at(const unsigned int n, std::shared_ptr<list<T1>> l) {
    struct _Enter {
      std::shared_ptr<list<T1>> l;
      const unsigned int n;
    };

    struct _Call1 {
      T1 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<list<T1>>, std::shared_ptr<list<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        std::shared_ptr<list<T1>> l = _f.l;
        const unsigned int n = _f.n;
        if (n <= 0) {
          _result = std::make_pair(list<T1>::nil(), std::move(l));
        } else {
          unsigned int m = n - 1;
          if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
            _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list<T1>::Cons>(l->v());
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{d_a1, m});
          }
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        T1 d_a0 = _f._s0;
        const std::shared_ptr<list<T1>> &taken = _result.first;
        const std::shared_ptr<list<T1>> &rest = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, taken), rest);
      }
    }
    return _result;
  }

  /// swizzle separates into even/odd positions.
  template <typename T1>
  __attribute__((pure)) static std::pair<std::shared_ptr<list<T1>>,
                                         std::shared_ptr<list<T1>>>
  swizzle(const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      T1 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<list<T1>>, std::shared_ptr<list<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l->v());
          if (std::holds_alternative<typename list<T1>::Nil>(d_a1->v())) {
            _result = std::make_pair(list<T1>::cons(d_a0, list<T1>::nil()),
                                     list<T1>::nil());
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename list<T1>::Cons>(d_a1->v());
            _stack.emplace_back(_Call1{d_a00, d_a0});
            _stack.emplace_back(_Enter{d_a10});
          }
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        T1 d_a00 = _f._s0;
        T1 d_a0 = _f._s1;
        const std::shared_ptr<list<T1>> &evens = _result.first;
        const std::shared_ptr<list<T1>> &odds = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, evens),
                                 list<T1>::cons(d_a00, odds));
      }
    }
    return _result;
  }

  /// span p l splits at first element not satisfying p.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<list<T1>>,
                                         std::shared_ptr<list<T1>>>
  span(F0 &&p, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      T1 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<list<T1>>, std::shared_ptr<list<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l->v());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{d_a1});
          } else {
            _result =
                std::make_pair(list<T1>::nil(), list<T1>::cons(d_a0, d_a1));
          }
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        T1 d_a0 = _f._s0;
        const std::shared_ptr<list<T1>> &ys = _result.first;
        const std::shared_ptr<list<T1>> &zs = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, ys), zs);
      }
    }
    return _result;
  }

  /// partition3 pivot l three-way partition around pivot.
  __attribute__((
      pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                              std::pair<std::shared_ptr<list<unsigned int>>,
                                        std::shared_ptr<list<unsigned int>>>>
  partition3(const unsigned int pivot,
             const std::shared_ptr<list<unsigned int>> &l);
  /// min_max l finds both min and max in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  min_max(const std::shared_ptr<list<unsigned int>> &l);
  /// sum_and_count computes both in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  sum_and_count(const std::shared_ptr<list<unsigned int>> &l);
  /// sum_prod_count triple accumulator.
  __attribute__((pure)) static std::pair<unsigned int,
                                         std::pair<unsigned int, unsigned int>>
  sum_prod_count(const std::shared_ptr<list<unsigned int>> &l);

  /// mapAccumL f acc l map with accumulator threading.
  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((
      pure)) static std::pair<unsigned int, std::shared_ptr<list<unsigned int>>>
  mapAccumL(F0 &&f, const unsigned int acc,
            const std::shared_ptr<list<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<list<unsigned int>> l;
      const unsigned int acc;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<unsigned int, std::shared_ptr<list<unsigned int>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<unsigned int>> l = _f.l;
        const unsigned int acc = _f.acc;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l->v())) {
          _result = std::make_pair(acc, list<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l->v());
          auto _cs = f(acc, d_a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Call1{y});
          _stack.emplace_back(_Enter{d_a1, acc_});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        unsigned int y = _f._s0;
        const unsigned int &final_acc = _result.first;
        const std::shared_ptr<list<unsigned int>> &ys = _result.second;
        _result = std::make_pair(final_acc, list<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }

  /// lookup_all key l finds all values associated with key.
  static std::shared_ptr<list<unsigned int>> lookup_all(
      const unsigned int key,
      const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);
  /// swap_pairs l swaps elements in each pair.
  static std::shared_ptr<list<std::pair<unsigned int, unsigned int>>>
  swap_pairs(
      const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);
};

#endif // INCLUDED_LOOPIFY_PAIRS
