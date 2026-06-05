#ifndef INCLUDED_LOOPIFY_PAIRS
#define INCLUDED_LOOPIFY_PAIRS

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE pair/tuple operations.
struct LoopifyPairs {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a, l] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a.type() == typeid(A))
                  return std::any_cast<A>(a);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a);
              } else
                return A(a);
            }(),
            l ? std::make_shared<list<A>>(*l) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list(Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l) {
            _stack.push_back(std::move(_alt->l));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.f0)(std::move(_f.a0), std::move(_f.a1),
                                   std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(T2 f, F1 &&f0,
           const list<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.f0)(std::move(_f.a0), std::move(_f.a1),
                                   std::move(_result));
      }
    }
    return _result;
  }

  /// partition p l splits into (satisfies p, doesn't satisfy p).
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::pair<list<T1>, list<T1>>
  partition(F0 &&p,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Cont_Cons: saves [a0, p], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      T1 a0;
      F0 p;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto p = std::move(_f.p);
        auto _cs = std::move(_result);
        list<T1> yes = std::move(_cs.first);
        list<T1> no = std::move(_cs.second);
        if (p(a0)) {
          _result =
              std::make_pair(list<T1>::cons(a0, std::move(yes)), std::move(no));
        } else {
          _result =
              std::make_pair(std::move(yes), list<T1>::cons(a0, std::move(no)));
        }
      }
    }
    return _result;
  }

  /// unzip l splits list of nat pairs into pair of lists.
  static std::pair<list<uint64_t>, list<uint64_t>>
  unzip(const list<std::pair<uint64_t, uint64_t>> &l);

  /// zip combines two lists into pairs.
  template <typename T1, typename T2>
  static list<std::pair<T1, T2>>
  zip(const list<T1> &l1,
      const list<T2> &
          l2) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<T2> *l2;
      const list<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(std::make_pair(std::declval<T1 &>(),
                                           std::declval<T2 &>()))>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<std::pair<T1, T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l2, &l1});
    /// Loopified zip: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T2> &l2 = *_f.l2;
        const list<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
          _result = list<std::pair<T1, T2>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
          if (std::holds_alternative<typename list<T2>::Nil>(l2.v())) {
            _result = list<std::pair<T1, T2>>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename list<T2>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a00)});
            _stack.emplace_back(_Enter{a10.get(), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<std::pair<T1, T2>>::cons(_f._s0, std::move(_result));
      }
    }
    return _result;
  } /// zip3 combines three lists.

  template <typename T1, typename T2, typename T3>
  static list<std::pair<T1, std::pair<T2, T3>>>
  zip3(const list<T1> &l1, const list<T2> &l2,
       const list<T3> &l3) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const list<T3> *l3;
      const list<T2> *l2;
      const list<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(std::make_pair(
          std::declval<T1 &>(),
          std::make_pair(std::declval<T2 &>(), std::declval<T3 &>())))>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<std::pair<T1, std::pair<T2, T3>>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l3, &l2, &l1});
    /// Loopified zip3: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T3> &l3 = *_f.l3;
        const list<T2> &l2 = *_f.l2;
        const list<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
          _result = list<std::pair<T1, std::pair<T2, T3>>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
          if (std::holds_alternative<typename list<T2>::Nil>(l2.v())) {
            _result = list<std::pair<T1, std::pair<T2, T3>>>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename list<T2>::Cons>(l2.v());
            if (std::holds_alternative<typename list<T3>::Nil>(l3.v())) {
              _result = list<std::pair<T1, std::pair<T2, T3>>>::nil();
            } else {
              const auto &[a01, a11] =
                  std::get<typename list<T3>::Cons>(l3.v());
              _stack.emplace_back(
                  _Resume_Cons{std::make_pair(a0, std::make_pair(a00, a01))});
              _stack.emplace_back(_Enter{a11.get(), a10.get(), a1.get()});
            }
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<std::pair<T1, std::pair<T2, T3>>>::cons(
            _f._s0, std::move(_result));
      }
    }
    return _result;
  } /// split_at n l splits at position n.

  template <typename T1>
  static std::pair<list<T1>, list<T1>>
  split_at(uint64_t n,
           list<T1> l) { /// _Enter: captures varying parameters for each
                         /// recursive call.

    struct _Enter {
      list<T1> l;
      uint64_t n;
    };

    /// _Cont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l), n});
    /// Loopified split_at: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<T1> l = std::move(_f.l);
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = std::make_pair(list<T1>::nil(), std::move(l));
        } else {
          uint64_t m = n - 1;
          if (std::holds_alternative<typename list<T1>::Nil>(l.v_mut())) {
            _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
          } else {
            auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v_mut());
            _stack.emplace_back(_Cont_Cons{std::move(a0)});
            _stack.emplace_back(_Enter{*a1, m});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto _cs = std::move(_result);
        list<T1> taken = std::move(_cs.first);
        list<T1> rest = std::move(_cs.second);
        _result = std::make_pair(
            list<T1>::cons(std::move(a0), std::move(taken)), std::move(rest));
      }
    }
    return _result;
  }

  /// swizzle separates into even/odd positions.
  template <typename T1>
  static std::pair<list<T1>, list<T1>>
  swizzle(const list<T1> &l) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Cont_Cons: saves [a0, a00], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      T1 a0;
      T1 a00;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified swizzle: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(list<T1>::cons(a0, list<T1>::nil()),
                                     list<T1>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Cont_Cons{a0, a00});
            _stack.emplace_back(_Enter{a10.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto a00 = std::move(_f.a00);
        auto _cs = std::move(_result);
        list<T1> evens = std::move(_cs.first);
        list<T1> odds = std::move(_cs.second);
        _result = std::make_pair(list<T1>::cons(a0, std::move(evens)),
                                 list<T1>::cons(a00, std::move(odds)));
      }
    }
    return _result;
  }

  /// span p l splits at first element not satisfying p.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::pair<list<T1>, list<T1>>
  span(F0 &&p,
       const list<T1> &
           l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified span: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _result = std::make_pair(list<T1>::nil(), list<T1>::cons(a0, *a1));
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        auto a0 = std::move(_f.a0);
        auto _cs = std::move(_result);
        list<T1> ys = std::move(_cs.first);
        list<T1> zs = std::move(_cs.second);
        _result =
            std::make_pair(list<T1>::cons(a0, std::move(ys)), std::move(zs));
      }
    }
    return _result;
  }

  /// partition3 pivot l three-way partition around pivot.
  static std::pair<list<uint64_t>, std::pair<list<uint64_t>, list<uint64_t>>>
  partition3(uint64_t pivot, const list<uint64_t> &l);
  /// min_max l finds both min and max in one pass.
  static std::pair<uint64_t, uint64_t> min_max(const list<uint64_t> &l);
  /// sum_and_count computes both in one pass.
  static std::pair<uint64_t, uint64_t> sum_and_count(const list<uint64_t> &l);
  /// sum_prod_count triple accumulator.
  static std::pair<uint64_t, std::pair<uint64_t, uint64_t>>
  sum_prod_count(const list<uint64_t> &l);

  /// mapAccumL f acc l map with accumulator threading.
  template <typename F0>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F0 &,
                                   uint64_t &, uint64_t &>
  static std::pair<uint64_t, list<uint64_t>>
  mapAccumL(F0 &&f, uint64_t acc,
            const list<uint64_t> &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
      uint64_t acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      uint64_t y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<uint64_t, list<uint64_t>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified mapAccumL: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        uint64_t acc = _f.acc;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          auto _cs = f(acc, a0);
          uint64_t acc_ = std::move(_cs.first);
          uint64_t y = std::move(_cs.second);
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(acc_)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        uint64_t y = _f.y;
        auto _cs1 = std::move(_result);
        uint64_t final_acc = std::move(_cs1.first);
        list<uint64_t> ys = std::move(_cs1.second);
        _result = std::make_pair(std::move(final_acc),
                                 list<uint64_t>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }

  /// lookup_all key l finds all values associated with key.
  static list<uint64_t>
  lookup_all(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);
  /// swap_pairs l swaps elements in each pair.
  static list<std::pair<uint64_t, uint64_t>>
  swap_pairs(const list<std::pair<uint64_t, uint64_t>> &l);
};

#endif // INCLUDED_LOOPIFY_PAIRS
