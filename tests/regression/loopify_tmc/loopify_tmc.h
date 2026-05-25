#ifndef INCLUDED_LOOPIFY_TMC
#define INCLUDED_LOOPIFY_TMC

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
struct LoopifyTmc {
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
        _result = _f.f0(_f.a0, _f.a1, _result);
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
        _result = _f.f0(_f.a0, _f.a1, _result);
      }
    }
    return _result;
  }

  /// app l1 l2 appends two lists. Basic TMC pattern: cons head (app tail l2).
  template <typename T1>
  static list<T1> app(const list<T1> &l1,
                      list<T1> l2) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      list<T1> l2;
      const list<T1> *l1;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l2, &l1});
    /// Loopified app: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<T1> l2 = std::move(_f.l2);
        const list<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
          _result = std::move(l2);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{std::move(l2), a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T1>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// map f l applies f to every element. TMC with element transform.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static list<T2>
  map(F0 &&f,
      const list<T1>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      T2 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified map: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T2>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T2>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// filter f l keeps elements satisfying f. Mixed tail + TMC branches.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static list<T1>
  filter(F0 &&f,
         const list<T1> &l) { /// _Enter: captures varying parameters for each
                              /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified filter: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          if (f(a0)) {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<T1>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// snoc l x appends x at the end. TMC, base case allocates a cell.
  template <typename T1>
  static list<T1>
  snoc(const list<T1> &l,
       T1 x) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified snoc: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T1>::cons(x, list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T1>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// replicate n x creates n copies of x. Nat recursion producing list.
  template <typename T1>
  static list<T1> replicate(
      uint64_t n,
      T1 x) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      uint64_t n;
    };

    /// _Resume_m: saves [x], resumes after recursive call with _result.
    struct _Resume_m {
      T1 x;
    };

    using _Frame = std::variant<_Enter, _Resume_m>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified replicate: _Enter -> _Resume_m.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = list<T1>::nil();
        } else {
          uint64_t m = n - 1;
          _stack.emplace_back(_Resume_m{x});
          _stack.emplace_back(_Enter{m});
        }
      } else {
        auto _f = std::move(std::get<_Resume_m>(_frame));
        _result = list<T1>::cons(_f.x, _result);
      }
    }
    return _result;
  }

  /// range lo hi creates lo, lo+1, ..., hi-1.
  static list<uint64_t> range(uint64_t lo, uint64_t hi);

  /// zip_with f l1 l2 combines two lists element-wise. Two varying params.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static list<T3>
  zip_with(F0 &&f, const list<T1> &l1,
           const list<T2> &l2) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T2> *l2;
      const list<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      T3 _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T3> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l2, &l1});
    /// Loopified zip_with: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T2> &l2 = *_f.l2;
        const list<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
          _result = list<T3>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
          if (std::holds_alternative<typename list<T2>::Nil>(l2.v())) {
            _result = list<T3>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename list<T2>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons{f(a0, a00)});
            _stack.emplace_back(_Enter{a10.get(), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T3>::cons(_f._s0, _result);
      }
    }
    return _result;
  }

  /// prefix_sums acc l computes running prefix sums.
  static list<uint64_t> prefix_sums(uint64_t acc, const list<uint64_t> &l);

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2. Nested TMC.
  template <typename T1>
  static list<T1>
  stutter(const list<T1> &l) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [a0_0, a0_1], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      T1 a0_0;
      T1 a0_1;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified stutter: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T1>::cons(_f.a0_0, list<T1>::cons(_f.a0_1, _result));
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_TMC
