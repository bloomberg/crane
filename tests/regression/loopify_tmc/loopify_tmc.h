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
  template <typename T1> static list<T1> app(const list<T1> &l1, list<T1> l2) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l2 = std::move(l2);
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        *_write = std::make_shared<list<T1>>(std::move(_loop_l2));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).l;
        _loop_l1 = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  /// map f l applies f to every element. TMC with element transform.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static list<T2> map(F0 &&f, const list<T1> &l) {
    std::shared_ptr<list<T2>> _head{};
    std::shared_ptr<list<T2>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T2>>(list<T2>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_shared<list<T2>>(typename list<T2>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T2>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  /// filter f l keeps elements satisfying f. Mixed tail + TMC branches.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static list<T1> filter(F0 &&f, const list<T1> &l) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (f(a0)) {
          auto _cell =
              std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).l;
          _loop_l = a1.get();
          continue;
        } else {
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// snoc l x appends x at the end. TMC, base case allocates a cell.
  template <typename T1> static list<T1> snoc(const list<T1> &l, T1 x) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write =
            std::make_shared<list<T1>>(list<T1>::cons(x, list<T1>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  /// replicate n x creates n copies of x. Nat recursion producing list.
  template <typename T1> static list<T1> replicate(uint64_t n, T1 x) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_shared<list<T1>>(list<T1>::nil());
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).l;
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// range lo hi creates lo, lo+1, ..., hi-1.
  static list<uint64_t> range(uint64_t lo, uint64_t hi);

  /// zip_with f l1 l2 combines two lists element-wise. Two varying params.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static list<T3> zip_with(F0 &&f, const list<T1> &l1, const list<T2> &l2) {
    std::shared_ptr<list<T3>> _head{};
    std::shared_ptr<list<T3>> *_write = &_head;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        *_write = std::make_shared<list<T3>>(list<T3>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          *_write = std::make_shared<list<T3>>(list<T3>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = std::make_shared<list<T3>>(
              typename list<T3>::Cons(f(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<T3>::Cons>((*_write)->v_mut()).l;
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// prefix_sums acc l computes running prefix sums.
  static list<uint64_t> prefix_sums(uint64_t acc, const list<uint64_t> &l);

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2. Nested TMC.
  template <typename T1> static list<T1> stutter(const list<T1> &l) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        auto _cell1 =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        std::get<typename list<T1>::Cons>(_cell->v_mut()).l = std::move(_cell1);
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>(
                      std::get<typename list<T1>::Cons>((*_write)->v_mut())
                          .l->v_mut())
                      .l;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

#endif // INCLUDED_LOOPIFY_TMC
