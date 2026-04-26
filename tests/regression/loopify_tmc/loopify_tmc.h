#ifndef INCLUDED_LOOPIFY_TMC
#define INCLUDED_LOOPIFY_TMC

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
struct LoopifyTmc {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(
            Cons{clone_as_value<t_A>(d_a0),
                 clone_as_value<std::unique_ptr<list<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) list<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<_CloneT0>(typename list<_CloneT0>::Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<_CloneT0>(typename list<_CloneT0>::Cons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<list<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// app l1 l2 appends two lists. Basic TMC pattern: cons head (app tail l2).
  template <typename T1>
  __attribute__((pure)) static list<T1> app(const list<T1> &l1, list<T1> l2) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<list<T1>>(l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1.v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l1 = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// map f l applies f to every element. TMC with element transform.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static list<T2> map(F0 &&f, const list<T1> &l) {
    std::unique_ptr<list<T2>> _head{};
    std::unique_ptr<list<T2>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<T2>>(list<T2>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<list<T2>>(
            typename list<T2>::Cons(f(d_a0), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T2>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// filter f l keeps elements satisfying f. Mixed tail + TMC branches.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static list<T1> filter(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      if (f(d_a0)) {
        return list<T1>::cons(d_a0, filter<T1>(f, *(d_a1)));
      } else {
        return filter<T1>(f, *(d_a1));
      }
    }
  }

  /// snoc l x appends x at the end. TMC, base case allocates a cell.
  template <typename T1>
  __attribute__((pure)) static list<T1> snoc(const list<T1> &l, const T1 x) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) =
            std::make_unique<list<T1>>(list<T1>::cons(x, list<T1>::nil()));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// replicate n x creates n copies of x. Nat recursion producing list.
  template <typename T1>
  __attribute__((pure)) static list<T1> replicate(const unsigned int &n,
                                                  const T1 x) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(x, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_n = m;
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// range lo hi creates lo, lo+1, ..., hi-1.
  __attribute__((pure)) static list<unsigned int> range(const unsigned int &lo,
                                                        const unsigned int &hi);

  /// zip_with f l1 l2 combines two lists element-wise. Two varying params.
  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  __attribute__((pure)) static list<T3> zip_with(F0 &&f, const list<T1> &l1,
                                                 const list<T2> &l2) {
    std::unique_ptr<list<T3>> _head{};
    std::unique_ptr<list<T3>> *_write = &_head;
    list<T2> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<list<T3>>(list<T3>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2.v())) {
          *(_write) = std::make_unique<list<T3>>(list<T3>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2.v());
          auto _cell = std::make_unique<list<T3>>(
              typename list<T3>::Cons(f(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<T3>::Cons>((*_write)->v_mut()).d_a1;
          list<T2> _next_l2 = *(d_a10);
          list<T1> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// prefix_sums acc l computes running prefix sums.
  __attribute__((pure)) static list<unsigned int>
  prefix_sums(const unsigned int &acc, const list<unsigned int> &l);

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2. Nested TMC.
  template <typename T1>
  __attribute__((pure)) static list<T1> stutter(const list<T1> &l) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        auto _cell1 =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        std::get<typename list<T1>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>(
                      std::get<typename list<T1>::Cons>((*_write)->v_mut())
                          .d_a1->v_mut())
                      .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

#endif // INCLUDED_LOOPIFY_TMC
