#ifndef INCLUDED_TAILREC_REORDER_PROBE
#define INCLUDED_TAILREC_REORDER_PROBE

#include <memory>
#include <optional>
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

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
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
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
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
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
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

struct TailrecReorderProbe {
  /// Custom list to control exact code generation.
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<t_A>(Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<t_A>(
            Mycons{clone_as_value<t_A>(d_a0),
                   clone_as_value<std::unique_ptr<mylist<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) mylist<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Mycons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<mylist<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist<t_A> mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0,
                                                    const mylist<t_A> &a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> *operator->() { return this; }

    __attribute__((pure)) const mylist<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0, const mylist<T1> &m) {
    struct _Enter {
      const mylist<T1> m;
    };

    struct _Call1 {
      mylist<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m.v());
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

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0, const mylist<T1> &m) {
    struct _Enter {
      const mylist<T1> m;
    };

    struct _Call1 {
      mylist<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m.v());
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

  /// Tail-recursive reverse via accumulator.
  ///
  /// BUG HYPOTHESIS: When loopified, the assignments to loop variables
  /// l := t and acc := mycons h acc must happen in the right order.
  /// If l := t fires first, the old list node may be freed (when
  /// use_count drops to 0), making h a dangling reference in the
  /// subsequent mycons h acc construction.
  ///
  /// This is a potential evaluation-order / use-after-free bug in the
  /// loopify pass.
  template <typename T1>
  __attribute__((pure)) static mylist<T1> my_rev_append(const mylist<T1> &l,
                                                        mylist<T1> acc) {
    mylist<T1> _result;
    mylist<T1> _loop_acc = std::move(acc);
    mylist<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l.v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l.v());
        mylist<T1> _next_acc = mylist<T1>::mycons(d_a0, _loop_acc);
        mylist<T1> _next_l = *(d_a1);
        _loop_acc = std::move(_next_acc);
        _loop_l = std::move(_next_l);
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static mylist<T1> my_reverse(const mylist<T1> &l) {
    return my_rev_append<T1>(l, mylist<T1>::mynil());
  }

  /// Variant: TWO arguments depend on pattern-matched fields.
  /// l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2
  /// Both acc1 and acc2 need h from the OLD l.
  __attribute__((
      pure)) static std::pair<mylist<unsigned int>, mylist<unsigned int>>
  dual_accum(const mylist<unsigned int> &l, mylist<unsigned int> acc1,
             mylist<unsigned int> acc2);

  template <typename T1, MapsTo<unsigned int, T1> F0>
  __attribute__((pure)) static unsigned int mylist_sum(F0 &&f,
                                                       const mylist<T1> &l) {
    struct _Enter {
      const mylist<T1> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> l = _f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  static inline const unsigned int test_rev = mylist_sum<unsigned int>(
      [](unsigned int x) { return x; },
      my_reverse<unsigned int>(mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(
                  2u, mylist<unsigned int>::mycons(
                          3u, mylist<unsigned int>::mynil())))));
  static inline const unsigned int test_dual = []() -> unsigned int {
    auto _cs = dual_accum(
        mylist<unsigned int>::mycons(
            10u, mylist<unsigned int>::mycons(
                     20u, mylist<unsigned int>::mycons(
                              30u, mylist<unsigned int>::mynil()))),
        mylist<unsigned int>::mynil(), mylist<unsigned int>::mynil());
    const mylist<unsigned int> &a = _cs.first;
    const mylist<unsigned int> &b = _cs.second;
    return (mylist_sum<unsigned int>([](unsigned int x) { return x; }, a) +
            mylist_sum<unsigned int>([](unsigned int x) { return x; }, b));
  }();
  /// Tail-recursive function where the recursive argument is a COMPLEX
  /// expression involving multiple pattern variables.
  __attribute__((pure)) static mylist<unsigned int>
  weave(const mylist<unsigned int> &l1, const mylist<unsigned int> &l2,
        mylist<unsigned int> acc);
  static inline const unsigned int test_weave = mylist_sum<unsigned int>(
      [](unsigned int x) { return x; },
      weave(mylist<unsigned int>::mycons(
                1u, mylist<unsigned int>::mycons(
                        3u, mylist<unsigned int>::mynil())),
            mylist<unsigned int>::mycons(
                2u, mylist<unsigned int>::mycons(
                        4u, mylist<unsigned int>::mynil())),
            mylist<unsigned int>::mynil()));
};

#endif // INCLUDED_TAILREC_REORDER_PROBE
