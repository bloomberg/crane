#ifndef INCLUDED_LOOPIFY_PAIRS
#define INCLUDED_LOOPIFY_PAIRS

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

/// Consolidated UNIQUE pair/tuple operations.
struct LoopifyPairs {
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

  /// partition p l splits into (satisfies p, doesn't satisfy p).
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<list<T1>, list<T1>>
  partition(F0 &&p, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      T1 _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<list<T1>, list<T1>> _result{};
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
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, p});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        F0 p = _f._s1;
        const list<T1> &yes = _result.first;
        const list<T1> &no = _result.second;
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
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  unzip(const list<std::pair<unsigned int, unsigned int>> &l);

  /// zip combines two lists into pairs.
  template <typename T1, typename T2>
  __attribute__((pure)) static list<std::pair<T1, T2>> zip(const list<T1> &l1,
                                                           const list<T2> &l2) {
    std::unique_ptr<list<std::pair<T1, T2>>> _head{};
    std::unique_ptr<list<std::pair<T1, T2>>> *_write = &_head;
    list<T2> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<list<std::pair<T1, T2>>>(
            list<std::pair<T1, T2>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2.v())) {
          *(_write) = std::make_unique<list<std::pair<T1, T2>>>(
              list<std::pair<T1, T2>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2.v());
          auto _cell = std::make_unique<list<std::pair<T1, T2>>>(
              typename list<std::pair<T1, T2>>::Cons(
                  std::make_pair(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<std::pair<T1, T2>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          list<T2> _next_l2 = *(d_a10);
          list<T1> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  } /// zip3 combines three lists.

  template <typename T1, typename T2, typename T3>
  __attribute__((pure)) static list<std::pair<T1, std::pair<T2, T3>>>
  zip3(const list<T1> &l1, const list<T2> &l2, const list<T3> &l3) {
    std::unique_ptr<list<std::pair<T1, std::pair<T2, T3>>>> _head{};
    std::unique_ptr<list<std::pair<T1, std::pair<T2, T3>>>> *_write = &_head;
    list<T3> _loop_l3 = l3;
    list<T2> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
            list<std::pair<T1, std::pair<T2, T3>>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2.v())) {
          *(_write) = std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
              list<std::pair<T1, std::pair<T2, T3>>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2.v());
          if (std::holds_alternative<typename list<T3>::Nil>(_loop_l3.v())) {
            *(_write) =
                std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
                    list<std::pair<T1, std::pair<T2, T3>>>::nil());
            break;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename list<T3>::Cons>(_loop_l3.v());
            auto _cell =
                std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
                    typename list<std::pair<T1, std::pair<T2, T3>>>::Cons(
                        std::make_pair(d_a0, std::make_pair(d_a00, d_a01)),
                        nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<
                     typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
                     (*_write)->v_mut())
                     .d_a1;
            list<T3> _next_l3 = *(d_a11);
            list<T2> _next_l2 = *(d_a10);
            list<T1> _next_l1 = *(d_a1);
            _loop_l3 = std::move(_next_l3);
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
            continue;
          }
        }
      }
    }
    return std::move(*(_head));
  }

  /// split_at n l splits at position n.
  template <typename T1>
  __attribute__((pure)) static std::pair<list<T1>, list<T1>>
  split_at(const unsigned int &n, list<T1> l) {
    struct _Enter {
      list<T1> l;
      const unsigned int n;
    };

    struct _Call1 {
      T1 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<T1> l = _f.l;
        const unsigned int n = _f.n;
        if (n <= 0) {
          _result = std::make_pair(list<T1>::nil(), l);
        } else {
          unsigned int m = n - 1;
          if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
            _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
          } else {
            const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1), m});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        const list<T1> &taken = _result.first;
        const list<T1> &rest = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, taken), rest);
      }
    }
    return _result;
  }

  /// swizzle separates into even/odd positions.
  template <typename T1>
  __attribute__((pure)) static std::pair<list<T1>, list<T1>>
  swizzle(const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      T1 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<list<T1>, list<T1>> _result{};
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
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          auto &&_sv0 = *(d_a1);
          if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(list<T1>::cons(d_a0, list<T1>::nil()),
                                     list<T1>::nil());
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename list<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Call1{d_a0, d_a00});
            _stack.emplace_back(_Enter{*(d_a10)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        T1 d_a00 = _f._s1;
        const list<T1> &evens = _result.first;
        const list<T1> &odds = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, evens),
                                 list<T1>::cons(d_a00, odds));
      }
    }
    return _result;
  }

  /// span p l splits at first element not satisfying p.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<list<T1>, list<T1>>
  span(F0 &&p, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      T1 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<list<T1>, list<T1>> _result{};
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
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          } else {
            _result =
                std::make_pair(list<T1>::nil(), list<T1>::cons(d_a0, *(d_a1)));
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        const list<T1> &ys = _result.first;
        const list<T1> &zs = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, ys), zs);
      }
    }
    return _result;
  }

  /// partition3 pivot l three-way partition around pivot.
  __attribute__((pure)) static std::pair<
      list<unsigned int>, std::pair<list<unsigned int>, list<unsigned int>>>
  partition3(const unsigned int &pivot, const list<unsigned int> &l);
  /// min_max l finds both min and max in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  min_max(const list<unsigned int> &l);
  /// sum_and_count computes both in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  sum_and_count(const list<unsigned int> &l);
  /// sum_prod_count triple accumulator.
  __attribute__((pure)) static std::pair<unsigned int,
                                         std::pair<unsigned int, unsigned int>>
  sum_prod_count(const list<unsigned int> &l);

  /// mapAccumL f acc l map with accumulator threading.
  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((pure)) static std::pair<unsigned int, list<unsigned int>>
  mapAccumL(F0 &&f, unsigned int acc, const list<unsigned int> &l) {
    struct _Enter {
      const list<unsigned int> l;
      unsigned int acc;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<unsigned int, list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<unsigned int> l = _f.l;
        unsigned int acc = _f.acc;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(acc, list<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          auto _cs = f(acc, d_a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Call1{y});
          _stack.emplace_back(_Enter{*(d_a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int y = _f._s0;
        const unsigned int &final_acc = _result.first;
        const list<unsigned int> &ys = _result.second;
        _result = std::make_pair(final_acc, list<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }

  /// lookup_all key l finds all values associated with key.
  __attribute__((pure)) static list<unsigned int>
  lookup_all(const unsigned int &key,
             const list<std::pair<unsigned int, unsigned int>> &l);
  /// swap_pairs l swaps elements in each pair.
  __attribute__((pure)) static list<std::pair<unsigned int, unsigned int>>
  swap_pairs(const list<std::pair<unsigned int, unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_PAIRS
