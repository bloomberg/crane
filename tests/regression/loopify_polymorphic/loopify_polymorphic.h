#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifyPolymorphic {
  template <typename T1>
  __attribute__((pure)) static unsigned int poly_length(const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {
      decltype(1u) _s0;
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
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static List<T1> poly_reverse(const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {
      decltype(List<T1>::cons(std::declval<T1 &>(), List<T1>::nil())) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{List<T1>::cons(d_a0, List<T1>::nil())});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _result.app(_f._s0);
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static List<T1> poly_append(const List<T1> &l1,
                                                    List<T1> l2) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    List<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<List<T1>>(l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l1.v());
        auto _cell =
            std::make_unique<List<T1>>(typename List<T1>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l1 = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  __attribute__((pure)) static std::optional<T1> poly_last(const List<T1> &l) {
    std::optional<T1> _result;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static List<T1> poly_take(const unsigned int &n,
                                                  const List<T1> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    List<T1> _loop_l = l;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
          *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<T1>::Cons>(_loop_l.v());
          auto _cell = std::make_unique<List<T1>>(
              typename List<T1>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
          List<T1> _next_l = *(d_a1);
          unsigned int _next_n = n_;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  __attribute__((pure)) static List<T1> poly_drop(const unsigned int &n,
                                                  List<T1> l) {
    List<T1> _result;
    List<T1> _loop_l = std::move(l);
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        _result = _loop_l;
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
          _result = List<T1>::nil();
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<T1>::Cons>(_loop_l.v());
          List<T1> _next_l = *(d_a1);
          unsigned int _next_n = n_;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static std::optional<T1> poly_nth(const unsigned int &n,
                                                          const List<T1> &l) {
    std::optional<T1> _result;
    List<T1> _loop_l = l;
    unsigned int _loop_n = n;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        if (_loop_n == 0u) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          List<T1> _next_l = *(d_a1);
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static List<T1> poly_filter(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      if (p(d_a0)) {
        return List<T1>::cons(d_a0, poly_filter<T1>(p, *(d_a1)));
      } else {
        return poly_filter<T1>(p, *(d_a1));
      }
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static List<T2> poly_map(F0 &&f, const List<T1> &l) {
    std::unique_ptr<List<T2>> _head{};
    std::unique_ptr<List<T2>> *_write = &_head;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<List<T2>>(List<T2>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<List<T2>>(
            typename List<T2>::Cons(f(d_a0), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<T2>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static List<std::pair<T1, T2>>
  poly_zip(const List<T1> &l1, const List<T2> &l2) {
    std::unique_ptr<List<std::pair<T1, T2>>> _head{};
    std::unique_ptr<List<std::pair<T1, T2>>> *_write = &_head;
    List<T2> _loop_l2 = l2;
    List<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<List<std::pair<T1, T2>>>(
            List<std::pair<T1, T2>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<T2>::Nil>(_loop_l2.v())) {
          *(_write) = std::make_unique<List<std::pair<T1, T2>>>(
              List<std::pair<T1, T2>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<T2>::Cons>(_loop_l2.v());
          auto _cell = std::make_unique<List<std::pair<T1, T2>>>(
              typename List<std::pair<T1, T2>>::Cons(
                  std::make_pair(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<std::pair<T1, T2>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          List<T2> _next_l2 = *(d_a10);
          List<T1> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static std::pair<List<T1>, List<T2>>
  poly_unzip(const List<std::pair<T1, T2>> &l) {
    struct _Enter {
      const List<std::pair<T1, T2>> l;
    };

    struct _Call1 {
      T1 _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<T1>, List<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<std::pair<T1, T2>> l = _f.l;
        if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
                l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T2>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<std::pair<T1, T2>>::Cons>(l.v());
          const T1 &a = d_a0.first;
          const T2 &b = d_a0.second;
          _stack.emplace_back(_Call1{a, b});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 a = _f._s0;
        T2 b = _f._s1;
        const List<T1> &as_ = _result.first;
        const List<T2> &bs = _result.second;
        _result = std::make_pair(List<T1>::cons(a, as_), List<T2>::cons(b, bs));
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<List<T1>, List<T1>>
  poly_partition(F0 &&p, const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {
      T1 _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<T1>, List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, p});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        F0 p = _f._s1;
        const List<T1> &trues = _result.first;
        const List<T1> &falses = _result.second;
        if (p(d_a0)) {
          _result = std::make_pair(List<T1>::cons(d_a0, trues), falses);
        } else {
          _result = std::make_pair(trues, List<T1>::cons(d_a0, falses));
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bool poly_member(F0 &&eq, const T1 x,
                                                const List<T1> &l) {
    bool _result;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        if (eq(x, d_a0)) {
          _result = true;
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static List<T1> poly_replicate(const unsigned int &n,
                                                       const T1 x) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        auto _cell =
            std::make_unique<List<T1>>(typename List<T1>::Cons(x, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*(_head));
  }

  __attribute__((pure)) static unsigned int
  nat_length(const List<unsigned int> &_x0);
  __attribute__((pure)) static List<unsigned int>
  nat_reverse(const List<unsigned int> &_x0);
  __attribute__((pure)) static List<unsigned int>
  nat_append(const List<unsigned int> &_x0, const List<unsigned int> &_x1);
  __attribute__((pure)) static std::optional<unsigned int>
  nat_last(const List<unsigned int> &_x0);
  __attribute__((pure)) static List<unsigned int>
  nat_take(const unsigned int &_x0, const List<unsigned int> &_x1);
  __attribute__((pure)) static List<unsigned int>
  nat_drop(const unsigned int &_x0, const List<unsigned int> &_x1);
  __attribute__((pure)) static std::optional<unsigned int>
  nat_nth(const unsigned int &_x0, const List<unsigned int> &_x1);
  __attribute__((pure)) static bool nat_eq(const unsigned int &_x0,
                                           const unsigned int &_x1);
  __attribute__((pure)) static bool is_even(const unsigned int &x);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  nat_filter(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_filter<unsigned int>(_x0, _x1);
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  nat_map(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_map<unsigned int, unsigned int>(_x0, _x1);
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  nat_partition(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_partition<unsigned int>(_x0, _x1);
  }

  __attribute__((pure)) static bool nat_member(const unsigned int &_x0,
                                               const List<unsigned int> &_x1);
  __attribute__((pure)) static List<unsigned int>
  nat_replicate(const unsigned int &_x0, const unsigned int &_x1);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
