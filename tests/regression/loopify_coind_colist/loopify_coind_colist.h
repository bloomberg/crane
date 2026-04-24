#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

#include "lazy.h"
#include <functional>
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
  return x ? std::make_shared<T>(x->clone()) : nullptr;
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
};

struct LoopifyCoindColist {
  template <typename t_A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      t_A d_a0;
      std::shared_ptr<colist<t_A>> d_a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<colist<t_A>> conil() {
      return std::make_shared<colist<t_A>>(Conil{});
    }

    static std::shared_ptr<colist<t_A>>
    cocons(t_A a0, std::shared_ptr<colist<t_A>> a1) {
      return std::make_shared<colist<t_A>>(
          Cocons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<colist<t_A>>
    lazy_(std::function<std::shared_ptr<colist<t_A>>()> thunk) {
      return std::make_shared<colist<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<colist<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<colist<T2>>
  comap(F0 &&f, const std::shared_ptr<colist<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<colist<T1>> l;
    };

    using _Frame = std::variant<_Enter>;
    std::shared_ptr<colist<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const std::shared_ptr<colist<T1>> l = _f.l;
      if (std::holds_alternative<typename colist<T1>::Conil>(l->v())) {
        _result = colist<T2>::lazy_([]() -> std::shared_ptr<colist<T2>> {
          return colist<T2>::conil();
        });
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename colist<T1>::Cocons>(l->v());
        _result =
            colist<T2>::lazy_([=]() mutable -> std::shared_ptr<colist<T2>> {
              return colist<T2>::cocons(f(d_a0), comap<T1, T2>(f, d_a1));
            });
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<colist<T1>>
  cotake(const unsigned int &n, const std::shared_ptr<colist<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<colist<T1>> l;
      const unsigned int n;
    };

    using _Frame = std::variant<_Enter>;
    std::shared_ptr<colist<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const std::shared_ptr<colist<T1>> l = _f.l;
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = colist<T1>::lazy_([]() -> std::shared_ptr<colist<T1>> {
          return colist<T1>::conil();
        });
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(l->v())) {
          _result = colist<T1>::lazy_([]() -> std::shared_ptr<colist<T1>> {
            return colist<T1>::conil();
          });
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename colist<T1>::Cocons>(l->v());
          _result =
              colist<T1>::lazy_([=]() mutable -> std::shared_ptr<colist<T1>> {
                return colist<T1>::cocons(d_a0, cotake<T1>(n_, d_a1));
              });
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<colist<T1>> from_list(const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    using _Frame = std::variant<_Enter>;
    std::shared_ptr<colist<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<T1> l = _f.l;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        _result = colist<T1>::lazy_([]() -> std::shared_ptr<colist<T1>> {
          return colist<T1>::conil();
        });
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        _result = colist<T1>::lazy_([&]() -> std::shared_ptr<colist<T1>> {
          return colist<T1>::cocons(d_a0, from_list<T1>(*(d_a1)));
        });
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static List<T1>
  to_list(const unsigned int &fuel, const std::shared_ptr<colist<T1>> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    std::shared_ptr<colist<T1>> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(_loop_l->v())) {
          *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename colist<T1>::Cocons>(_loop_l->v());
          auto _cell = std::make_unique<List<T1>>(
              typename List<T1>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
          std::shared_ptr<colist<T1>> _next_l = d_a1;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  static inline const List<unsigned int> test_comap = to_list<unsigned int>(
      5u, comap<unsigned int, unsigned int>(
              [](const unsigned int &n) { return (n * 2u); },
              from_list<unsigned int>(List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          2u, List<unsigned int>::cons(
                                  3u, List<unsigned int>::nil()))))));
  static inline const List<unsigned int> test_cotake = to_list<unsigned int>(
      10u, cotake<unsigned int>(
               2u, from_list<unsigned int>(List<unsigned int>::cons(
                       10u, List<unsigned int>::cons(
                                20u, List<unsigned int>::cons(
                                         30u, List<unsigned int>::nil()))))));
};

#endif // INCLUDED_LOOPIFY_COIND_COLIST
