#ifndef INCLUDED_MONADIC
#define INCLUDED_MONADIC

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return (*a2).template fold_left<T1>(f, f(a0, a1));
    }
  }
};

struct Monadic {
  template <typename T1> static std::optional<T1> option_return(T1 x) {
    return std::make_optional<T1>(x);
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<std::optional<T2>, F1 &, T1 &>
  static std::optional<T2> option_bind(const std::optional<T1> &ma, F1 &&f) {
    if (ma.has_value()) {
      const T1 &a = *ma;
      return f(a);
    } else {
      return std::optional<T2>();
    }
  }

  static std::optional<unsigned int> safe_div(unsigned int n, unsigned int m);
  static std::optional<unsigned int> safe_sub(unsigned int n, unsigned int m);
  static std::optional<unsigned int>
  div_then_sub(unsigned int a, unsigned int b, unsigned int c);
  template <typename s, typename a>
  using State = std::function<std::pair<a, s>(s)>;

  template <typename T1, typename T2> static State<T1, T2> state_return(T2 x) {
    return [=](T1 s) mutable { return std::make_pair(x, s); };
  }

  template <typename T1, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<State<T1, T3>, F1 &, T2 &>
  static State<T1, T3> state_bind(State<T1, T2> ma, F1 &&f) {
    return [=](const T1 &s) mutable {
      auto _cs = ma(s);
      const T2 &a = _cs.first;
      const T1 &s_ = _cs.second;
      return f(a)(s_);
    };
  }

  template <typename T1> static const State<T1, T1> &state_get() {
    static const State<T1, T1> v = [](const auto &s) {
      return std::make_pair(s, s);
    };
    return v;
  }

  template <typename T1> static State<T1, std::monostate> state_put(T1 s) {
    return
        [=](const T1 &) mutable { return std::make_pair(std::monostate{}, s); };
  }

  template <typename T1>
  static State<unsigned int, unsigned int> count_elements(const List<T1> &l) {
    return l.template fold_left<State<unsigned int, unsigned int>>(
        [](std::function<std::pair<unsigned int, unsigned int>(unsigned int)>
               acc,
           const T1 &) {
          return state_bind<unsigned int, unsigned int,
                            unsigned int>(acc, [](unsigned int) {
            return state_bind<unsigned int, unsigned int, unsigned int>(
                state_get<unsigned int>(), [](unsigned int n) {
                  return state_bind<unsigned int, std::monostate, unsigned int>(
                      state_put<unsigned int>((n + 1)),
                      [=](std::monostate) mutable {
                        return state_return<unsigned int, unsigned int>(n);
                      });
                });
          });
        },
        state_return<unsigned int, unsigned int>(0u));
  }

  static inline const std::optional<unsigned int> test_return =
      option_return<unsigned int>(42u);
  static inline const std::optional<unsigned int> test_bind_some =
      option_bind<unsigned int, unsigned int>(
          std::make_optional<unsigned int>(10u), [](unsigned int x) {
            return std::make_optional<unsigned int>((x + 1u));
          });
  static inline const std::optional<unsigned int> test_bind_none =
      option_bind<unsigned int, unsigned int>(
          std::optional<unsigned int>(), [](unsigned int x) {
            return std::make_optional<unsigned int>((x + 1u));
          });
  static inline const std::optional<unsigned int> test_safe_div_ok =
      safe_div(10u, 3u);
  static inline const std::optional<unsigned int> test_safe_div_zero =
      safe_div(10u, 0u);
  static inline const std::optional<unsigned int> test_chain_ok =
      div_then_sub(20u, 4u, 2u);
  static inline const std::optional<unsigned int> test_chain_fail =
      div_then_sub(20u, 0u, 2u);
  static inline const std::pair<unsigned int, unsigned int> test_state =
      count_elements<unsigned int>(List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::cons(
                                          5u, List<unsigned int>::nil()))))))(
          0u);
};

#endif // INCLUDED_MONADIC
