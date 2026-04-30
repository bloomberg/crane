#ifndef INCLUDED_MONADIC
#define INCLUDED_MONADIC

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }
};

struct Monadic {
  template <typename T1> static std::optional<T1> option_return(const T1 x) {
    return std::make_optional<T1>(x);
  }

  template <typename T1, typename T2, MapsTo<std::optional<T2>, T1> F1>
  static std::optional<T2> option_bind(const std::optional<T1> &ma, F1 &&f) {
    if (ma.has_value()) {
      const T1 &a = *ma;
      return f(a);
    } else {
      return std::optional<T2>();
    }
  }

  static std::optional<unsigned int> safe_div(const unsigned int &n,
                                              const unsigned int &m);
  static std::optional<unsigned int> safe_sub(const unsigned int &n,
                                              const unsigned int &m);
  static std::optional<unsigned int>
  div_then_sub(const unsigned int &a, const unsigned int &b, unsigned int c);
  template <typename s, typename a>
  using State = std::function<std::pair<a, s>(s)>;

  template <typename T1, typename T2>
  static State<T1, T2> state_return(const T2 x) {
    return [=](const T1 s) mutable { return std::make_pair(x, s); };
  }

  template <typename T1, typename T2, typename T3, MapsTo<State<T1, T3>, T2> F1>
  static State<T1, T3> state_bind(const State<T1, T2> ma, F1 &&f) {
    return [=](const T1 s) mutable {
      auto _cs = ma(s);
      const T2 &a = _cs.first;
      const T1 &s_ = _cs.second;
      return f(a)(s_);
    };
  }

  template <typename T1> static const State<T1, T1> &state_get() {
    static const State<T1, T1> v = [](const T1 s) {
      return std::make_pair(s, s);
    };
    return v;
  }

  template <typename T1>
  static State<T1, std::monostate> state_put(const T1 s) {
    return
        [=](const T1) mutable { return std::make_pair(std::monostate{}, s); };
  }

  template <typename T1>
  static State<unsigned int, unsigned int> count_elements(const List<T1> &l) {
    return l.template fold_left<State<unsigned int, unsigned int>>(
        [](const std::function<std::pair<unsigned int, unsigned int>(
               unsigned int)>
               acc,
           const T1) {
          return state_bind<unsigned int, unsigned int,
                            unsigned int>(acc, [](const unsigned int &) {
            return state_bind<unsigned int, unsigned int, unsigned int>(
                state_get<unsigned int>(), [](unsigned int n) {
                  return state_bind<unsigned int, std::monostate, unsigned int>(
                      state_put<unsigned int>((n + 1)),
                      [=](const std::monostate &) mutable {
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
          std::make_optional<unsigned int>(10u), [](const unsigned int &x) {
            return std::make_optional<unsigned int>((x + 1u));
          });
  static inline const std::optional<unsigned int> test_bind_none =
      option_bind<unsigned int, unsigned int>(
          std::optional<unsigned int>(), [](const unsigned int &x) {
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
