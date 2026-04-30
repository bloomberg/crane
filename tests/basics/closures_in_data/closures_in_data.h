#ifndef INCLUDED_CLOSURES_IN_DATA
#define INCLUDED_CLOSURES_IN_DATA

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

  template <typename T1, MapsTo<T1, t_A> F0> List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }
};

struct ClosuresInData {
  /// A list of functions: successor, doubling, and squaring.
  static inline const List<std::function<unsigned int(unsigned int)>> fn_list =
      List<std::function<unsigned int(unsigned int)>>::cons(
          [](unsigned int x) { return (x + 1); },
          List<std::function<unsigned int(unsigned int)>>::cons(
              [](const unsigned int &x) { return (x + x); },
              List<std::function<unsigned int(unsigned int)>>::cons(
                  [](const unsigned int &x) { return (x * x); },
                  List<std::function<unsigned int(unsigned int)>>::nil())));
  /// apply_all fns x applies every function in fns to x,
  /// returning the list of results.
  static List<unsigned int>
  apply_all(const List<std::function<unsigned int(unsigned int)>> &fns,
            unsigned int x);

  /// A pair of invertible transformations: forward and backward.
  struct transform {
    std::function<unsigned int(unsigned int)> forward;
    std::function<unsigned int(unsigned int)> backward;

    // ACCESSORS
    transform clone() const {
      return transform{(*(this)).forward, (*(this)).backward};
    }
  };

  /// A transform that doubles via addition and halves via division.
  static inline const transform double_transform =
      transform{[](const unsigned int &x) { return (x + x); },
                [](const unsigned int &x) { return (2u ? x / 2u : 0); }};
  static unsigned int apply_forward(const transform &t, const unsigned int &x);
  static unsigned int apply_backward(const transform &t, const unsigned int &x);
  /// compose_all fns x folds fns left, threading x through each
  /// function in sequence.
  static unsigned int
  compose_all(const List<std::function<unsigned int(unsigned int)>> &fns,
              const unsigned int &x);
  /// A pipeline of transformations: increment, double, then add 10.
  static inline const List<std::function<unsigned int(unsigned int)>> pipeline =
      List<std::function<unsigned int(unsigned int)>>::cons(
          [](const unsigned int &x) { return (x + 1u); },
          List<std::function<unsigned int(unsigned int)>>::cons(
              [](const unsigned int &x) { return (x * 2u); },
              List<std::function<unsigned int(unsigned int)>>::cons(
                  [](const unsigned int &x) { return (x + 10u); },
                  List<std::function<unsigned int(unsigned int)>>::nil())));
  /// maybe_apply mf x applies function mf to x if present,
  /// otherwise returns x unchanged.
  static unsigned int maybe_apply(
      const std::optional<std::function<unsigned int(unsigned int)>> &mf,
      unsigned int x);
  static inline const List<unsigned int> test_apply_all =
      apply_all(fn_list, 5u);
  static inline const unsigned int test_forward =
      apply_forward(double_transform, 7u);
  static inline const unsigned int test_backward =
      apply_backward(double_transform, 14u);
  static inline const unsigned int test_compose = compose_all(pipeline, 3u);
  static inline const unsigned int test_maybe_some =
      maybe_apply(std::make_optional<std::function<unsigned int(unsigned int)>>(
                      [](unsigned int x) { return (x + 1); }),
                  41u);
  static inline const unsigned int test_maybe_none = maybe_apply(
      std::optional<std::function<unsigned int(unsigned int)>>(), 42u);
};

#endif // INCLUDED_CLOSURES_IN_DATA
