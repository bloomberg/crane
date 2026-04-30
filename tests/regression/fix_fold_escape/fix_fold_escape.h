#ifndef INCLUDED_FIX_FOLD_ESCAPE
#define INCLUDED_FIX_FOLD_ESCAPE

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
};

struct FixFoldEscape {
  /// Manual fold_left to avoid stdlib extraction complications.
  template <
      MapsTo<List<std::function<unsigned int(unsigned int)>>,
             List<std::function<unsigned int(unsigned int)>>, unsigned int>
          F0>
  static List<std::function<unsigned int(unsigned int)>>
  fold_left(F0 &&f, List<std::function<unsigned int(unsigned int)>> acc,
            const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      return fold_left(f, f(std::move(acc), d_a0), *(d_a1));
    }
  }

  /// Collect fixpoint closures by folding over a list of nats.
  /// Each iteration creates a new fixpoint adder that captures the
  /// current element n from the fold callback's parameter.
  ///
  /// BUG HYPOTHESIS: The callback lambda's parameter n lives on the
  /// callback's stack frame. The fixpoint adder captures n by &.
  /// The callback returns cons adder acc, storing the closure.
  /// After the callback returns, n is destroyed. Later iterations and
  /// the final result contain dangling closures.
  static List<std::function<unsigned int(unsigned int)>>
  collect_adders(const List<unsigned int> &l);
  static unsigned int
  apply_head(const List<std::function<unsigned int(unsigned int)>> &l,
             const unsigned int &x);
  static unsigned int
  sum_apply(const List<std::function<unsigned int(unsigned int)>> &l,
            const unsigned int &x); /// test1: collect_adders 10; 20; 30 ->
                                    /// adder_30; adder_20; adder_10
  /// (reversed by fold_left). apply_head picks adder_30, apply to 5 -> 35.
  static inline const unsigned int test1 = apply_head(
      collect_adders(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil())))),
      5u);
  /// test2: Sum all adders applied to 0.
  /// adder_30(0) + adder_20(0) + adder_10(0) = 30 + 20 + 10 = 60.
  static inline const unsigned int test2 = sum_apply(
      collect_adders(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil())))),
      0u);
  /// test3: With noise between collection and use.
  static inline const unsigned int test3 = []() {
    List<std::function<unsigned int(unsigned int)>> fns =
        collect_adders(List<unsigned int>::cons(
            100u, List<unsigned int>::cons(200u, List<unsigned int>::nil())));
    unsigned int noise = ((55u + 44u) + 33u);
    return (apply_head(std::move(fns), 0u) + noise);
  }();
};

#endif // INCLUDED_FIX_FOLD_ESCAPE
