#ifndef INCLUDED_REGISTER_PAIR_OPS
#define INCLUDED_REGISTER_PAIR_OPS

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
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
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0> bool forallb(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return true;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (f(d_a0) && (*(d_a1)).forallb(f));
    }
  }
};

struct ListDef {
  static List<unsigned int> seq(unsigned int start, const unsigned int &len);
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct RegisterPairOps {
  template <typename T1>
  static List<T1> update_nth(const unsigned int &n, const T1 x,
                             const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *(d_a1));
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, *(d_a10)));
      }
    }
  }

  struct state {
    List<unsigned int> regs;

    // ACCESSORS
    state clone() const { return state{(*(this)).regs.clone()}; }
  };

  static unsigned int get_reg(const state &s, const unsigned int &r);
  static state set_reg(const state &s, const unsigned int &r,
                       const unsigned int &v);
  static unsigned int get_reg_pair(const state &s, const unsigned int &r);
  static state set_reg_pair(const state &s, const unsigned int &r,
                            const unsigned int &v);
  static inline const unsigned int test_get_reg_pair_even_value = get_reg_pair(
      state{List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          10u, List<unsigned int>::cons(
                                   11u, List<unsigned int>::nil()))))},
      2u);
  static inline const state sample_from_regs = state{List<unsigned int>::cons(
      0u, List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      10u,
                      List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   0u, List<unsigned int>::cons(
                                           0u, List<unsigned int>::nil()))))))};
  static inline const bool test_get_reg_pair_from_regs =
      get_reg_pair(sample_from_regs, 2u) == 171u;
  static inline const bool test_get_reg_pair_odd_normalizes =
      get_reg_pair(
          state{List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      1u, List<unsigned int>::cons(
                              10u, List<unsigned int>::cons(
                                       11u, List<unsigned int>::nil()))))},
          2u) ==
      get_reg_pair(
          state{List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      1u, List<unsigned int>::cons(
                              10u, List<unsigned int>::cons(
                                       11u, List<unsigned int>::nil()))))},
          3u);
  static inline const state sample_pair_high = state{List<unsigned int>::cons(
      2u,
      List<unsigned int>::cons(
          9u, List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  8u, List<unsigned int>::cons(
                                          1u, List<unsigned int>::nil()))))))};
  static inline const bool test_set_reg_affects_pair_high =
      get_reg_pair(set_reg(sample_pair_high, 2u, 13u), 2u) ==
      ((13u * 16u) + get_reg(sample_pair_high, 3u));
  static inline const state sample_pair_low = state{List<unsigned int>::cons(
      2u,
      List<unsigned int>::cons(
          9u, List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  8u, List<unsigned int>::cons(
                                          1u, List<unsigned int>::nil()))))))};
  static inline const bool test_set_reg_affects_pair_low =
      get_reg_pair(set_reg(sample_pair_low, 3u, 12u), 3u) ==
      ((get_reg(sample_pair_low, 2u) * 16u) + 12u);
  static inline const state sample_idempotent = state{List<unsigned int>::cons(
      0u,
      List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil()))))))};
  static inline const bool test_set_reg_pair_idempotent =
      get_reg_pair(
          set_reg_pair(set_reg_pair(sample_idempotent, 2u, 34u), 2u, 171u),
          2u) == 171u;
  static inline const state sample_preserves = state{List<unsigned int>::cons(
      1u,
      List<unsigned int>::cons(
          2u, List<unsigned int>::cons(
                  3u, List<unsigned int>::cons(
                          4u, List<unsigned int>::cons(
                                  5u, List<unsigned int>::cons(
                                          6u, List<unsigned int>::nil()))))))};
  static inline const bool test_set_reg_pair_preserves_other_pairs =
      get_reg_pair(set_reg_pair(sample_preserves, 0u, 171u), 2u) ==
      get_reg_pair(sample_preserves, 2u);
  static unsigned int pair_base(const unsigned int &r);
  static inline const state sample_register_pair =
      state{List<unsigned int>::cons(
          0u,
          List<unsigned int>::cons(
              0u,
              List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil()))))))};
  static inline const bool test_even_projection = pair_base(6u) == 6u;
  static inline const bool test_odd_projection = pair_base(7u) == 6u;
  static inline const bool test_set_pair_get_high =
      get_reg(set_reg_pair(sample_register_pair, 2u, 171u), 2u) == 10u;
  static inline const bool test_set_pair_get_low =
      get_reg(set_reg_pair(sample_register_pair, 2u, 171u), 3u) == 11u;
  static unsigned int pair_index(const unsigned int &r);
  static bool pair_property(const unsigned int &r);
  static inline const List<unsigned int> test_regs = ListDef::seq(0u, 16u);
  static inline const bool test_register_pair_architecture =
      test_regs.forallb(pair_property);
  static inline const state sample_even_rounding =
      state{List<unsigned int>::cons(
          0u,
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::cons(
                                          5u, List<unsigned int>::nil()))))))};
  static inline const unsigned int test_register_pair_even_rounding =
      get_reg_pair(set_reg_pair(sample_even_rounding, 3u, 45u), 3u);
  static inline const state sample_successor = state{List<unsigned int>::cons(
      0u, List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      10u,
                      List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   0u, List<unsigned int>::cons(
                                           0u, List<unsigned int>::nil()))))))};
  static inline const bool test_even_same_as_successor =
      get_reg_pair(sample_successor, 2u) == get_reg_pair(sample_successor, 3u);
  static inline const bool test_odd_same_as_predecessor =
      get_reg_pair(sample_successor, 3u) == get_reg_pair(sample_successor, 2u);
  static inline const bool test_reg_pair_successor =
      (test_even_same_as_successor && test_odd_same_as_predecessor);
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<
                                      std::pair<
                                          std::pair<
                                              std::pair<
                                                  std::pair<unsigned int, bool>,
                                                  bool>,
                                              bool>,
                                          bool>,
                                      bool>,
                                  bool>,
                              bool>,
                          bool>,
                      bool>,
                  bool>,
              bool>,
          unsigned int>,
      bool>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(
                                                  std::make_pair(
                                                      std::make_pair(
                                                          test_get_reg_pair_even_value,
                                                          test_get_reg_pair_from_regs),
                                                      test_get_reg_pair_odd_normalizes),
                                                  test_set_reg_affects_pair_high),
                                              test_set_reg_affects_pair_low),
                                          test_set_reg_pair_idempotent),
                                      test_set_reg_pair_preserves_other_pairs),
                                  test_even_projection),
                              test_odd_projection),
                          test_set_pair_get_high),
                      test_set_pair_get_low),
                  test_register_pair_architecture),
              test_register_pair_even_rounding),
          test_reg_pair_successor);
};

template <typename T1>
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_REGISTER_PAIR_OPS
