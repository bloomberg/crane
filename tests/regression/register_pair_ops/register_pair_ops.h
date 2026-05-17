#ifndef INCLUDED_REGISTER_PAIR_OPS
#define INCLUDED_REGISTER_PAIR_OPS

#include <memory>
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return true;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (f(a0) && (*a1).forallb(f));
    }
  }
};

struct ListDef {
  static List<unsigned int> seq(unsigned int start, unsigned int len);
  template <typename T1>
  static T1 nth(unsigned int n, const List<T1> &l, T1 default0);
};

struct RegisterPairOps {
  template <typename T1>
  static List<T1> update_nth(unsigned int n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state {
    List<unsigned int> regs;

    // ACCESSORS
    state clone() const { return state{(*this).regs.clone()}; }
  };

  static unsigned int get_reg(const state &s, unsigned int r);
  static state set_reg(const state &s, unsigned int r, unsigned int v);
  static unsigned int get_reg_pair(const state &s, unsigned int r);
  static state set_reg_pair(const state &s, unsigned int r, unsigned int v);
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
  static unsigned int pair_base(unsigned int r);
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
  static unsigned int pair_index(unsigned int r);
  static bool pair_property(unsigned int r);
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
T1 ListDef::nth(unsigned int n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_REGISTER_PAIR_OPS
