#ifndef INCLUDED_UNIT_VOID_STRESS
#define INCLUDED_UNIT_VOID_STRESS

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
    A a;
    std::shared_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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
};

struct UnitVoidStress {
  static void consume(uint64_t n);
  static void discard(uint64_t _x);
  static std::pair<uint64_t, std::monostate> pair_with_void_call(uint64_t n);
  static std::optional<std::monostate> some_void_call(uint64_t n);
  static inline const List<std::monostate> list_void_calls =
      List<std::monostate>::cons(
          []() {
            consume(UINT64_C(1));
            return std::monostate{};
          }(),
          List<std::monostate>::cons(
              []() {
                consume(UINT64_C(2));
                return std::monostate{};
              }(),
              List<std::monostate>::nil()));
  static void id_void_call(uint64_t _x0);
  static std::pair<uint64_t, std::monostate> pair_with_discard(uint64_t n);
  static void store_and_call(uint64_t _x0);
  static std::pair<uint64_t, std::monostate> pair_via_let(uint64_t n);
  static void cond_void(bool b, uint64_t n);
  static void match_nat_void(uint64_t n);
  static std::pair<std::pair<uint64_t, std::monostate>, uint64_t>
  nested_pair_void(uint64_t n);
  static std::optional<std::pair<uint64_t, std::monostate>>
  option_pair_void(uint64_t n);
  static std::pair<uint64_t, uint64_t> let_void_then_pair(uint64_t n);
  static uint64_t seq_voids_value(uint64_t _x);
  static uint64_t void_in_one_branch(bool b, uint64_t n);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<void, F0 &, T1 &>
  static List<std::monostate> map_void(F0 &&f, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<std::monostate>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return List<std::monostate>::cons(
          [&]() {
            f(a0);
            return std::monostate{};
          }(),
          map_void<T1>(f, *a1));
    }
  }

  static inline const List<std::monostate> test_map_void = map_void<uint64_t>(
      discard, List<uint64_t>::cons(
                   UINT64_C(1),
                   List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())));

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static std::optional<std::monostate> apply_void_to_option(F0 &&f,
                                                            uint64_t n) {
    return std::make_optional<std::monostate>([=]() mutable {
      f(n);
      return std::monostate{};
    }());
  }

  static inline const std::optional<std::monostate> test_apply_void_option =
      apply_void_to_option(discard, UINT64_C(42));
  static inline const std::optional<std::monostate> make_some_tt =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const List<std::monostate> make_unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static inline const std::pair<std::monostate, std::monostate> make_unit_pair =
      std::make_pair(std::monostate{}, std::monostate{});

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 apply_result(F0 &&f, uint64_t _x0) {
    return f(_x0);
  }

  static inline const std::monostate test_apply_result_void = []() {
    apply_result<std::monostate>(
        [](const uint64_t &_wa0) {
          consume(_wa0);
          return std::monostate{};
        },
        UINT64_C(5));
    return std::monostate{};
  }();

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static std::pair<uint64_t, T1> apply_in_pair(F0 &&f, uint64_t n) {
    return std::make_pair(n, f(n));
  }

  static inline const std::pair<uint64_t, std::monostate>
      test_apply_in_pair_void = apply_in_pair<std::monostate>(
          [](const uint64_t &_wa0) {
            consume(_wa0);
            return std::monostate{};
          },
          UINT64_C(5));
  static void even_void(uint64_t n);
  static void odd_void(uint64_t n);
  static inline const std::monostate test_mutual_void = []() {
    even_void(UINT64_C(10));
    return std::monostate{};
  }();
  static void match_opt_void(const std::optional<uint64_t> &o);
  static inline const std::monostate test_match_opt_void = []() {
    match_opt_void(std::make_optional<uint64_t>(UINT64_C(3)));
    return std::monostate{};
  }();
  static inline const std::pair<uint64_t, std::monostate> test_pair_void =
      pair_with_void_call(UINT64_C(5));
  static inline const std::optional<std::monostate> test_some_void =
      some_void_call(UINT64_C(3));
  static inline const std::pair<uint64_t, uint64_t> test_let_void =
      let_void_then_pair(UINT64_C(7));
  static inline const uint64_t test_seq = seq_voids_value(UINT64_C(10));
  static inline const uint64_t test_branch =
      void_in_one_branch(true, UINT64_C(5));
};

#endif // INCLUDED_UNIT_VOID_STRESS
