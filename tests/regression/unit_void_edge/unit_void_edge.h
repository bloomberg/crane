#ifndef INCLUDED_UNIT_VOID_EDGE
#define INCLUDED_UNIT_VOID_EDGE

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
    std::unique_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
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
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
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

struct UnitVoidEdge {
  static void return_unit(uint64_t _x);
  static inline const uint64_t let_bind_void_call = []() {
    return_unit(UINT64_C(5));
    std::monostate x = std::monostate{};
    {
      return UINT64_C(42);
    }
  }();
  static void count_down(uint64_t n);

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_unit_fn(F0 &&f, uint64_t _x0) {
    f(_x0);
    return;
  }

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static uint64_t map_to_unit(F0 &&, uint64_t) {
    return UINT64_C(42);
  }

  template <typename T1> static T1 id(T1 x) { return x; }

  static inline const std::monostate id_unit = []() {
    id<std::monostate>(std::monostate{});
    return std::monostate{};
  }();
  static void id_unit_fn(uint64_t _x);
  static inline const uint64_t nested_lets = UINT64_C(42);
  static inline const std::optional<std::monostate> unit_some =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const std::optional<std::monostate> unit_none =
      std::optional<std::monostate>();
  static uint64_t match_option_unit(const std::optional<std::monostate> &o);
  static std::optional<std::monostate> return_some_tt(uint64_t n);
  static void unit_chain(std::monostate u);
  static void helper_void(uint64_t _x);
  static uint64_t use_helper(uint64_t n);
  static uint64_t match_unit_nontail(std::monostate u);
  static void unit_to_unit_with_work(std::monostate u);
  static void seq_voids(uint64_t _x);
  static void conditional_unit(bool b);

  template <typename T1> static uint64_t poly_take(const T1 &) {
    return UINT64_C(42);
  }

  static inline const uint64_t take_tt =
      poly_take<std::monostate>(std::monostate{});
  static inline const List<std::monostate> unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static uint64_t double_match_unit(std::monostate u1, std::monostate u2);

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_and_discard(F0 &&f, uint64_t _x0) {
    f(_x0);
    return;
  }

  static inline const std::monostate test_apply_discard = []() {
    apply_and_discard(return_unit, UINT64_C(42));
    return std::monostate{};
  }();

  struct tagged_nat {
    uint64_t tn_value;
    std::monostate tn_tag;

    // ACCESSORS
    tagged_nat clone() const {
      return tagged_nat{this->tn_value, this->tn_tag};
    }
  };

  static tagged_nat make_tagged(uint64_t n);
  static uint64_t get_value(const tagged_nat &t);
  static inline const uint64_t test_record_unit = []() {
    tagged_nat t = make_tagged(UINT64_C(99));
    return get_value(std::move(t));
  }();
  static void make_callback(uint64_t n, std::monostate _x);
  static inline const std::monostate test_make_callback = []() {
    make_callback(UINT64_C(5), std::monostate{});
    return std::monostate{};
  }();

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &> &&
             std::is_invocable_r_v<void, F1 &, bool &>
  static void multi_void_callbacks(F0 &&, F1 &&, uint64_t, bool) {
    return;
  }

  static void dummy_bool_void(bool _x);
  static inline const std::monostate test_multi_cb = []() {
    multi_void_callbacks(return_unit, dummy_bool_void, UINT64_C(7), true);
    return std::monostate{};
  }();
  static inline const uint64_t test_let_bind = let_bind_void_call;
  static inline const std::monostate test_count_down = []() {
    count_down(UINT64_C(10));
    return std::monostate{};
  }();
  static inline const std::monostate test_apply = []() {
    apply_unit_fn(return_unit, UINT64_C(5));
    return std::monostate{};
  }();
  static inline const uint64_t test_map = map_to_unit(return_unit, UINT64_C(5));
  static inline const uint64_t test_nested = nested_lets;
  static inline const uint64_t test_match_some = match_option_unit(unit_some);
  static inline const uint64_t test_match_none = match_option_unit(unit_none);
  static inline const std::optional<std::monostate> test_return_some =
      return_some_tt(UINT64_C(1));
  static inline const uint64_t test_use_helper = use_helper(UINT64_C(7));
  static inline const uint64_t test_match_nontail =
      match_unit_nontail(std::monostate{});
  static inline const uint64_t test_double_match =
      double_match_unit(std::monostate{}, std::monostate{});
  static inline const uint64_t test_take_tt = take_tt;
};

#endif // INCLUDED_UNIT_VOID_EDGE
