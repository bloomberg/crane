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
};

struct UnitVoidEdge {
  static void return_unit(unsigned int _x);
  static inline const unsigned int let_bind_void_call = []() {
    return_unit(5u);
    std::monostate x = std::monostate{};
    {
      return 42u;
    }
  }();
  static void count_down(unsigned int n);

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, unsigned int &>
  static void apply_unit_fn(F0 &&f, unsigned int _x0) {
    f(_x0);
    return;
  }

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, unsigned int &>
  static unsigned int map_to_unit(F0 &&, unsigned int) {
    return 42u;
  }

  template <typename T1> static T1 id(T1 x) { return x; }

  static inline const std::monostate id_unit = []() {
    id<std::monostate>(std::monostate{});
    return std::monostate{};
  }();
  static void id_unit_fn(unsigned int _x);
  static inline const unsigned int nested_lets = 42u;
  static inline const std::optional<std::monostate> unit_some =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const std::optional<std::monostate> unit_none =
      std::optional<std::monostate>();
  static unsigned int match_option_unit(const std::optional<std::monostate> &o);
  static std::optional<std::monostate> return_some_tt(unsigned int n);
  static void unit_chain(std::monostate u);
  static void helper_void(unsigned int _x);
  static unsigned int use_helper(unsigned int n);
  static unsigned int match_unit_nontail(std::monostate u);
  static void unit_to_unit_with_work(std::monostate u);
  static void seq_voids(unsigned int _x);
  static void conditional_unit(bool b);

  template <typename T1> static unsigned int poly_take(const T1 &) {
    return 42u;
  }

  static inline const unsigned int take_tt =
      poly_take<std::monostate>(std::monostate{});
  static inline const List<std::monostate> unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static unsigned int double_match_unit(std::monostate u1, std::monostate u2);

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, unsigned int &>
  static void apply_and_discard(F0 &&f, unsigned int _x0) {
    f(_x0);
    return;
  }

  static inline const std::monostate test_apply_discard = []() {
    apply_and_discard(return_unit, 42u);
    return std::monostate{};
  }();

  struct tagged_nat {
    unsigned int tn_value;
    std::monostate tn_tag;

    // ACCESSORS
    tagged_nat clone() const {
      return tagged_nat{(*this).tn_value, (*this).tn_tag};
    }
  };

  static tagged_nat make_tagged(unsigned int n);
  static unsigned int get_value(const tagged_nat &t);
  static inline const unsigned int test_record_unit = []() {
    tagged_nat t = make_tagged(99u);
    return get_value(std::move(t));
  }();
  static void make_callback(unsigned int n, std::monostate _x);
  static inline const std::monostate test_make_callback = []() {
    make_callback(5u, std::monostate{});
    return std::monostate{};
  }();

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<void, F0 &, unsigned int &> &&
             std::is_invocable_r_v<void, F1 &, bool &>
  static void multi_void_callbacks(F0 &&, F1 &&, unsigned int, bool) {
    return;
  }

  static void dummy_bool_void(bool _x);
  static inline const std::monostate test_multi_cb = []() {
    multi_void_callbacks(return_unit, dummy_bool_void, 7u, true);
    return std::monostate{};
  }();
  static inline const unsigned int test_let_bind = let_bind_void_call;
  static inline const std::monostate test_count_down = []() {
    count_down(10u);
    return std::monostate{};
  }();
  static inline const std::monostate test_apply = []() {
    apply_unit_fn(return_unit, 5u);
    return std::monostate{};
  }();
  static inline const unsigned int test_map = map_to_unit(return_unit, 5u);
  static inline const unsigned int test_nested = nested_lets;
  static inline const unsigned int test_match_some =
      match_option_unit(unit_some);
  static inline const unsigned int test_match_none =
      match_option_unit(unit_none);
  static inline const std::optional<std::monostate> test_return_some =
      return_some_tt(1u);
  static inline const unsigned int test_use_helper = use_helper(7u);
  static inline const unsigned int test_match_nontail =
      match_unit_nontail(std::monostate{});
  static inline const unsigned int test_double_match =
      double_match_unit(std::monostate{}, std::monostate{});
  static inline const unsigned int test_take_tt = take_tt;
};

#endif // INCLUDED_UNIT_VOID_EDGE
