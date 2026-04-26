#ifndef INCLUDED_UNIT_VOID_EDGE
#define INCLUDED_UNIT_VOID_EDGE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
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
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
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

struct UnitVoidEdge {
  static void return_unit(const unsigned int &_x);
  static inline const unsigned int let_bind_void_call = []() {
    return_unit(5u);
    std::monostate x = std::monostate{};
    {
      return 42u;
    }
  }();
  static void count_down(const unsigned int &n);

  template <MapsTo<void, unsigned int> F0>
  static void apply_unit_fn(F0 &&f, unsigned int _x0) {
    f(_x0);
    return;
  }

  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static unsigned int map_to_unit(F0 &&,
                                                        const unsigned int &) {
    return 42u;
  }

  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const std::monostate id_unit = []() {
    id<std::monostate>(std::monostate{});
    return std::monostate{};
  }();
  static void id_unit_fn(const unsigned int &_x);
  static inline const unsigned int nested_lets = 42u;
  static inline const std::optional<std::monostate> unit_some =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const std::optional<std::monostate> unit_none =
      std::optional<std::monostate>();
  __attribute__((pure)) static unsigned int
  match_option_unit(const std::optional<std::monostate> &o);
  __attribute__((pure)) static std::optional<std::monostate>
  return_some_tt(const unsigned int &n);
  static void unit_chain(std::monostate u);
  static void helper_void(const unsigned int &_x);
  __attribute__((pure)) static unsigned int use_helper(unsigned int n);
  __attribute__((pure)) static unsigned int
  match_unit_nontail(const std::monostate &u);
  static void unit_to_unit_with_work(const std::monostate &u);
  static void seq_voids(const unsigned int &_x);
  static void conditional_unit(const bool &b);

  template <typename T1>
  __attribute__((pure)) static unsigned int poly_take(const T1) {
    return 42u;
  }

  static inline const unsigned int take_tt =
      poly_take<std::monostate>(std::monostate{});
  static inline const List<std::monostate> unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  __attribute__((pure)) static unsigned int
  double_match_unit(const std::monostate &u1, const std::monostate &u2);

  template <MapsTo<void, unsigned int> F0>
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

    __attribute__((pure)) tagged_nat *operator->() { return this; }

    __attribute__((pure)) const tagged_nat *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) tagged_nat clone() const {
      return tagged_nat{(*(this)).tn_value, (*(this)).tn_tag};
    }
  };

  __attribute__((pure)) static tagged_nat make_tagged(unsigned int n);
  __attribute__((pure)) static unsigned int get_value(const tagged_nat &t);
  static inline const unsigned int test_record_unit = []() {
    tagged_nat t = make_tagged(99u);
    return get_value(t);
  }();
  static void make_callback(const unsigned int &n, const std::monostate &_x);
  static inline const std::monostate test_make_callback = []() {
    make_callback(5u, std::monostate{});
    return std::monostate{};
  }();

  template <MapsTo<void, unsigned int> F0, MapsTo<void, bool> F1>
  static void multi_void_callbacks(F0 &&, F1 &&, const unsigned int &,
                                   const bool &) {
    return;
  }

  static void dummy_bool_void(const bool &_x);
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
