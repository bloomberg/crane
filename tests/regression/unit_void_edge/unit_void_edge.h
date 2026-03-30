#ifndef INCLUDED_UNIT_VOID_EDGE
#define INCLUDED_UNIT_VOID_EDGE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct UnitVoidEdge {
  static void return_unit(const unsigned int _x);
  static inline const unsigned int let_bind_void_call = []() {
    return_unit(5u);
    std::monostate x = std::monostate{};
    {
      return 42u;
    }
  }();
  static void count_down(const unsigned int n);

  template <MapsTo<void, unsigned int> F0>
  static void apply_unit_fn(F0 &&f, const unsigned int _x0) {
    {
      f(std::move(_x0));
      return;
    }
  }

  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  map_to_unit(F0 &&_x, const unsigned int _x0) {
    return 42u;
  }

  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const std::monostate id_unit = []() {
    id<std::monostate>(std::monostate{});
    return std::monostate{};
  }();
  static void id_unit_fn(const unsigned int _x);
  static inline const unsigned int nested_lets = 42u;
  static inline const std::optional<std::monostate> unit_some =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const std::optional<std::monostate> unit_none =
      std::optional<std::monostate>();
  __attribute__((pure)) static unsigned int
  match_option_unit(const std::optional<std::monostate> o);
  __attribute__((pure)) static std::optional<std::monostate>
  return_some_tt(const unsigned int n);
  static void unit_chain(const std::monostate u);
  static void helper_void(const unsigned int _x);
  __attribute__((pure)) static unsigned int use_helper(const unsigned int n);
  __attribute__((pure)) static unsigned int
  match_unit_nontail(const std::monostate u);
  static void unit_to_unit_with_work(const std::monostate u);
  static void seq_voids(const unsigned int _x);
  static void conditional_unit(const bool b);

  template <typename T1>
  __attribute__((pure)) static unsigned int poly_take(const T1 _x) {
    return 42u;
  }

  static inline const unsigned int take_tt =
      poly_take<std::monostate>(std::monostate{});
  static inline const std::shared_ptr<List<std::monostate>> unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  __attribute__((pure)) static unsigned int
  double_match_unit(const std::monostate u1, const std::monostate u2);

  template <MapsTo<void, unsigned int> F0>
  static void apply_and_discard(F0 &&f, const unsigned int _x0) {
    {
      f(std::move(_x0));
      return;
    }
  }

  static inline const std::monostate test_apply_discard = []() {
    apply_and_discard(return_unit, 42u);
    return std::monostate{};
  }();

  struct tagged_nat {
    unsigned int tn_value;
    std::monostate tn_tag;
  };

  static std::shared_ptr<tagged_nat> make_tagged(const unsigned int n);
  __attribute__((pure)) static unsigned int
  get_value(const std::shared_ptr<tagged_nat> &t);
  static inline const unsigned int test_record_unit = []() {
    std::shared_ptr<tagged_nat> t = make_tagged(99u);
    return get_value(std::move(t));
  }();
  static void make_callback(const unsigned int n, const std::monostate _x);
  static inline const std::monostate test_make_callback = []() {
    make_callback(5u, std::monostate{});
    return std::monostate{};
  }();

  template <MapsTo<void, unsigned int> F0, MapsTo<void, bool> F1>
  static void multi_void_callbacks(F0 &&_x, F1 &&_x0, const unsigned int _x1,
                                   const bool _x2) {
    return;
  }

  static void dummy_bool_void(const bool _x);
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
