#ifndef INCLUDED_UNIT_VOID_STRESS
#define INCLUDED_UNIT_VOID_STRESS

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
  explicit List(Nil _v) : d_v_(_v) {}

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

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct UnitVoidStress {
  static void consume(const unsigned int n);
  static void discard(const unsigned int _x);
  __attribute__((pure)) static std::pair<unsigned int, std::monostate>
  pair_with_void_call(const unsigned int n);
  __attribute__((pure)) static std::optional<std::monostate>
  some_void_call(const unsigned int n);
  static inline const std::shared_ptr<List<std::monostate>> list_void_calls =
      List<std::monostate>::cons(
          []() {
            consume(1u);
            return std::monostate{};
          }(),
          List<std::monostate>::cons(
              []() {
                consume(2u);
                return std::monostate{};
              }(),
              List<std::monostate>::nil()));
  static void id_void_call(const unsigned int _x0);
  __attribute__((pure)) static std::pair<unsigned int, std::monostate>
  pair_with_discard(const unsigned int n);
  static void store_and_call(const unsigned int _x0);
  __attribute__((pure)) static std::pair<unsigned int, std::monostate>
  pair_via_let(const unsigned int n);
  static void cond_void(const bool b, const unsigned int n);
  static void match_nat_void(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<unsigned int, std::monostate>, unsigned int>
  nested_pair_void(const unsigned int n);
  __attribute__((
      pure)) static std::optional<std::pair<unsigned int, std::monostate>>
  option_pair_void(const unsigned int n);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  let_void_then_pair(const unsigned int n);
  __attribute__((pure)) static unsigned int
  seq_voids_value(const unsigned int _x);
  __attribute__((pure)) static unsigned int
  void_in_one_branch(const bool b, const unsigned int n);

  template <typename T1, MapsTo<void, T1> F0>
  static std::shared_ptr<List<std::monostate>>
  map_void(F0 &&f, const std::shared_ptr<List<T1>> &l) {
    return std::visit(Overloaded{[](const typename List<T1>::Nil &)
                                     -> std::shared_ptr<List<std::monostate>> {
                                   return List<std::monostate>::nil();
                                 },
                                 [&](const typename List<T1>::Cons &_args)
                                     -> std::shared_ptr<List<std::monostate>> {
                                   return List<std::monostate>::cons(
                                       [&]() {
                                         f(_args.d_a0);
                                         return std::monostate{};
                                       }(),
                                       map_void<T1>(f, _args.d_a1));
                                 }},
                      l->v());
  }

  static inline const std::shared_ptr<List<std::monostate>> test_map_void =
      map_void<unsigned int>(
          discard,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())));

  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static std::optional<std::monostate>
  apply_void_to_option(F0 &&f, const unsigned int n) {
    return std::make_optional<std::monostate>([&]() {
      f(n);
      return std::monostate{};
    }());
  }

  static inline const std::optional<std::monostate> test_apply_void_option =
      apply_void_to_option(discard, 42u);
  static inline const std::optional<std::monostate> make_some_tt =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const std::shared_ptr<List<std::monostate>> make_unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static inline const std::pair<std::monostate, std::monostate> make_unit_pair =
      std::make_pair(std::monostate{}, std::monostate{});

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 apply_result(F0 &&f, const unsigned int _x0) {
    return f(_x0);
  }

  static inline const std::monostate test_apply_result_void = []() {
    apply_result<std::monostate>(
        [](const unsigned int &_wa0) {
          consume(_wa0);
          return std::monostate{};
        },
        5u);
    return std::monostate{};
  }();

  template <typename T1, MapsTo<T1, unsigned int> F0>
  __attribute__((pure)) static std::pair<unsigned int, T1>
  apply_in_pair(F0 &&f, const unsigned int n) {
    return std::make_pair(n, f(n));
  }

  static inline const std::pair<unsigned int, std::monostate>
      test_apply_in_pair_void = apply_in_pair<std::monostate>(
          [](const unsigned int &_wa0) {
            consume(_wa0);
            return std::monostate{};
          },
          5u);
  static void even_void(const unsigned int n);
  static void odd_void(const unsigned int n);
  static inline const std::monostate test_mutual_void = []() {
    even_void(10u);
    return std::monostate{};
  }();
  static void match_opt_void(const std::optional<unsigned int> o);
  static inline const std::monostate test_match_opt_void = []() {
    match_opt_void(std::make_optional<unsigned int>(3u));
    return std::monostate{};
  }();
  static inline const std::pair<unsigned int, std::monostate> test_pair_void =
      pair_with_void_call(5u);
  static inline const std::optional<std::monostate> test_some_void =
      some_void_call(3u);
  static inline const std::pair<unsigned int, unsigned int> test_let_void =
      let_void_then_pair(7u);
  static inline const unsigned int test_seq = seq_voids_value(10u);
  static inline const unsigned int test_branch = void_in_one_branch(true, 5u);
};

#endif // INCLUDED_UNIT_VOID_STRESS
