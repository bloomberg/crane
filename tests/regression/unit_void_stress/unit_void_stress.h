#ifndef INCLUDED_UNIT_VOID_STRESS
#define INCLUDED_UNIT_VOID_STRESS

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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
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
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
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

struct UnitVoidStress {
  static void consume(const unsigned int &n);
  static void discard(const unsigned int &_x);
  __attribute__((pure)) static std::pair<unsigned int, std::monostate>
  pair_with_void_call(const unsigned int &n);
  __attribute__((pure)) static std::optional<std::monostate>
  some_void_call(const unsigned int &n);
  static inline const List<std::monostate> list_void_calls =
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
  static void id_void_call(const unsigned int &_x0);
  __attribute__((pure)) static std::pair<unsigned int, std::monostate>
  pair_with_discard(unsigned int n);
  static void store_and_call(const unsigned int &_x0);
  __attribute__((pure)) static std::pair<unsigned int, std::monostate>
  pair_via_let(const unsigned int &n);
  static void cond_void(const bool &b, const unsigned int &n);
  static void match_nat_void(const unsigned int &n);
  __attribute__((pure)) static std::pair<
      std::pair<unsigned int, std::monostate>, unsigned int>
  nested_pair_void(unsigned int n);
  __attribute__((
      pure)) static std::optional<std::pair<unsigned int, std::monostate>>
  option_pair_void(unsigned int n);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  let_void_then_pair(unsigned int n);
  __attribute__((pure)) static unsigned int
  seq_voids_value(const unsigned int &_x);
  __attribute__((pure)) static unsigned int void_in_one_branch(const bool &b,
                                                               unsigned int n);

  template <typename T1, MapsTo<void, T1> F0>
  __attribute__((pure)) static List<std::monostate>
  map_void(F0 &&f, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<std::monostate>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return List<std::monostate>::cons(
          [&]() {
            f(d_a0);
            return std::monostate{};
          }(),
          map_void<T1>(f, *(d_a1)));
    }
  }

  static inline const List<std::monostate> test_map_void =
      map_void<unsigned int>(
          discard,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())));

  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static std::optional<std::monostate>
  apply_void_to_option(F0 &&f, const unsigned int &n) {
    return std::make_optional<std::monostate>([=]() mutable {
      f(n);
      return std::monostate{};
    }());
  }

  static inline const std::optional<std::monostate> test_apply_void_option =
      apply_void_to_option(discard, 42u);
  static inline const std::optional<std::monostate> make_some_tt =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const List<std::monostate> make_unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static inline const std::pair<std::monostate, std::monostate> make_unit_pair =
      std::make_pair(std::monostate{}, std::monostate{});

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 apply_result(F0 &&f, unsigned int _x0) {
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
  apply_in_pair(F0 &&f, unsigned int n) {
    return std::make_pair(n, f(n));
  }

  static inline const std::pair<unsigned int, std::monostate>
      test_apply_in_pair_void = apply_in_pair<std::monostate>(
          [](const unsigned int &_wa0) {
            consume(_wa0);
            return std::monostate{};
          },
          5u);
  static void even_void(const unsigned int &n);
  static void odd_void(const unsigned int &n);
  static inline const std::monostate test_mutual_void = []() {
    even_void(10u);
    return std::monostate{};
  }();
  static void match_opt_void(const std::optional<unsigned int> &o);
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
