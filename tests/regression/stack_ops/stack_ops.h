#ifndef INCLUDED_STACK_OPS
#define INCLUDED_STACK_OPS

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

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct StackOps {
  struct state_basic {
    List<unsigned int> stack_basic;

    __attribute__((pure)) state_basic *operator->() { return this; }

    __attribute__((pure)) const state_basic *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state_basic clone() const {
      return state_basic{(*(this)).stack_basic};
    }
  };

  struct state_with_acc {
    List<unsigned int> stack_with_acc;
    unsigned int acc;

    __attribute__((pure)) state_with_acc *operator->() { return this; }

    __attribute__((pure)) const state_with_acc *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) state_with_acc clone() const {
      return state_with_acc{(*(this)).stack_with_acc, (*(this)).acc};
    }
  };

  __attribute__((
      pure)) static std::pair<std::optional<unsigned int>, state_basic>
  pop_stack(state_basic s);
  __attribute__((pure)) static bool
  is_none(const std::optional<unsigned int> &o);
  __attribute__((pure)) static unsigned int
  option_or_zero(const std::optional<unsigned int> &o);
  static inline const bool empty_is_none =
      is_none(pop_stack(state_basic{List<unsigned int>::nil()}).first);
  static inline const unsigned int some_addr = option_or_zero(
      pop_stack(
          state_basic{List<unsigned int>::cons(
              9u, List<unsigned int>::cons(8u, List<unsigned int>::nil()))})
          .first);
  __attribute__((
      pure)) static std::pair<std::optional<unsigned int>, state_with_acc>
  pop_stack_acc(state_with_acc s);
  static inline const unsigned int pop_acc_test = []() -> unsigned int {
    auto _cs = pop_stack_acc(state_with_acc{
        List<unsigned int>::cons(
            9u, List<unsigned int>::cons(8u, List<unsigned int>::nil())),
        3u});
    const std::optional<unsigned int> &o = _cs.first;
    const state_with_acc &s_ = _cs.second;
    if (o.has_value()) {
      const unsigned int &a = *o;
      return ((a + s_.stack_with_acc.length()) + s_.acc);
    } else {
      return s_.acc;
    }
  }();
  __attribute__((pure)) static state_basic push_stack(const state_basic &s,
                                                      unsigned int addr);
  __attribute__((pure)) static unsigned int top_or_zero(const state_basic &s);
  static inline const unsigned int empty_len =
      push_stack(state_basic{List<unsigned int>::nil()}, 12u)
          .stack_basic.length();
  static inline const unsigned int overflow_head = top_or_zero(push_stack(
      state_basic{List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())))},
      9u));
  static inline const unsigned int overflow_len =
      push_stack(state_basic{List<unsigned int>::cons(
                     1u, List<unsigned int>::cons(
                             2u, List<unsigned int>::cons(
                                     3u, List<unsigned int>::nil())))},
                 9u)
          .stack_basic.length();
  __attribute__((pure)) static state_basic push_stack_cap(const state_basic &s,
                                                          unsigned int addr);
  static inline const unsigned int push_cap_test =
      push_stack_cap(
          state_basic{List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       20u, List<unsigned int>::cons(
                                30u, List<unsigned int>::cons(
                                         40u, List<unsigned int>::nil()))))},
          7u)
          .stack_basic.length();
  static inline const std::pair<
      std::pair<std::pair<std::pair<unsigned int, bool>, unsigned int>,
                std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(std::make_pair(some_addr, empty_is_none),
                             pop_acc_test),
              std::make_pair(std::make_pair(empty_len, overflow_head),
                             overflow_len)),
          push_cap_test);
};

#endif // INCLUDED_STACK_OPS
