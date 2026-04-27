#ifndef INCLUDED_FUNCTOR_COMP
#define INCLUDED_FUNCTOR_COMP

#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }

  __attribute__((pure)) List<t_A> rev() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).rev().app(List<t_A>::cons(d_a0, List<t_A>::nil()));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

template <typename M>
concept CONTAINER = requires {
  typename M::t;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::t>;
      });
  {
    M::push(std::declval<unsigned int>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::pop(std::declval<typename M::t>())
  } -> std::same_as<std::optional<std::pair<unsigned int, typename M::t>>>;
  { M::size(std::declval<typename M::t>()) } -> std::same_as<unsigned int>;
};

struct FunctorComp {
  struct Stack {
    using t = List<unsigned int>;
    static inline const t empty = List<unsigned int>::nil();
    __attribute__((pure)) static t push(unsigned int x, List<unsigned int> s);
    __attribute__((pure)) static std::optional<std::pair<unsigned int, t>>
    pop(const List<unsigned int> &s);
    __attribute__((pure)) static unsigned int size(const t _x0);
  };

  struct Queue {
    using t = std::pair<List<unsigned int>, List<unsigned int>>;
    static inline const t empty =
        std::make_pair(List<unsigned int>::nil(), List<unsigned int>::nil());
    __attribute__((pure)) static t
    push(unsigned int x,
         const std::pair<List<unsigned int>, List<unsigned int>> &q);
    __attribute__((pure)) static std::optional<std::pair<unsigned int, t>>
    pop(const std::pair<List<unsigned int>, List<unsigned int>> &q);
    __attribute__((pure)) static unsigned int
    size(const std::pair<List<unsigned int>, List<unsigned int>> &q);
  };

  template <CONTAINER C> struct ContainerOps {
    __attribute__((pure)) static typename C::t
    push_list(const List<unsigned int> &l, const typename C::t c) {
      return l.template fold_left<typename C::t>(
          [](const typename C::t acc, const unsigned int &x) {
            return C::push(x, acc);
          },
          c);
    }

    __attribute__((pure)) static List<unsigned int>
    to_list(const typename C::t c) {
      std::function<List<unsigned int>(unsigned int, List<unsigned int>,
                                       typename C::t)>
          go;
      go = [&](unsigned int fuel, List<unsigned int> acc,
               typename C::t c0) -> List<unsigned int> {
        if (fuel <= 0) {
          return acc.rev();
        } else {
          unsigned int f = fuel - 1;
          auto _cs = C::pop(c0);
          if (_cs.has_value()) {
            const std::pair<unsigned int, typename C::t> &p = *_cs;
            const unsigned int &x = p.first;
            const typename C::t &c_ = p.second;
            return go(f, List<unsigned int>::cons(x, acc), c_);
          } else {
            return acc.rev();
          }
        }
      };
      return go(C::size(c), List<unsigned int>::nil(), c);
    }
  };

  using StackOps = ContainerOps<Stack>;
  using QueueOps = ContainerOps<Queue>;
  static inline const List<unsigned int> test_stack =
      StackOps::to_list(StackOps::push_list(
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          Stack::empty));
  static inline const List<unsigned int> test_queue =
      QueueOps::to_list(QueueOps::push_list(
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          Queue::empty));
  static inline const unsigned int test_stack_size =
      Stack::size(StackOps::push_list(
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       20u, List<unsigned int>::cons(
                                30u, List<unsigned int>::nil()))),
          Stack::empty));
  static inline const unsigned int test_queue_size =
      Queue::size(QueueOps::push_list(
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       20u, List<unsigned int>::cons(
                                30u, List<unsigned int>::nil()))),
          Queue::empty));
};

#endif // INCLUDED_FUNCTOR_COMP
