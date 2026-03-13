#ifndef INCLUDED_FUNCTOR_COMP
#define INCLUDED_FUNCTOR_COMP

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              t_A b = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return std::move(l0)->template fold_left<T1>(f, f(a0, b));
            }},
        this->v());
  }

  std::shared_ptr<List<t_A>> rev() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::ctor::Nil_();
                   },
                   [](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A x = _args.d_a0;
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return std::move(l_)->rev()->app(
                         List<t_A>::ctor::Cons_(x, List<t_A>::ctor::Nil_()));
                   }},
        this->v());
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A a = _args.d_a0;
                     std::shared_ptr<List<t_A>> l1 = _args.d_a1;
                     return List<t_A>::ctor::Cons_(a, std::move(l1)->app(m));
                   }},
        this->v());
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
    using t = std::shared_ptr<List<unsigned int>>;
    static inline const t empty = List<unsigned int>::ctor::Nil_();
    __attribute__((pure)) static t push(const unsigned int x,
                                        std::shared_ptr<List<unsigned int>> s);
    __attribute__((pure)) static std::optional<std::pair<unsigned int, t>>
    pop(const std::shared_ptr<List<unsigned int>> &s);
    __attribute__((pure)) static unsigned int size(const t _x0);
  };

  struct Queue {
    using t = std::pair<std::shared_ptr<List<unsigned int>>,
                        std::shared_ptr<List<unsigned int>>>;
    static inline const t empty = std::make_pair(
        List<unsigned int>::ctor::Nil_(), List<unsigned int>::ctor::Nil_());
    __attribute__((pure)) static t
    push(const unsigned int x,
         const std::pair<std::shared_ptr<List<unsigned int>>,
                         std::shared_ptr<List<unsigned int>>>
             q);
    __attribute__((pure)) static std::optional<std::pair<unsigned int, t>>
    pop(const std::pair<std::shared_ptr<List<unsigned int>>,
                        std::shared_ptr<List<unsigned int>>>
            q);
    __attribute__((pure)) static unsigned int
    size(const std::pair<std::shared_ptr<List<unsigned int>>,
                         std::shared_ptr<List<unsigned int>>>
             q);
  };

  template <CONTAINER C> struct ContainerOps {
    __attribute__((pure)) static typename C::t
    push_list(const std::shared_ptr<List<unsigned int>> &l,
              const typename C::t c) {
      return l->template fold_left<typename C::t>(
          [](typename C::t acc, unsigned int x) { return C::push(x, acc); }, c);
    }

    static std::shared_ptr<List<unsigned int>> to_list(const typename C::t c) {
      std::function<std::shared_ptr<List<unsigned int>>(
          unsigned int, std::shared_ptr<List<unsigned int>>, typename C::t)>
          go;
      go = [&](unsigned int fuel, std::shared_ptr<List<unsigned int>> acc,
               typename C::t c0) -> std::shared_ptr<List<unsigned int>> {
        if (fuel <= 0) {
          return std::move(acc)->rev();
        } else {
          unsigned int f = fuel - 1;
          if (C::pop(c0).has_value()) {
            std::pair<unsigned int, typename C::t> p = *C::pop(c0);
            unsigned int x = p.first;
            typename C::t c_ = p.second;
            return go(f, List<unsigned int>::ctor::Cons_(std::move(x), acc),
                      c_);
          } else {
            return acc->rev();
          }
        }
      };
      return go(C::size(c), List<unsigned int>::ctor::Nil_(), c);
    }
  };

  using StackOps = ContainerOps<Stack>;
  using QueueOps = ContainerOps<Queue>;
  static inline const std::shared_ptr<List<unsigned int>> test_stack =
      StackOps::to_list(StackOps::push_list(
          List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Cons_(
                              3u, List<unsigned int>::ctor::Nil_()))),
          Stack::empty));
  static inline const std::shared_ptr<List<unsigned int>> test_queue =
      QueueOps::to_list(QueueOps::push_list(
          List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Cons_(
                              3u, List<unsigned int>::ctor::Nil_()))),
          Queue::empty));
  static inline const unsigned int test_stack_size =
      Stack::size(StackOps::push_list(
          List<unsigned int>::ctor::Cons_(
              10u, List<unsigned int>::ctor::Cons_(
                       20u, List<unsigned int>::ctor::Cons_(
                                30u, List<unsigned int>::ctor::Nil_()))),
          Stack::empty));
  static inline const unsigned int test_queue_size =
      Queue::size(QueueOps::push_list(
          List<unsigned int>::ctor::Cons_(
              10u, List<unsigned int>::ctor::Cons_(
                       20u, List<unsigned int>::ctor::Cons_(
                                30u, List<unsigned int>::ctor::Nil_()))),
          Queue::empty));
};

#endif // INCLUDED_FUNCTOR_COMP
