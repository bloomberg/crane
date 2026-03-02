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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  std::shared_ptr<List<A>> rev() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<A>> {
              return List<A>::ctor::nil_();
            },
            [](const typename List<A>::cons _args) -> std::shared_ptr<List<A>> {
              A x = _args._a0;
              std::shared_ptr<List<A>> l_ = _args._a1;
              return std::move(l_)->rev()->app(
                  List<A>::ctor::cons_(x, List<A>::ctor::nil_()));
            }},
        this->v());
  }
  template <typename T1, MapsTo<T1, T1, A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{[&](const typename List<A>::nil _args) -> T1 { return a0; },
                   [&](const typename List<A>::cons _args) -> T1 {
                     A b = _args._a0;
                     std::shared_ptr<List<A>> l0 = _args._a1;
                     return std::move(l0)->template fold_left<T1>(f, f(a0, b));
                   }},
        this->v());
  }
  unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> unsigned int { return 0; },
            [](const typename List<A>::cons _args) -> unsigned int {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return (std::move(l_)->length() + 1);
            }},
        this->v());
  }
  std::shared_ptr<List<A>> app(const std::shared_ptr<List<A>> &m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
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

    static inline const t empty = List<unsigned int>::ctor::nil_();

    static t push(const unsigned int x, std::shared_ptr<List<unsigned int>> s);

    static std::optional<std::pair<unsigned int, t>>
    pop(const std::shared_ptr<List<unsigned int>> &s);

    static unsigned int size(const t);
  };

  struct Queue {
    using t = std::pair<std::shared_ptr<List<unsigned int>>,
                        std::shared_ptr<List<unsigned int>>>;

    static inline const t empty = std::make_pair(
        List<unsigned int>::ctor::nil_(), List<unsigned int>::ctor::nil_());

    static t push(const unsigned int x,
                  const std::pair<std::shared_ptr<List<unsigned int>>,
                                  std::shared_ptr<List<unsigned int>>>
                      q);

    static std::optional<std::pair<unsigned int, t>>
    pop(const std::pair<std::shared_ptr<List<unsigned int>>,
                        std::shared_ptr<List<unsigned int>>>
            q);

    static unsigned int
    size(const std::pair<std::shared_ptr<List<unsigned int>>,
                         std::shared_ptr<List<unsigned int>>>
             q);
  };

  template <CONTAINER C> struct ContainerOps {
    static typename C::t push_list(const std::shared_ptr<List<unsigned int>> &l,
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
            return go(f, List<unsigned int>::ctor::cons_(std::move(x), acc),
                      c_);
          } else {
            return acc->rev();
          }
        }
      };
      return go(C::size(c), List<unsigned int>::ctor::nil_(), c);
    }
  };

  using StackOps = ContainerOps<Stack>;

  using QueueOps = ContainerOps<Queue>;

  static inline const std::shared_ptr<List<unsigned int>> test_stack =
      StackOps::to_list(StackOps::push_list(
          List<unsigned int>::ctor::cons_(
              (0 + 1),
              List<unsigned int>::ctor::cons_(
                  ((0 + 1) + 1),
                  List<unsigned int>::ctor::cons_(
                      (((0 + 1) + 1) + 1), List<unsigned int>::ctor::nil_()))),
          Stack::empty));

  static inline const std::shared_ptr<List<unsigned int>> test_queue =
      QueueOps::to_list(QueueOps::push_list(
          List<unsigned int>::ctor::cons_(
              (0 + 1),
              List<unsigned int>::ctor::cons_(
                  ((0 + 1) + 1),
                  List<unsigned int>::ctor::cons_(
                      (((0 + 1) + 1) + 1), List<unsigned int>::ctor::nil_()))),
          Queue::empty));

  static inline const unsigned int test_stack_size =
      Stack::size(StackOps::push_list(
          List<unsigned int>::ctor::cons_(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1),
                  List<unsigned int>::ctor::cons_(
                      ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                               1) +
                                              1) +
                                             1) +
                                            1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1),
                      List<unsigned int>::ctor::nil_()))),
          Stack::empty));

  static inline const unsigned int test_queue_size =
      Queue::size(QueueOps::push_list(
          List<unsigned int>::ctor::cons_(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1),
                  List<unsigned int>::ctor::cons_(
                      ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                               1) +
                                              1) +
                                             1) +
                                            1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1),
                      List<unsigned int>::ctor::nil_()))),
          Queue::empty));
};
