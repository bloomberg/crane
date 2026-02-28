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

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<List::list<A>> nil_uptr() {
        return std::unique_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::unique_ptr<List::list<A>>
      cons_uptr(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::unique_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    std::shared_ptr<List::list<A>> rev() const {
      return std::visit(Overloaded{[](const typename List::list<A>::nil _args)
                                       -> std::shared_ptr<List::list<A>> {
                                     return List::list<A>::ctor::nil_();
                                   },
                                   [](const typename List::list<A>::cons _args)
                                       -> std::shared_ptr<List::list<A>> {
                                     A x = _args._a0;
                                     std::shared_ptr<List::list<A>> l_ =
                                         _args._a1;
                                     return std::move(l_)->rev()->app(
                                         List::list<A>::ctor::cons_(
                                             x, List::list<A>::ctor::nil_()));
                                   }},
                        this->v());
    }
    unsigned int length() const {
      return std::visit(
          Overloaded{
              [](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (std::move(l_)->length() + 1);
              }},
          this->v());
    }
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a,
                                                         std::move(l1)->app(m));
                     }},
          this->v());
    }
  };
  template <typename T1, typename T2, MapsTo<T1, T1, T2> F0>
  static T1 fold_left(F0 &&f, const std::shared_ptr<List::list<T2>> &l,
                      const T1 a0);
};

struct FunctorComp {
  template <typename M>
  concept CONTAINER = requires {
    typename M::t;
    requires std::same_as<std::remove_cvref_t<decltype(M::empty)>,
                          typename M::t>;
    {
      M::push(std::declval<unsigned int>(), std::declval<typename M::t>())
    } -> std::same_as<typename M::t>;
    {
      M::pop(std::declval<typename M::t>())
    } -> std::same_as<std::optional<std::pair<unsigned int, typename M::t>>>;
    { M::size(std::declval<typename M::t>()) } -> std::same_as<unsigned int>;
  };

  struct Stack {
    using t = std::shared_ptr<List::list<unsigned int>>;

    static inline const t empty = List::list<unsigned int>::ctor::nil_();

    static t push(const unsigned int x,
                  std::shared_ptr<List::list<unsigned int>> s);

    static std::optional<std::pair<unsigned int, t>>
    pop(const std::shared_ptr<List::list<unsigned int>> &s);

    static unsigned int size(const t);
  };

  struct Queue {
    using t = std::pair<std::shared_ptr<List::list<unsigned int>>,
                        std::shared_ptr<List::list<unsigned int>>>;

    static inline const t empty =
        std::make_pair(List::list<unsigned int>::ctor::nil_(),
                       List::list<unsigned int>::ctor::nil_());

    static t push(const unsigned int x,
                  const std::pair<std::shared_ptr<List::list<unsigned int>>,
                                  std::shared_ptr<List::list<unsigned int>>>
                      q);

    static std::optional<std::pair<unsigned int, t>>
    pop(const std::pair<std::shared_ptr<List::list<unsigned int>>,
                        std::shared_ptr<List::list<unsigned int>>>
            q);

    static unsigned int
    size(const std::pair<std::shared_ptr<List::list<unsigned int>>,
                         std::shared_ptr<List::list<unsigned int>>>
             q);
  };

  template <CONTAINER C> struct ContainerOps {
    static typename C::t
    push_list(const std::shared_ptr<List::list<unsigned int>> &l,
              const typename C::t c) {
      return List::fold_left<typename C::t, unsigned int>(
          [](typename C::t acc, unsigned int x) { return C::push(x, acc); }, l,
          c);
    }

    static std::shared_ptr<List::list<unsigned int>>
    to_list(const typename C::t c) {
      std::function<std::shared_ptr<List::list<unsigned int>>(
          unsigned int, std::shared_ptr<List::list<unsigned int>>,
          typename C::t)>
          go;
      go = [&](unsigned int fuel, std::shared_ptr<List::list<unsigned int>> acc,
               typename C::t c0) -> std::shared_ptr<List::list<unsigned int>> {
        if (fuel <= 0) {
          return std::move(acc)->rev();
        } else {
          unsigned int f = fuel - 1;
          if (C::pop(c0).has_value()) {
            std::pair<unsigned int, typename C::t> p = *C::pop(c0);
            unsigned int x = p.first;
            typename C::t c_ = p.second;
            return go(f,
                      List::list<unsigned int>::ctor::cons_(std::move(x), acc),
                      c_);
          } else {
            return acc->rev();
          }
        }
      };
      return go(C::size(c), List::list<unsigned int>::ctor::nil_(), c);
    }
  };

  using StackOps = ContainerOps<Stack>;

  using QueueOps = ContainerOps<Queue>;

  static inline const std::shared_ptr<List::list<unsigned int>> test_stack =
      StackOps::to_list(StackOps::push_list(
          List::list<unsigned int>::ctor::cons_(
              (0 + 1),
              List::list<unsigned int>::ctor::cons_(
                  ((0 + 1) + 1), List::list<unsigned int>::ctor::cons_(
                                     (((0 + 1) + 1) + 1),
                                     List::list<unsigned int>::ctor::nil_()))),
          Stack::empty));

  static inline const std::shared_ptr<List::list<unsigned int>> test_queue =
      QueueOps::to_list(QueueOps::push_list(
          List::list<unsigned int>::ctor::cons_(
              (0 + 1),
              List::list<unsigned int>::ctor::cons_(
                  ((0 + 1) + 1), List::list<unsigned int>::ctor::cons_(
                                     (((0 + 1) + 1) + 1),
                                     List::list<unsigned int>::ctor::nil_()))),
          Queue::empty));

  static inline const unsigned int test_stack_size =
      Stack::size(StackOps::push_list(
          List::list<unsigned int>::ctor::cons_(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List::list<unsigned int>::ctor::cons_(
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
                  List::list<unsigned int>::ctor::cons_(
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
                      List::list<unsigned int>::ctor::nil_()))),
          Stack::empty));

  static inline const unsigned int test_queue_size =
      Queue::size(QueueOps::push_list(
          List::list<unsigned int>::ctor::cons_(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List::list<unsigned int>::ctor::cons_(
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
                  List::list<unsigned int>::ctor::cons_(
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
                      List::list<unsigned int>::ctor::nil_()))),
          Queue::empty));
};

template <typename T1, typename T2, MapsTo<T1, T1, T2> F0>
T1 List::fold_left(F0 &&f, const std::shared_ptr<List::list<T2>> &l,
                   const T1 a0) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<T2>::nil _args) -> T1 { return a0; },
          [&](const typename List::list<T2>::cons _args) -> T1 {
            T2 b = _args._a0;
            std::shared_ptr<List::list<T2>> l0 = _args._a1;
            return List::fold_left<T1, T2>(f, std::move(l0), f(a0, b));
          }},
      l->v());
}
