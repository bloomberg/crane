#ifndef INCLUDED_STACK_OPS
#define INCLUDED_STACK_OPS

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
};

struct StackOps {
  struct state_basic {
    std::shared_ptr<List<unsigned int>> stack_basic;
  };

  struct state_with_acc {
    std::shared_ptr<List<unsigned int>> stack_with_acc;
    unsigned int acc;
  };

  __attribute__((pure)) static std::pair<std::optional<unsigned int>,
                                         std::shared_ptr<state_basic>>
  pop_stack(std::shared_ptr<state_basic> s);
  __attribute__((pure)) static bool
  is_none(const std::optional<unsigned int> o);
  __attribute__((pure)) static unsigned int
  option_or_zero(const std::optional<unsigned int> o);
  static inline const bool empty_is_none =
      is_none(pop_stack(std::make_shared<state_basic>(
                            state_basic{List<unsigned int>::ctor::Nil_()}))
                  .first);
  static inline const unsigned int some_addr = option_or_zero(
      pop_stack(std::make_shared<state_basic>(
                    state_basic{List<unsigned int>::ctor::Cons_(
                        9u, List<unsigned int>::ctor::Cons_(
                                8u, List<unsigned int>::ctor::Nil_()))}))
          .first);
  __attribute__((pure)) static std::pair<std::optional<unsigned int>,
                                         std::shared_ptr<state_with_acc>>
  pop_stack_acc(std::shared_ptr<state_with_acc> s);
  static inline const unsigned int pop_acc_test = [](void) {
    std::optional<unsigned int> o =
        pop_stack_acc(std::make_shared<state_with_acc>(state_with_acc{
                          List<unsigned int>::ctor::Cons_(
                              9u, List<unsigned int>::ctor::Cons_(
                                      8u, List<unsigned int>::ctor::Nil_())),
                          3u}))
            .first;
    std::shared_ptr<state_with_acc> s_ =
        pop_stack_acc(std::make_shared<state_with_acc>(state_with_acc{
                          List<unsigned int>::ctor::Cons_(
                              9u, List<unsigned int>::ctor::Cons_(
                                      8u, List<unsigned int>::ctor::Nil_())),
                          3u}))
            .second;
    if (o.has_value()) {
      unsigned int a = *o;
      return ((std::move(a) + s_->stack_with_acc->length()) + s_->acc);
    } else {
      return std::move(s_)->acc;
    }
  }();
  static std::shared_ptr<state_basic>
  push_stack(const std::shared_ptr<state_basic> &s, const unsigned int addr);
  __attribute__((pure)) static unsigned int
  top_or_zero(const std::shared_ptr<state_basic> &s);
  static inline const unsigned int empty_len =
      push_stack(std::make_shared<state_basic>(
                     state_basic{List<unsigned int>::ctor::Nil_()}),
                 12u)
          ->stack_basic->length();
  static inline const unsigned int overflow_head = top_or_zero(push_stack(
      std::make_shared<state_basic>(state_basic{List<unsigned int>::ctor::Cons_(
          1u, List<unsigned int>::ctor::Cons_(
                  2u, List<unsigned int>::ctor::Cons_(
                          3u, List<unsigned int>::ctor::Nil_())))}),
      9u));
  static inline const unsigned int overflow_len =
      push_stack(
          std::make_shared<state_basic>(
              state_basic{List<unsigned int>::ctor::Cons_(
                  1u, List<unsigned int>::ctor::Cons_(
                          2u, List<unsigned int>::ctor::Cons_(
                                  3u, List<unsigned int>::ctor::Nil_())))}),
          9u)
          ->stack_basic->length();
  static std::shared_ptr<state_basic>
  push_stack_cap(const std::shared_ptr<state_basic> &s,
                 const unsigned int addr);
  static inline const unsigned int push_cap_test =
      push_stack_cap(
          std::make_shared<state_basic>(
              state_basic{List<unsigned int>::ctor::Cons_(
                  10u,
                  List<unsigned int>::ctor::Cons_(
                      20u,
                      List<unsigned int>::ctor::Cons_(
                          30u, List<unsigned int>::ctor::Cons_(
                                   40u, List<unsigned int>::ctor::Nil_()))))}),
          7u)
          ->stack_basic->length();
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
