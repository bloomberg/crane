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

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
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

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<A>::cons _args) -> unsigned int {
                     std::shared_ptr<List<A>> l_ = _args._a1;
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

  static std::pair<std::optional<unsigned int>, std::shared_ptr<state_basic>>
  pop_stack(std::shared_ptr<state_basic> s);
  static bool is_none(const std::optional<unsigned int> o);
  static unsigned int option_or_zero(const std::optional<unsigned int> o);
  static inline const bool empty_is_none =
      is_none(pop_stack(std::make_shared<state_basic>(
                            state_basic{List<unsigned int>::ctor::nil_()}))
                  .first);
  static inline const unsigned int some_addr = option_or_zero(
      pop_stack(std::make_shared<state_basic>(
                    state_basic{List<unsigned int>::ctor::cons_(
                        9u, List<unsigned int>::ctor::cons_(
                                8u, List<unsigned int>::ctor::nil_()))}))
          .first);
  static std::pair<std::optional<unsigned int>, std::shared_ptr<state_with_acc>>
  pop_stack_acc(std::shared_ptr<state_with_acc> s);
  static inline const unsigned int pop_acc_test = [](void) {
    std::optional<unsigned int> o =
        pop_stack_acc(std::make_shared<state_with_acc>(state_with_acc{
                          List<unsigned int>::ctor::cons_(
                              9u, List<unsigned int>::ctor::cons_(
                                      8u, List<unsigned int>::ctor::nil_())),
                          3u}))
            .first;
    std::shared_ptr<state_with_acc> s_ =
        pop_stack_acc(std::make_shared<state_with_acc>(state_with_acc{
                          List<unsigned int>::ctor::cons_(
                              9u, List<unsigned int>::ctor::cons_(
                                      8u, List<unsigned int>::ctor::nil_())),
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
  static unsigned int top_or_zero(const std::shared_ptr<state_basic> &s);
  static inline const unsigned int empty_len =
      push_stack(std::make_shared<state_basic>(
                     state_basic{List<unsigned int>::ctor::nil_()}),
                 12u)
          ->stack_basic->length();
  static inline const unsigned int overflow_head = top_or_zero(push_stack(
      std::make_shared<state_basic>(state_basic{List<unsigned int>::ctor::cons_(
          1u, List<unsigned int>::ctor::cons_(
                  2u, List<unsigned int>::ctor::cons_(
                          3u, List<unsigned int>::ctor::nil_())))}),
      9u));
  static inline const unsigned int overflow_len =
      push_stack(
          std::make_shared<state_basic>(
              state_basic{List<unsigned int>::ctor::cons_(
                  1u, List<unsigned int>::ctor::cons_(
                          2u, List<unsigned int>::ctor::cons_(
                                  3u, List<unsigned int>::ctor::nil_())))}),
          9u)
          ->stack_basic->length();
  static std::shared_ptr<state_basic>
  push_stack_cap(const std::shared_ptr<state_basic> &s,
                 const unsigned int addr);
  static inline const unsigned int push_cap_test =
      push_stack_cap(
          std::make_shared<state_basic>(
              state_basic{List<unsigned int>::ctor::cons_(
                  10u,
                  List<unsigned int>::ctor::cons_(
                      20u,
                      List<unsigned int>::ctor::cons_(
                          30u, List<unsigned int>::ctor::cons_(
                                   40u, List<unsigned int>::ctor::nil_()))))}),
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
