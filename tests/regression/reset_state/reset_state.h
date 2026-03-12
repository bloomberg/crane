#ifndef INCLUDED_RESET_STATE
#define INCLUDED_RESET_STATE

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

  A nth(const unsigned int n, const A default0) const {
    if (n <= 0) {
      return std::visit(Overloaded{[&](const typename List<A>::nil _args) -> A {
                                     return default0;
                                   },
                                   [](const typename List<A>::cons _args) -> A {
                                     A x = _args._a0;
                                     return x;
                                   }},
                        this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<A>::nil _args) -> A { return default0; },
              [&](const typename List<A>::cons _args) -> A {
                std::shared_ptr<List<A>> l_ = _args._a1;
                return std::move(l_)->nth(m, default0);
              }},
          this->v());
    }
  }

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

struct ResetState {
  struct state_full {
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> regs_full;
    bool carry;
    unsigned int pc_full;
    std::shared_ptr<List<unsigned int>> stack;
    std::shared_ptr<List<unsigned int>> ram_sys;
    std::shared_ptr<List<unsigned int>> rom;
  };

  struct state_minimal {
    std::shared_ptr<List<unsigned int>> regs_minimal;
    bool carry_minimal;
    unsigned int pc_minimal;
    std::shared_ptr<List<unsigned int>> ram_sys_minimal;
    std::shared_ptr<List<unsigned int>> rom_minimal;
  };

  static std::shared_ptr<state_full>
  reset_state_full(std::shared_ptr<state_full> s);
  static inline const unsigned int memory_preserve_test = [](void) {
    std::unique_ptr<state_full> s = std::make_unique<state_full>(
        state_full{9u,
                   List<unsigned int>::ctor::cons_(
                       1u, List<unsigned int>::ctor::cons_(
                               2u, List<unsigned int>::ctor::nil_())),
                   true, 55u,
                   List<unsigned int>::ctor::cons_(
                       8u, List<unsigned int>::ctor::cons_(
                               7u, List<unsigned int>::ctor::nil_())),
                   List<unsigned int>::ctor::cons_(
                       3u, List<unsigned int>::ctor::cons_(
                               4u, List<unsigned int>::ctor::cons_(
                                       5u, List<unsigned int>::ctor::nil_()))),
                   List<unsigned int>::ctor::cons_(
                       10u, List<unsigned int>::ctor::cons_(
                                11u, List<unsigned int>::ctor::nil_()))});
    std::shared_ptr<state_full> s_ = reset_state_full(std::move(s));
    return (((s_->acc + s_->ram_sys->nth(1u, 0u)) + s_->rom->nth(0u, 0u)) +
            s_->stack->length());
  }();
  static std::shared_ptr<state_minimal>
  reset_state_minimal(std::shared_ptr<state_minimal> s);
  static inline const unsigned int pc_clear_test =
      reset_state_minimal(
          std::make_shared<state_minimal>(state_minimal{
              List<unsigned int>::ctor::cons_(
                  1u, List<unsigned int>::ctor::cons_(
                          2u, List<unsigned int>::ctor::nil_())),
              true, 99u,
              List<unsigned int>::ctor::cons_(3u,
                                              List<unsigned int>::ctor::nil_()),
              List<unsigned int>::ctor::cons_(
                  4u, List<unsigned int>::ctor::cons_(
                          5u, List<unsigned int>::ctor::nil_()))}))
          ->pc_minimal;
  static inline const std::pair<unsigned int, unsigned int> t =
      std::make_pair(memory_preserve_test, pc_clear_test);
};

#endif // INCLUDED_RESET_STATE
