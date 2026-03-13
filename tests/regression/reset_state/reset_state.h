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

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       t_A x = _args.d_a0;
                       return x;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args) -> t_A {
                       std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                       return std::move(l_)->nth(m, default0);
                     }},
          this->v());
    }
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
                   List<unsigned int>::ctor::Cons_(
                       1u, List<unsigned int>::ctor::Cons_(
                               2u, List<unsigned int>::ctor::Nil_())),
                   true, 55u,
                   List<unsigned int>::ctor::Cons_(
                       8u, List<unsigned int>::ctor::Cons_(
                               7u, List<unsigned int>::ctor::Nil_())),
                   List<unsigned int>::ctor::Cons_(
                       3u, List<unsigned int>::ctor::Cons_(
                               4u, List<unsigned int>::ctor::Cons_(
                                       5u, List<unsigned int>::ctor::Nil_()))),
                   List<unsigned int>::ctor::Cons_(
                       10u, List<unsigned int>::ctor::Cons_(
                                11u, List<unsigned int>::ctor::Nil_()))});
    std::shared_ptr<state_full> s_ = reset_state_full(std::move(s));
    return (((s_->acc + s_->ram_sys->nth(1u, 0u)) + s_->rom->nth(0u, 0u)) +
            s_->stack->length());
  }();
  static std::shared_ptr<state_minimal>
  reset_state_minimal(std::shared_ptr<state_minimal> s);
  static inline const unsigned int pc_clear_test =
      reset_state_minimal(
          std::make_shared<state_minimal>(state_minimal{
              List<unsigned int>::ctor::Cons_(
                  1u, List<unsigned int>::ctor::Cons_(
                          2u, List<unsigned int>::ctor::Nil_())),
              true, 99u,
              List<unsigned int>::ctor::Cons_(3u,
                                              List<unsigned int>::ctor::Nil_()),
              List<unsigned int>::ctor::Cons_(
                  4u, List<unsigned int>::ctor::Cons_(
                          5u, List<unsigned int>::ctor::Nil_()))}))
          ->pc_minimal;
  static inline const std::pair<unsigned int, unsigned int> t =
      std::make_pair(memory_preserve_test, pc_clear_test);
};

#endif // INCLUDED_RESET_STATE
