#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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
        Overloaded{
            [](const typename List<A>::nil _args) -> unsigned int { return 0; },
            [](const typename List<A>::cons _args) -> unsigned int {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return (std::move(l_)->length() + 1);
            }},
        this->v());
  }
};

struct ResetStateMemoryPreserve {
  struct state {
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> regs;
    bool carry;
    unsigned int pc;
    std::shared_ptr<List<unsigned int>> stack;
    std::shared_ptr<List<unsigned int>> ram_sys;
    std::shared_ptr<List<unsigned int>> rom;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  regs(const std::shared_ptr<state> &s);

  static bool carry(const std::shared_ptr<state> &s);

  static unsigned int pc(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  stack(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  ram_sys(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  rom(const std::shared_ptr<state> &s);

  static std::shared_ptr<state> reset_state(std::shared_ptr<state> s);

  static inline const unsigned int t = [](void) {
 std::unique_ptr<state> s = std::make_unique<state>(state{(((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::cons_((0 + 1), List<unsigned int>::ctor::cons_(((0 + 1) + 1), List<unsigned int>::ctor::nil_())), true, (((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::cons_(((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::cons_((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::nil_())), List<unsigned int>::ctor::cons_((((0 + 1) + 1) + 1), List<unsigned int>::ctor::cons_(((((0 + 1) + 1) + 1) + 1), List<unsigned int>::ctor::cons_((((((0 + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::nil_()))), List<unsigned int>::ctor::cons_(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::cons_((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::nil_()))});
 std::shared_ptr<state> s_ = reset_state(std::move(s));
 return (((s_->acc + s_->ram_sys->nth((0 + 1), 0)) + s_->rom->nth(0, 0)) +
         s_->stack->length());
  }();
};
