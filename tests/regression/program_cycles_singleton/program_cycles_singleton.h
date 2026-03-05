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
};

struct ProgramCyclesSingleton {
  enum class instruction { NOP };

  template <typename T1>
  static T1 instruction_rect(const T1 f, const instruction i) {
    return [&](void) {
      switch (i) {
      case instruction::NOP: {
        return f;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction_rec(const T1 f, const instruction i) {
    return [&](void) {
      switch (i) {
      case instruction::NOP: {
        return f;
      }
      }
    }();
  }

  struct state {
    unsigned int acc;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static unsigned int cycles(const std::shared_ptr<state> &_x,
                             const instruction _x0);

  static unsigned int
  program_cycles(const std::shared_ptr<state> &s,
                 const std::shared_ptr<List<instruction>> &prog);

  static inline const unsigned int t =
      program_cycles(std::make_shared<state>(state{0}),
                     List<instruction>::ctor::cons_(
                         instruction::NOP, List<instruction>::ctor::nil_()));
};
