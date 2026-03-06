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
};

struct StepFetchDecodeExec {
  struct instruction {
  public:
    struct NOP {};
    struct ADD_ACC {
      unsigned int _a0;
    };
    using variant_t = std::variant<NOP, ADD_ACC>;

  private:
    variant_t v_;
    explicit instruction(NOP _v) : v_(std::move(_v)) {}
    explicit instruction(ADD_ACC _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::shared_ptr<instruction> ADD_ACC_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(ADD_ACC{a0}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> ADD_ACC_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(ADD_ACC{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  struct state {
    unsigned int acc;
    unsigned int pc;
    std::shared_ptr<List<unsigned int>> rom;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static unsigned int pc(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  rom(const std::shared_ptr<state> &s);

  static unsigned int fetch_byte(const std::shared_ptr<state> &s,
                                 const unsigned int addr);

  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);

  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const std::shared_ptr<instruction> &i);

  static std::shared_ptr<state> step(const std::shared_ptr<state> &s);

  static inline const unsigned int t = [](void) {
    std::shared_ptr<state> s1 = step(std::make_shared<state>(
        state{(((0 + 1) + 1) + 1), 0,
              List<unsigned int>::ctor::cons_(
                  (0 + 1), List<unsigned int>::ctor::cons_(
                               ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                               List<unsigned int>::ctor::cons_(
                                   0, List<unsigned int>::ctor::nil_())))}));
    return (s1->acc + s1->pc);
  }();
};
