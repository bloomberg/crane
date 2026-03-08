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
};

struct DisassembleNextAddress {
  struct instruction {
  public:
    struct NOP {};
    struct LDM {
      unsigned int _a0;
    };
    using variant_t = std::variant<NOP, LDM>;

  private:
    variant_t v_;
    explicit instruction(NOP _v) : v_(std::move(_v)) {}
    explicit instruction(LDM _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::shared_ptr<instruction> LDM_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM{a0}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM{a0}));
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
            [&](const typename instruction::LDM _args) -> T1 {
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
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);

  template <typename T1>
  static std::shared_ptr<List<T1>> drop(const unsigned int n,
                                        std::shared_ptr<List<T1>> l) {
    if (n <= 0) {
      return std::move(l);
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> l_ = _args._a1;
                                     return drop<T1>(std::move(n_),
                                                     std::move(l_));
                                   }},
                        l->v());
    }
  }

  static std::optional<std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble(const std::shared_ptr<List<unsigned int>> &rom,
              const unsigned int addr);

  static inline const unsigned int t = [](void) {
    if (disassemble(
            List<unsigned int>::ctor::cons_(
                0u,
                List<unsigned int>::ctor::cons_(
                    7u, List<unsigned int>::ctor::cons_(
                            9u, List<unsigned int>::ctor::cons_(
                                    11u, List<unsigned int>::ctor::nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble(
          List<unsigned int>::ctor::cons_(
              0u, List<unsigned int>::ctor::cons_(
                      7u, List<unsigned int>::ctor::cons_(
                              9u, List<unsigned int>::ctor::cons_(
                                      11u, List<unsigned int>::ctor::nil_())))),
          0u);
      std::shared_ptr<instruction> _x = p.first;
      unsigned int next = p.second;
      return std::move(next);
    } else {
      return 0u;
    }
  }();
};
