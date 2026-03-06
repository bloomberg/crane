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

struct JumpClassifierFlags {
  struct instruction {
  public:
    struct JCN {
      unsigned int _a0;
      unsigned int _a1;
    };
    struct JUN {
      unsigned int _a0;
    };
    struct JMS {
      unsigned int _a0;
    };
    struct JIN {
      unsigned int _a0;
    };
    struct BBL {
      unsigned int _a0;
    };
    struct ISZ {
      unsigned int _a0;
      unsigned int _a1;
    };
    struct ADD {
      unsigned int _a0;
    };
    struct NOP {};
    using variant_t = std::variant<JCN, JUN, JMS, JIN, BBL, ISZ, ADD, NOP>;

  private:
    variant_t v_;
    explicit instruction(JCN _v) : v_(std::move(_v)) {}
    explicit instruction(JUN _v) : v_(std::move(_v)) {}
    explicit instruction(JMS _v) : v_(std::move(_v)) {}
    explicit instruction(JIN _v) : v_(std::move(_v)) {}
    explicit instruction(BBL _v) : v_(std::move(_v)) {}
    explicit instruction(ISZ _v) : v_(std::move(_v)) {}
    explicit instruction(ADD _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> JCN_(unsigned int a0,
                                               unsigned int a1) {
        return std::shared_ptr<instruction>(new instruction(JCN{a0, a1}));
      }
      static std::shared_ptr<instruction> JUN_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::shared_ptr<instruction> JMS_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::shared_ptr<instruction> JIN_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JIN{a0}));
      }
      static std::shared_ptr<instruction> BBL_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(BBL{a0}));
      }
      static std::shared_ptr<instruction> ISZ_(unsigned int a0,
                                               unsigned int a1) {
        return std::shared_ptr<instruction>(new instruction(ISZ{a0, a1}));
      }
      static std::shared_ptr<instruction> ADD_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(ADD{a0}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> JCN_uptr(unsigned int a0,
                                                   unsigned int a1) {
        return std::unique_ptr<instruction>(new instruction(JCN{a0, a1}));
      }
      static std::unique_ptr<instruction> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::unique_ptr<instruction> JMS_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::unique_ptr<instruction> JIN_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JIN{a0}));
      }
      static std::unique_ptr<instruction> BBL_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(BBL{a0}));
      }
      static std::unique_ptr<instruction> ISZ_uptr(unsigned int a0,
                                                   unsigned int a1) {
        return std::unique_ptr<instruction>(new instruction(ISZ{a0, a1}));
      }
      static std::unique_ptr<instruction> ADD_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(ADD{a0}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int, unsigned int> F5,
            MapsTo<T1, unsigned int> F6>
  static T1 instruction_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                             F5 &&f4, F6 &&f5, const T1 f6,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JCN _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::JIN _args) -> T1 {
              unsigned int n = _args._a0;
              return f2(std::move(n));
            },
            [&](const typename instruction::BBL _args) -> T1 {
              unsigned int n = _args._a0;
              return f3(std::move(n));
            },
            [&](const typename instruction::ISZ _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f4(std::move(n), std::move(n0));
            },
            [&](const typename instruction::ADD _args) -> T1 {
              unsigned int n = _args._a0;
              return f5(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f6; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int, unsigned int> F5,
            MapsTo<T1, unsigned int> F6>
  static T1 instruction_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                            F6 &&f5, const T1 f6,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JCN _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::JIN _args) -> T1 {
              unsigned int n = _args._a0;
              return f2(std::move(n));
            },
            [&](const typename instruction::BBL _args) -> T1 {
              unsigned int n = _args._a0;
              return f3(std::move(n));
            },
            [&](const typename instruction::ISZ _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f4(std::move(n), std::move(n0));
            },
            [&](const typename instruction::ADD _args) -> T1 {
              unsigned int n = _args._a0;
              return f5(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f6; }},
        i->v());
  }

  static bool is_jump(const std::shared_ptr<instruction> &i);

  static unsigned int
  count_jumps(const std::shared_ptr<List<std::shared_ptr<instruction>>> &prog);

  static inline const unsigned int t =
      count_jumps(List<std::shared_ptr<instruction>>::ctor::cons_(
          instruction::ctor::ADD_(0),
          List<std::shared_ptr<instruction>>::ctor::cons_(
              instruction::ctor::JCN_(
                  ((((0 + 1) + 1) + 1) + 1),
                  ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
              List<std::shared_ptr<instruction>>::ctor::cons_(
                  instruction::ctor::NOP_(),
                  List<std::shared_ptr<instruction>>::ctor::cons_(
                      instruction::ctor::JMS_(
                          (((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) +
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
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1)),
                      List<std::shared_ptr<instruction>>::ctor::cons_(
                          instruction::ctor::ISZ_((0 + 1), ((0 + 1) + 1)),
                          List<
                              std::shared_ptr<instruction>>::ctor::nil_()))))));
};
