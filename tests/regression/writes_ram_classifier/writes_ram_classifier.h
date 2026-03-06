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

struct WritesRamClassifier {
  struct instruction {
  public:
    struct WRM {};
    struct WMP {};
    struct WR0 {};
    struct WR1 {};
    struct WR2 {};
    struct WR3 {};
    struct NOP {};
    struct ADD {
      unsigned int _a0;
    };
    using variant_t = std::variant<WRM, WMP, WR0, WR1, WR2, WR3, NOP, ADD>;

  private:
    variant_t v_;
    explicit instruction(WRM _v) : v_(std::move(_v)) {}
    explicit instruction(WMP _v) : v_(std::move(_v)) {}
    explicit instruction(WR0 _v) : v_(std::move(_v)) {}
    explicit instruction(WR1 _v) : v_(std::move(_v)) {}
    explicit instruction(WR2 _v) : v_(std::move(_v)) {}
    explicit instruction(WR3 _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}
    explicit instruction(ADD _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> WRM_() {
        return std::shared_ptr<instruction>(new instruction(WRM{}));
      }
      static std::shared_ptr<instruction> WMP_() {
        return std::shared_ptr<instruction>(new instruction(WMP{}));
      }
      static std::shared_ptr<instruction> WR0_() {
        return std::shared_ptr<instruction>(new instruction(WR0{}));
      }
      static std::shared_ptr<instruction> WR1_() {
        return std::shared_ptr<instruction>(new instruction(WR1{}));
      }
      static std::shared_ptr<instruction> WR2_() {
        return std::shared_ptr<instruction>(new instruction(WR2{}));
      }
      static std::shared_ptr<instruction> WR3_() {
        return std::shared_ptr<instruction>(new instruction(WR3{}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::shared_ptr<instruction> ADD_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(ADD{a0}));
      }
      static std::unique_ptr<instruction> WRM_uptr() {
        return std::unique_ptr<instruction>(new instruction(WRM{}));
      }
      static std::unique_ptr<instruction> WMP_uptr() {
        return std::unique_ptr<instruction>(new instruction(WMP{}));
      }
      static std::unique_ptr<instruction> WR0_uptr() {
        return std::unique_ptr<instruction>(new instruction(WR0{}));
      }
      static std::unique_ptr<instruction> WR1_uptr() {
        return std::unique_ptr<instruction>(new instruction(WR1{}));
      }
      static std::unique_ptr<instruction> WR2_uptr() {
        return std::unique_ptr<instruction>(new instruction(WR2{}));
      }
      static std::unique_ptr<instruction> WR3_uptr() {
        return std::unique_ptr<instruction>(new instruction(WR3{}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> ADD_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(ADD{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F7>
  static T1 instruction_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const T1 f3, const T1 f4, const T1 f5, F7 &&f6,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::WRM _args) -> T1 { return f; },
            [&](const typename instruction::WMP _args) -> T1 { return f0; },
            [&](const typename instruction::WR0 _args) -> T1 { return f1; },
            [&](const typename instruction::WR1 _args) -> T1 { return f2; },
            [&](const typename instruction::WR2 _args) -> T1 { return f3; },
            [&](const typename instruction::WR3 _args) -> T1 { return f4; },
            [&](const typename instruction::NOP _args) -> T1 { return f5; },
            [&](const typename instruction::ADD _args) -> T1 {
              unsigned int n = _args._a0;
              return f6(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F7>
  static T1 instruction_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const T1 f4, const T1 f5, F7 &&f6,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::WRM _args) -> T1 { return f; },
            [&](const typename instruction::WMP _args) -> T1 { return f0; },
            [&](const typename instruction::WR0 _args) -> T1 { return f1; },
            [&](const typename instruction::WR1 _args) -> T1 { return f2; },
            [&](const typename instruction::WR2 _args) -> T1 { return f3; },
            [&](const typename instruction::WR3 _args) -> T1 { return f4; },
            [&](const typename instruction::NOP _args) -> T1 { return f5; },
            [&](const typename instruction::ADD _args) -> T1 {
              unsigned int n = _args._a0;
              return f6(std::move(n));
            }},
        i->v());
  }

  static bool writes_ram(const std::shared_ptr<instruction> &i);

  static unsigned int count_writes_ram(
      const std::shared_ptr<List<std::shared_ptr<instruction>>> &prog);

  static inline const unsigned int t =
      count_writes_ram(List<std::shared_ptr<instruction>>::ctor::cons_(
          instruction::ctor::NOP_(),
          List<std::shared_ptr<instruction>>::ctor::cons_(
              instruction::ctor::WRM_(),
              List<std::shared_ptr<instruction>>::ctor::cons_(
                  instruction::ctor::ADD_((((0 + 1) + 1) + 1)),
                  List<std::shared_ptr<instruction>>::ctor::cons_(
                      instruction::ctor::WR3_(),
                      List<std::shared_ptr<instruction>>::ctor::cons_(
                          instruction::ctor::WMP_(),
                          List<std::shared_ptr<instruction>>::ctor::cons_(
                              instruction::ctor::NOP_(),
                              List<std::shared_ptr<instruction>>::ctor::
                                  nil_())))))));
};
