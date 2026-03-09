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

struct ProgramWf {
  struct instruction {
  public:
    struct JUN {
      unsigned int _a0;
    };
    struct JMS {
      unsigned int _a0;
    };
    struct NOP {};
    using variant_t = std::variant<JUN, JMS, NOP>;

  private:
    variant_t v_;
    explicit instruction(JUN _v) : v_(std::move(_v)) {}
    explicit instruction(JMS _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> JUN_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::shared_ptr<instruction> JMS_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::unique_ptr<instruction> JMS_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(F0 &&f, F1 &&f0, const T1 f1,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f1; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(F0 &&f, F1 &&f0, const T1 f1,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f1; }},
        i->v());
  }

  struct layout {
    unsigned int base_addr;
    unsigned int code_size;
  };

  static std::optional<unsigned int>
  jump_target(const std::shared_ptr<instruction> &i);

  static inline const std::shared_ptr<layout> sample_layout =
      std::make_shared<layout>(layout{200u, 20u});

  static inline const std::shared_ptr<List<std::shared_ptr<instruction>>>
      sample_prog = List<std::shared_ptr<instruction>>::ctor::cons_(
          instruction::ctor::NOP_(),
          List<std::shared_ptr<instruction>>::ctor::cons_(
              instruction::ctor::JUN_(205u),
              List<std::shared_ptr<instruction>>::ctor::cons_(
                  instruction::ctor::JMS_(218u),
                  List<std::shared_ptr<instruction>>::ctor::nil_())));

  static inline const unsigned int sample_code_size = sample_layout->code_size;
};
