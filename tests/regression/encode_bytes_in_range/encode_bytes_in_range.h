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

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct EncodeBytesInRange {
  struct instruction {
  public:
    struct CLB {};
    struct CMC {};
    struct DAA {};
    struct FIM {
      unsigned int _a0;
      unsigned int _a1;
    };
    struct JUN {
      unsigned int _a0;
    };
    struct LDM {
      unsigned int _a0;
    };
    struct NOP {};
    struct RDM {};
    struct TCS {};
    struct WPM {};
    struct WR0 {};
    using variant_t =
        std::variant<CLB, CMC, DAA, FIM, JUN, LDM, NOP, RDM, TCS, WPM, WR0>;

  private:
    variant_t v_;
    explicit instruction(CLB _v) : v_(std::move(_v)) {}
    explicit instruction(CMC _v) : v_(std::move(_v)) {}
    explicit instruction(DAA _v) : v_(std::move(_v)) {}
    explicit instruction(FIM _v) : v_(std::move(_v)) {}
    explicit instruction(JUN _v) : v_(std::move(_v)) {}
    explicit instruction(LDM _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}
    explicit instruction(RDM _v) : v_(std::move(_v)) {}
    explicit instruction(TCS _v) : v_(std::move(_v)) {}
    explicit instruction(WPM _v) : v_(std::move(_v)) {}
    explicit instruction(WR0 _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> CLB_() {
        return std::shared_ptr<instruction>(new instruction(CLB{}));
      }
      static std::shared_ptr<instruction> CMC_() {
        return std::shared_ptr<instruction>(new instruction(CMC{}));
      }
      static std::shared_ptr<instruction> DAA_() {
        return std::shared_ptr<instruction>(new instruction(DAA{}));
      }
      static std::shared_ptr<instruction> FIM_(unsigned int a0,
                                               unsigned int a1) {
        return std::shared_ptr<instruction>(new instruction(FIM{a0, a1}));
      }
      static std::shared_ptr<instruction> JUN_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::shared_ptr<instruction> LDM_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM{a0}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::shared_ptr<instruction> RDM_() {
        return std::shared_ptr<instruction>(new instruction(RDM{}));
      }
      static std::shared_ptr<instruction> TCS_() {
        return std::shared_ptr<instruction>(new instruction(TCS{}));
      }
      static std::shared_ptr<instruction> WPM_() {
        return std::shared_ptr<instruction>(new instruction(WPM{}));
      }
      static std::shared_ptr<instruction> WR0_() {
        return std::shared_ptr<instruction>(new instruction(WR0{}));
      }
      static std::unique_ptr<instruction> CLB_uptr() {
        return std::unique_ptr<instruction>(new instruction(CLB{}));
      }
      static std::unique_ptr<instruction> CMC_uptr() {
        return std::unique_ptr<instruction>(new instruction(CMC{}));
      }
      static std::unique_ptr<instruction> DAA_uptr() {
        return std::unique_ptr<instruction>(new instruction(DAA{}));
      }
      static std::unique_ptr<instruction> FIM_uptr(unsigned int a0,
                                                   unsigned int a1) {
        return std::unique_ptr<instruction>(new instruction(FIM{a0, a1}));
      }
      static std::unique_ptr<instruction> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::unique_ptr<instruction> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM{a0}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> RDM_uptr() {
        return std::unique_ptr<instruction>(new instruction(RDM{}));
      }
      static std::unique_ptr<instruction> TCS_uptr() {
        return std::unique_ptr<instruction>(new instruction(TCS{}));
      }
      static std::unique_ptr<instruction> WPM_uptr() {
        return std::unique_ptr<instruction>(new instruction(WPM{}));
      }
      static std::unique_ptr<instruction> WR0_uptr() {
        return std::unique_ptr<instruction>(new instruction(WR0{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
            MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
  static T1 instruction_rect(const T1 f, const T1 f0, const T1 f1, F3 &&f2,
                             F4 &&f3, F5 &&f4, const T1 f5, const T1 f6,
                             const T1 f7, const T1 f8, const T1 f9,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::CLB _args) -> T1 { return f; },
            [&](const typename instruction::CMC _args) -> T1 { return f0; },
            [&](const typename instruction::DAA _args) -> T1 { return f1; },
            [&](const typename instruction::FIM _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f2(std::move(n), std::move(n0));
            },
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f3(std::move(n));
            },
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f4(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f5; },
            [&](const typename instruction::RDM _args) -> T1 { return f6; },
            [&](const typename instruction::TCS _args) -> T1 { return f7; },
            [&](const typename instruction::WPM _args) -> T1 { return f8; },
            [&](const typename instruction::WR0 _args) -> T1 { return f9; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
            MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
  static T1 instruction_rec(const T1 f, const T1 f0, const T1 f1, F3 &&f2,
                            F4 &&f3, F5 &&f4, const T1 f5, const T1 f6,
                            const T1 f7, const T1 f8, const T1 f9,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::CLB _args) -> T1 { return f; },
            [&](const typename instruction::CMC _args) -> T1 { return f0; },
            [&](const typename instruction::DAA _args) -> T1 { return f1; },
            [&](const typename instruction::FIM _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f2(std::move(n), std::move(n0));
            },
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f3(std::move(n));
            },
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f4(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f5; },
            [&](const typename instruction::RDM _args) -> T1 { return f6; },
            [&](const typename instruction::TCS _args) -> T1 { return f7; },
            [&](const typename instruction::WPM _args) -> T1 { return f8; },
            [&](const typename instruction::WR0 _args) -> T1 { return f9; }},
        i->v());
  }

  static std::pair<unsigned int, unsigned int>
  encode(const std::shared_ptr<instruction> &i);

  static bool pair_in_range(const std::pair<unsigned int, unsigned int> p);

  static inline const bool t =
      ((((((((((pair_in_range(encode(instruction::ctor::CLB_())) &&
                pair_in_range(encode(instruction::ctor::CMC_()))) &&
               pair_in_range(encode(instruction::ctor::DAA_()))) &&
              pair_in_range(encode(instruction::ctor::FIM_(14u, 255u)))) &&
             pair_in_range(encode(instruction::ctor::JUN_(4095u)))) &&
            pair_in_range(encode(instruction::ctor::LDM_(15u)))) &&
           pair_in_range(encode(instruction::ctor::NOP_()))) &&
          pair_in_range(encode(instruction::ctor::RDM_()))) &&
         pair_in_range(encode(instruction::ctor::TCS_()))) &&
        pair_in_range(encode(instruction::ctor::WPM_()))) &&
       pair_in_range(encode(instruction::ctor::WR0_())));
};
