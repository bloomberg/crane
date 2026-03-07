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

struct EncodeLdmBytesInRange {
  struct instruction {
  public:
    struct LDM {
      unsigned int _a0;
    };
    using variant_t = std::variant<LDM>;

  private:
    variant_t v_;
    explicit instruction(LDM _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> LDM_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM{a0}));
      }
      static std::unique_ptr<instruction> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{[&](const typename instruction::LDM _args) -> T1 {
          unsigned int n = _args._a0;
          return f(std::move(n));
        }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{[&](const typename instruction::LDM _args) -> T1 {
          unsigned int n = _args._a0;
          return f(std::move(n));
        }},
        i->v());
  }

  static std::pair<unsigned int, unsigned int>
  encode(const std::shared_ptr<instruction> &i);

  static bool pair_in_range(const std::pair<unsigned int, unsigned int> p);

  static inline const bool t = pair_in_range(encode(instruction::ctor::LDM_(
      (((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1) +
        1) +
       1))));
};
