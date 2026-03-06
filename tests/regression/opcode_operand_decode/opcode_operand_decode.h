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

struct OpcodeOperandDecode {
  enum class instruction { NOP_, WRM_, WRR_, RDM_, DCL_ };

  template <typename T1>
  static T1 instruction_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const T1 f3, const instruction i) {
    return [&](void) {
      switch (i) {
      case instruction::NOP_: {
        return f;
      }
      case instruction::WRM_: {
        return f0;
      }
      case instruction::WRR_: {
        return f1;
      }
      case instruction::RDM_: {
        return f2;
      }
      case instruction::DCL_: {
        return f3;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const instruction i) {
    return [&](void) {
      switch (i) {
      case instruction::NOP_: {
        return f;
      }
      case instruction::WRM_: {
        return f0;
      }
      case instruction::WRR_: {
        return f1;
      }
      case instruction::RDM_: {
        return f2;
      }
      case instruction::DCL_: {
        return f3;
      }
      }
    }();
  }

  static instruction decode(const unsigned int b1, const unsigned int _x);

  static inline const unsigned int t = [](void) {
 switch (decode(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), 0)) {
 case instruction::NOP_: {
   return 0;
 }
 case instruction::WRM_: {
   return (0 + 1);
 }
 case instruction::WRR_: {
   return 0;
 }
 case instruction::RDM_: {
   return 0;
 }
 case instruction::DCL_: {
   return 0;
 }
 }
  }();
};
