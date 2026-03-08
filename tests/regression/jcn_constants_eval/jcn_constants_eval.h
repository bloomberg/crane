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

struct JcnConstantsEval {
  struct state {
    unsigned int acc;
    bool carry;
    bool test_pin;
  };

  static bool jcn_condition(const std::shared_ptr<state> &s,
                            const unsigned int cond);

  static inline const unsigned int JCN_JNT = 1u;

  static inline const unsigned int JCN_JC = 2u;

  static inline const unsigned int JCN_JZ = 4u;

  static inline const unsigned int JCN_JT = 9u;

  static inline const unsigned int JCN_JNC = 10u;

  static inline const unsigned int JCN_JNZ = 12u;

  static inline const unsigned int t = []() {
    return [](void) {
      std::shared_ptr<state> s =
          std::make_shared<state>(state{0u, true, false});
      return (([&](void) {
                if (jcn_condition(s, JCN_JC)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }() +
               [&](void) {
                 if (jcn_condition(s, JCN_JZ)) {
                   return 1u;
                 } else {
                   return 0u;
                 }
               }()) +
              [&](void) {
                if (jcn_condition(s, JCN_JNT)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }());
    }();
  }();
};
