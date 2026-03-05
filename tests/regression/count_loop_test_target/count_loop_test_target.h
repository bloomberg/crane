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

struct CountLoopTestTarget {
  struct instruction {
  public:
    struct ISZ {
      unsigned int _a0;
      unsigned int _a1;
    };
    struct NOP {};
    using variant_t = std::variant<ISZ, NOP>;

  private:
    variant_t v_;
    explicit instruction(ISZ _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> ISZ_(unsigned int a0,
                                               unsigned int a1) {
        return std::shared_ptr<instruction>(new instruction(ISZ{a0, a1}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> ISZ_uptr(unsigned int a0,
                                                   unsigned int a1) {
        return std::unique_ptr<instruction>(new instruction(ISZ{a0, a1}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const T1 f0,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::ISZ _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f0; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const T1 f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::ISZ _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f0; }},
        i->v());
  }

  static std::shared_ptr<instruction>
  count_loop_test(const unsigned int loop_addr);

  static unsigned int target_of(const std::shared_ptr<instruction> &i);

  static inline const unsigned int t = target_of(count_loop_test((
      ((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
      1)));
};
