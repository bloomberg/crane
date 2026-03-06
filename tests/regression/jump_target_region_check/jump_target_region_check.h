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

struct JumpTargetRegionCheck {
  struct instruction {
  public:
    struct JUN_ {
      unsigned int _a0;
    };
    struct JMS_ {
      unsigned int _a0;
    };
    struct NOP_ {};
    using variant_t = std::variant<JUN_, JMS_, NOP_>;

  private:
    variant_t v_;
    explicit instruction(JUN_ _v) : v_(std::move(_v)) {}
    explicit instruction(JMS_ _v) : v_(std::move(_v)) {}
    explicit instruction(NOP_ _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> JUN__(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JUN_{a0}));
      }
      static std::shared_ptr<instruction> JMS__(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JMS_{a0}));
      }
      static std::shared_ptr<instruction> NOP__() {
        return std::shared_ptr<instruction>(new instruction(NOP_{}));
      }
      static std::unique_ptr<instruction> JUN__uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JUN_{a0}));
      }
      static std::unique_ptr<instruction> JMS__uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JMS_{a0}));
      }
      static std::unique_ptr<instruction> NOP__uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP_{}));
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
            [&](const typename instruction::JUN_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::JMS_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::NOP_ _args) -> T1 { return f1; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(F0 &&f, F1 &&f0, const T1 f1,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JUN_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::JMS_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::NOP_ _args) -> T1 { return f1; }},
        i->v());
  }

  struct layout {
    unsigned int base_;
    unsigned int code_;
  };

  static unsigned int base_(const std::shared_ptr<layout> &l);

  static unsigned int code_(const std::shared_ptr<layout> &l);

  static bool addr_in_region(const unsigned int addr,
                             const std::shared_ptr<layout> &l);

  static std::optional<unsigned int>
  jump_target(const std::shared_ptr<instruction> &i);

  static bool in_layout(const std::shared_ptr<layout> &l,
                        const std::shared_ptr<instruction> &i);

  static inline const bool t = in_layout(
      std::make_shared<layout>(layout{
          ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1),
          ((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
           1)}),
      instruction::ctor::JUN__(
          ((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
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
                1) +
               1) +
              1) +
             1) +
            1) +
           1)));
};
