#ifndef INCLUDED_DISASSEMBLE_OPS
#define INCLUDED_DISASSEMBLE_OPS

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
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
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

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<A>::cons _args) -> unsigned int {
                     std::shared_ptr<List<A>> l_ = _args._a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x, const unsigned int n);
};

struct DisassembleOps {
  struct instruction {
    // TYPES
    struct NOP {};

    struct NOP2 {};

    struct LDM {
      unsigned int _a0;
    };

    struct LDM2 {
      unsigned int _a0;
    };

    using variant_t = std::variant<NOP, NOP2, LDM, LDM2>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

    explicit instruction(NOP2 _v) : v_(std::move(_v)) {}

    explicit instruction(LDM _v) : v_(std::move(_v)) {}

    explicit instruction(LDM2 _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }

      static std::shared_ptr<instruction> NOP2_() {
        return std::shared_ptr<instruction>(new instruction(NOP2{}));
      }

      static std::shared_ptr<instruction> LDM_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM{a0}));
      }

      static std::shared_ptr<instruction> LDM2_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM2{a0}));
      }

      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }

      static std::unique_ptr<instruction> NOP2_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP2{}));
      }

      static std::unique_ptr<instruction> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM{a0}));
      }

      static std::unique_ptr<instruction> LDM2_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM2{a0}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3>
  static T1 instruction_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::NOP2 _args) -> T1 { return f0; },
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::LDM2 _args) -> T1 {
              unsigned int n = _args._a0;
              return f2(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3>
  static T1 instruction_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::NOP2 _args) -> T1 { return f0; },
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::LDM2 _args) -> T1 {
              unsigned int n = _args._a0;
              return f2(std::move(n));
            }},
        i->v());
  }

  static std::shared_ptr<instruction> decode1(const unsigned int b1,
                                              const unsigned int b2);
  static std::shared_ptr<List<unsigned int>>
  drop_(const unsigned int n, std::shared_ptr<List<unsigned int>> l);
  static std::optional<std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble1(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);
  static inline const unsigned int test_disassemble_drop_window = [](void) {
    if (disassemble1(
            List<unsigned int>::ctor::cons_(
                1u,
                List<unsigned int>::ctor::cons_(
                    2u,
                    List<unsigned int>::ctor::cons_(
                        3u,
                        List<unsigned int>::ctor::cons_(
                            4u, List<unsigned int>::ctor::cons_(
                                    5u, List<unsigned int>::ctor::nil_()))))),
            1u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble1(
          List<unsigned int>::ctor::cons_(
              1u,
              List<unsigned int>::ctor::cons_(
                  2u,
                  List<unsigned int>::ctor::cons_(
                      3u, List<unsigned int>::ctor::cons_(
                              4u, List<unsigned int>::ctor::cons_(
                                      5u, List<unsigned int>::ctor::nil_()))))),
          1u);
      std::shared_ptr<instruction> _x = p.first;
      unsigned int next = p.second;
      return std::move(next);
    } else {
      return 0u;
    }
  }();
  static std::shared_ptr<instruction> decode2(const unsigned int b1,
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
  disassemble2(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);
  static inline const unsigned int test_disassemble_next_address = [](void) {
    if (disassemble2(
            List<unsigned int>::ctor::cons_(
                0u,
                List<unsigned int>::ctor::cons_(
                    7u, List<unsigned int>::ctor::cons_(
                            9u, List<unsigned int>::ctor::cons_(
                                    11u, List<unsigned int>::ctor::nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble2(
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
  static std::shared_ptr<instruction> decode3(const unsigned int b1,
                                              const unsigned int b2);
  static std::optional<std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble3(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);

  template <typename T1> static bool is_none(const std::optional<T1> o) {
    if (o.has_value()) {
      T1 _x = *o;
      return false;
    } else {
      return true;
    }
  }

  static inline const bool test_disassemble_short_rom_none =
      is_none<std::pair<std::shared_ptr<instruction>, unsigned int>>(
          disassemble3(List<unsigned int>::ctor::cons_(
                           9u, List<unsigned int>::ctor::nil_()),
                       0u));
  static std::shared_ptr<instruction> decode4(const unsigned int b1,
                                              const unsigned int b2);
  static std::optional<std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble4(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
    std::shared_ptr<List<unsigned int>> rom;
  };

  static inline const std::shared_ptr<state> init_state =
      std::make_shared<state>(
          state{ListDef::template repeat<unsigned int>(0u, 16u),
                ListDef::template repeat<unsigned int>(0u, 4096u)});
  static inline const unsigned int test_decode_disassemble_1 = [](void) {
    if (disassemble4(
            List<unsigned int>::ctor::cons_(
                0u,
                List<unsigned int>::ctor::cons_(
                    7u, List<unsigned int>::ctor::cons_(
                            9u, List<unsigned int>::ctor::cons_(
                                    11u, List<unsigned int>::ctor::nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble4(
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
  static inline const unsigned int test_decode_disassemble_2 = [](void) {
    if (disassemble4(
            List<unsigned int>::ctor::cons_(
                0u,
                List<unsigned int>::ctor::cons_(
                    7u, List<unsigned int>::ctor::cons_(
                            9u, List<unsigned int>::ctor::cons_(
                                    11u, List<unsigned int>::ctor::nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble4(
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
  static inline const unsigned int test_init_state_regs =
      init_state->regs->length();
  static inline const unsigned int test_init_state_rom =
      init_state->rom->length();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<std::pair<std::pair<unsigned int, unsigned int>, bool>,
                        unsigned int>,
              unsigned int>,
          unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(test_disassemble_drop_window,
                                         test_disassemble_next_address),
                          test_disassemble_short_rom_none),
                      test_decode_disassemble_1),
                  test_decode_disassemble_2),
              test_init_state_regs),
          test_init_state_rom);
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  if (n <= 0) {
    return List<T1>::ctor::nil_();
  } else {
    unsigned int k = n - 1;
    return List<T1>::ctor::cons_(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
