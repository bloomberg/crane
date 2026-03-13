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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
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
      unsigned int d_a0;
    };

    struct LDM2 {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP, NOP2, LDM, LDM2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP2 _v) : d_v_(std::move(_v)) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

    explicit instruction(LDM2 _v) : d_v_(std::move(_v)) {}

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
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
              unsigned int n = _args.d_a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::LDM2 _args) -> T1 {
              unsigned int n = _args.d_a0;
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
              unsigned int n = _args.d_a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::LDM2 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f2(std::move(n));
            }},
        i->v());
  }

  static std::shared_ptr<instruction> decode1(const unsigned int b1,
                                              const unsigned int b2);
  static std::shared_ptr<List<unsigned int>>
  drop_(const unsigned int n, std::shared_ptr<List<unsigned int>> l);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble1(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);
  static inline const unsigned int test_disassemble_drop_window = [](void) {
    if (disassemble1(
            List<unsigned int>::ctor::Cons_(
                1u,
                List<unsigned int>::ctor::Cons_(
                    2u,
                    List<unsigned int>::ctor::Cons_(
                        3u,
                        List<unsigned int>::ctor::Cons_(
                            4u, List<unsigned int>::ctor::Cons_(
                                    5u, List<unsigned int>::ctor::Nil_()))))),
            1u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble1(
          List<unsigned int>::ctor::Cons_(
              1u,
              List<unsigned int>::ctor::Cons_(
                  2u,
                  List<unsigned int>::ctor::Cons_(
                      3u, List<unsigned int>::ctor::Cons_(
                              4u, List<unsigned int>::ctor::Cons_(
                                      5u, List<unsigned int>::ctor::Nil_()))))),
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
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> l_ = _args.d_a1;
                                     return drop<T1>(std::move(n_),
                                                     std::move(l_));
                                   }},
                        l->v());
    }
  }

  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble2(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);
  static inline const unsigned int test_disassemble_next_address = [](void) {
    if (disassemble2(
            List<unsigned int>::ctor::Cons_(
                0u,
                List<unsigned int>::ctor::Cons_(
                    7u, List<unsigned int>::ctor::Cons_(
                            9u, List<unsigned int>::ctor::Cons_(
                                    11u, List<unsigned int>::ctor::Nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble2(
          List<unsigned int>::ctor::Cons_(
              0u, List<unsigned int>::ctor::Cons_(
                      7u, List<unsigned int>::ctor::Cons_(
                              9u, List<unsigned int>::ctor::Cons_(
                                      11u, List<unsigned int>::ctor::Nil_())))),
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
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble3(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);

  template <typename T1>
  __attribute__((pure)) static bool is_none(const std::optional<T1> o) {
    if (o.has_value()) {
      T1 _x = *o;
      return false;
    } else {
      return true;
    }
  }

  static inline const bool test_disassemble_short_rom_none =
      is_none<std::pair<std::shared_ptr<instruction>, unsigned int>>(
          disassemble3(List<unsigned int>::ctor::Cons_(
                           9u, List<unsigned int>::ctor::Nil_()),
                       0u));
  static std::shared_ptr<instruction> decode4(const unsigned int b1,
                                              const unsigned int b2);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
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
            List<unsigned int>::ctor::Cons_(
                0u,
                List<unsigned int>::ctor::Cons_(
                    7u, List<unsigned int>::ctor::Cons_(
                            9u, List<unsigned int>::ctor::Cons_(
                                    11u, List<unsigned int>::ctor::Nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble4(
          List<unsigned int>::ctor::Cons_(
              0u, List<unsigned int>::ctor::Cons_(
                      7u, List<unsigned int>::ctor::Cons_(
                              9u, List<unsigned int>::ctor::Cons_(
                                      11u, List<unsigned int>::ctor::Nil_())))),
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
            List<unsigned int>::ctor::Cons_(
                0u,
                List<unsigned int>::ctor::Cons_(
                    7u, List<unsigned int>::ctor::Cons_(
                            9u, List<unsigned int>::ctor::Cons_(
                                    11u, List<unsigned int>::ctor::Nil_())))),
            0u)
            .has_value()) {
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *disassemble4(
          List<unsigned int>::ctor::Cons_(
              0u, List<unsigned int>::ctor::Cons_(
                      7u, List<unsigned int>::ctor::Cons_(
                              9u, List<unsigned int>::ctor::Cons_(
                                      11u, List<unsigned int>::ctor::Nil_())))),
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
    return List<T1>::ctor::Nil_();
  } else {
    unsigned int k = n - 1;
    return List<T1>::ctor::Cons_(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
