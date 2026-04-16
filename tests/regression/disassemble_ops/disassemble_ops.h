#ifndef INCLUDED_DISASSEMBLE_OPS
#define INCLUDED_DISASSEMBLE_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
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

  public:
    // CREATORS
    explicit instruction(NOP _v) : d_v_(_v) {}

    explicit instruction(NOP2 _v) : d_v_(_v) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

    explicit instruction(LDM2 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    static std::shared_ptr<instruction> nop2() {
      return std::make_shared<instruction>(NOP2{});
    }

    static std::shared_ptr<instruction> ldm(unsigned int a0) {
      return std::make_shared<instruction>(LDM{std::move(a0)});
    }

    static std::shared_ptr<instruction> ldm2(unsigned int a0) {
      return std::make_shared<instruction>(LDM2{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3>
  static T1 instruction_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                             const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::NOP>(i->v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::NOP2>(i->v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction::LDM>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i->v());
      return f1(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM2>(i->v());
      return f2(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3>
  static T1 instruction_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                            const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::NOP>(i->v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::NOP2>(i->v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction::LDM>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i->v());
      return f1(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM2>(i->v());
      return f2(d_a0);
    }
  }

  static std::shared_ptr<instruction> decode1(const unsigned int b1,
                                              const unsigned int b2);
  static std::shared_ptr<List<unsigned int>>
  drop_(const unsigned int n, std::shared_ptr<List<unsigned int>> l);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble1(const std::shared_ptr<List<unsigned int>> &rom0,
               const unsigned int addr);
  static inline const unsigned int test_disassemble_drop_window =
      []() -> unsigned int {
    auto _cs = disassemble1(
        List<unsigned int>::cons(
            1u, List<unsigned int>::cons(
                    2u, List<unsigned int>::cons(
                            3u, List<unsigned int>::cons(
                                    4u, List<unsigned int>::cons(
                                            5u, List<unsigned int>::nil()))))),
        1u);
    if (_cs.has_value()) {
      const std::pair<std::shared_ptr<instruction>, unsigned int> &p = *_cs;
      const std::shared_ptr<instruction> &_x = p.first;
      const unsigned int &next = p.second;
      return next;
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
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
        return drop<T1>(n_, d_a1);
      }
    }
  }

  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble2(const std::shared_ptr<List<unsigned int>> &rom0,
               const unsigned int addr);
  static inline const unsigned int test_disassemble_next_address =
      []() -> unsigned int {
    auto _cs = disassemble2(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<std::shared_ptr<instruction>, unsigned int> &p = *_cs;
      const std::shared_ptr<instruction> &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static std::shared_ptr<instruction> decode3(const unsigned int b1,
                                              const unsigned int b2);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble3(const std::shared_ptr<List<unsigned int>> &rom0,
               const unsigned int addr);

  template <typename T1>
  __attribute__((pure)) static bool is_none(const std::optional<T1> o) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return false;
    } else {
      return true;
    }
  }

  static inline const bool test_disassemble_short_rom_none =
      is_none<std::pair<std::shared_ptr<instruction>, unsigned int>>(
          disassemble3(List<unsigned int>::cons(9u, List<unsigned int>::nil()),
                       0u));
  static std::shared_ptr<instruction> decode4(const unsigned int b1,
                                              const unsigned int b2);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble4(const std::shared_ptr<List<unsigned int>> &rom0,
               const unsigned int addr);

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
    std::shared_ptr<List<unsigned int>> rom;
  };

  static inline const std::shared_ptr<state> init_state =
      std::make_shared<state>(
          state{ListDef::template repeat<unsigned int>(0u, 16u),
                ListDef::template repeat<unsigned int>(0u, 4096u)});
  static inline const unsigned int test_decode_disassemble_1 =
      []() -> unsigned int {
    auto _cs = disassemble4(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<std::shared_ptr<instruction>, unsigned int> &p = *_cs;
      const std::shared_ptr<instruction> &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static inline const unsigned int test_decode_disassemble_2 =
      []() -> unsigned int {
    auto _cs = disassemble4(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<std::shared_ptr<instruction>, unsigned int> &p = *_cs;
      const std::shared_ptr<instruction> &_x = p.first;
      const unsigned int &next = p.second;
      return next;
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
    return List<T1>::nil();
  } else {
    unsigned int k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
