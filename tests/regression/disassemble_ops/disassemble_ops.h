#ifndef INCLUDED_DISASSEMBLE_OPS
#define INCLUDED_DISASSEMBLE_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  __attribute__((pure)) static List<T1> repeat(const T1 x,
                                               const unsigned int &n);
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
    instruction() {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    explicit instruction(NOP2 _v) : d_v_(_v) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

    explicit instruction(LDM2 _v) : d_v_(std::move(_v)) {}

    instruction(const instruction &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction(instruction &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction &operator=(const instruction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction &operator=(instruction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP>(_sv.v())) {
        return instruction(NOP{});
      } else if (std::holds_alternative<NOP2>(_sv.v())) {
        return instruction(NOP2{});
      } else if (std::holds_alternative<LDM>(_sv.v())) {
        const auto &[d_a0] = std::get<LDM>(_sv.v());
        return instruction(LDM{d_a0});
      } else {
        const auto &[d_a0] = std::get<LDM2>(_sv.v());
        return instruction(LDM2{d_a0});
      }
    }

    // CREATORS
    constexpr static instruction nop() { return instruction(NOP{}); }

    constexpr static instruction nop2() { return instruction(NOP2{}); }

    __attribute__((pure)) static instruction ldm(unsigned int a0) {
      return instruction(LDM{std::move(a0)});
    }

    __attribute__((pure)) static instruction ldm2(unsigned int a0) {
      return instruction(LDM2{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction *operator->() { return this; }

    __attribute__((pure)) const instruction *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3>
  static T1 instruction_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                             const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::NOP2>(i.v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction::LDM>(i.v())) {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i.v());
      return f1(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM2>(i.v());
      return f2(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3>
  static T1 instruction_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                            const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::NOP2>(i.v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction::LDM>(i.v())) {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i.v());
      return f1(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM2>(i.v());
      return f2(d_a0);
    }
  }

  __attribute__((pure)) static instruction decode1(const unsigned int &b1,
                                                   const unsigned int &b2);
  __attribute__((pure)) static List<unsigned int> drop_(const unsigned int &n,
                                                        List<unsigned int> l);
  __attribute__((
      pure)) static std::optional<std::pair<instruction, unsigned int>>
  disassemble1(const List<unsigned int> &rom0, const unsigned int &addr);
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
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  __attribute__((pure)) static instruction decode2(const unsigned int &b1,
                                                   const unsigned int &b2);

  template <typename T1>
  __attribute__((pure)) static List<T1> drop(const unsigned int &n,
                                             List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        return drop<T1>(n_, *(d_a1));
      }
    }
  }

  __attribute__((
      pure)) static std::optional<std::pair<instruction, unsigned int>>
  disassemble2(const List<unsigned int> &rom0, const unsigned int &addr);
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
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  __attribute__((pure)) static instruction decode3(const unsigned int &b1,
                                                   const unsigned int &b2);
  __attribute__((
      pure)) static std::optional<std::pair<instruction, unsigned int>>
  disassemble3(const List<unsigned int> &rom0, const unsigned int &addr);

  template <typename T1>
  constexpr static bool is_none(const std::optional<T1> &o) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return false;
    } else {
      return true;
    }
  }

  static inline const bool test_disassemble_short_rom_none =
      is_none<std::pair<instruction, unsigned int>>(disassemble3(
          List<unsigned int>::cons(9u, List<unsigned int>::nil()), 0u));
  __attribute__((pure)) static instruction decode4(const unsigned int &b1,
                                                   const unsigned int &b2);
  __attribute__((
      pure)) static std::optional<std::pair<instruction, unsigned int>>
  disassemble4(const List<unsigned int> &rom0, const unsigned int &addr);

  struct state {
    List<unsigned int> regs;
    List<unsigned int> rom;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).regs.clone(), (*(this)).rom.clone()};
    }
  };

  static inline const state init_state =
      state{ListDef::template repeat<unsigned int>(0u, 16u),
            ListDef::template repeat<unsigned int>(0u, 4096u)};
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
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
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
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static inline const unsigned int test_init_state_regs =
      init_state.regs.length();
  static inline const unsigned int test_init_state_rom =
      init_state.rom.length();
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
__attribute__((pure)) List<T1> ListDef::repeat(const T1 x,
                                               const unsigned int &n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    unsigned int k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
