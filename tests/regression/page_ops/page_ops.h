#ifndef INCLUDED_PAGE_OPS
#define INCLUDED_PAGE_OPS

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
};

struct Nat {
  __attribute__((pure)) static unsigned int pow(const unsigned int &n,
                                                const unsigned int &m);
};

struct PageOps {
  struct state {
    unsigned int pc;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const { return state{(*(this)).pc}; }
  };

  __attribute__((pure)) static unsigned int
  addr12_of_nat(const unsigned int &n);
  __attribute__((pure)) static unsigned int page_of(const unsigned int &p);
  __attribute__((pure)) static unsigned int page_base(const unsigned int &p);
  __attribute__((pure)) static unsigned int page_offset(const unsigned int &p);
  __attribute__((pure)) static unsigned int pc_inc1(const state &s);
  __attribute__((pure)) static unsigned int pc_inc2(const state &s);
  __attribute__((pure)) static unsigned int base_for_next1(const state &s);
  __attribute__((pure)) static unsigned int base_for_next2(const state &s);
  __attribute__((pure)) static unsigned int recompose(const unsigned int &p);
  static inline const unsigned int max_addr = ((
      (Nat::pow(2u, 12u) - 1u) > Nat::pow(2u, 12u) ? 0
                                                   : (Nat::pow(2u, 12u) - 1u)));

  struct instruction {
    // TYPES
    struct NOP {};

    struct LDM {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP, LDM>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

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
      } else {
        const auto &[d_a0] = std::get<LDM>(_sv.v());
        return instruction(LDM{d_a0});
      }
    }

    // CREATORS
    constexpr static instruction nop() { return instruction(NOP{}); }

    __attribute__((pure)) static instruction ldm(unsigned int a0) {
      return instruction(LDM{std::move(a0)});
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

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(const T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i.v());
      return f0(d_a0);
    }
  }

  __attribute__((pure)) static instruction decode(const unsigned int &b1,
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
  disassemble(const List<unsigned int> &rom, const unsigned int &addr);
  static inline const unsigned int test_page_base_alignment =
      (256u ? page_base(777u) % 256u : page_base(777u));
  static inline const unsigned int test_page_base_next_pc = []() {
    state s = state{511u};
    return (base_for_next1(s) + base_for_next2(s));
  }();
  static inline const unsigned int test_page_boundary_cross =
      base_for_next1(state{255u});
  static inline const unsigned int test_base_for_next_page_cross_1 =
      base_for_next1(state{255u});
  static inline const unsigned int test_base_for_next_page_cross_2 =
      base_for_next2(state{255u});
  static inline const bool test_page_decomp_roundtrip =
      (((256u ? 1027u / 256u : 0) * 256u) + (256u ? 1027u % 256u : 1027u)) ==
      1027u;
  static inline const unsigned int test_page_offset_recompose =
      recompose(addr12_of_nat(1027u));
  static inline const unsigned int test_page_recompose =
      recompose(addr12_of_nat(1027u));
  static inline const unsigned int test_pc_inc2_wraparound =
      pc_inc2(state{max_addr});
  static inline const unsigned int test_pc_inc1_wrap = pc_inc1(state{max_addr});
  static inline const unsigned int test_pc_inc2_wrap = pc_inc2(state{max_addr});
  static inline const unsigned int test_disassemble_edge =
      []() -> unsigned int {
    auto _cs = disassemble(
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
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<std::pair<std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>,
                                            unsigned int>,
                                  unsigned int>,
                              bool>,
                          unsigned int>,
                      unsigned int>,
                  unsigned int>,
              unsigned int>,
          unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(
                                                  test_page_base_alignment,
                                                  test_page_base_next_pc),
                                              test_page_boundary_cross),
                                          test_base_for_next_page_cross_1),
                                      test_base_for_next_page_cross_2),
                                  test_page_decomp_roundtrip),
                              test_page_offset_recompose),
                          test_page_recompose),
                      test_pc_inc2_wraparound),
                  test_pc_inc1_wrap),
              test_pc_inc2_wrap),
          test_disassemble_edge);
};

#endif // INCLUDED_PAGE_OPS
