#ifndef INCLUDED_PAGE_OPS
#define INCLUDED_PAGE_OPS

#include <memory>
#include <optional>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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
};

struct Nat {
  __attribute__((pure)) static unsigned int pow(const unsigned int n,
                                                const unsigned int m);
};

struct PageOps {
  struct state {
    unsigned int pc;
  };

  __attribute__((pure)) static unsigned int addr12_of_nat(const unsigned int n);
  __attribute__((pure)) static unsigned int page_of(const unsigned int p);
  __attribute__((pure)) static unsigned int page_base(const unsigned int p);
  __attribute__((pure)) static unsigned int page_offset(const unsigned int p);
  __attribute__((pure)) static unsigned int
  pc_inc1(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int
  pc_inc2(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int
  base_for_next1(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int
  base_for_next2(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int recompose(const unsigned int p);
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
    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    static std::shared_ptr<instruction> ldm(unsigned int a0) {
      return std::make_shared<instruction>(LDM{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{[&](const typename instruction::NOP) -> T1 { return f; },
                   [&](const typename instruction::LDM _args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{[&](const typename instruction::NOP) -> T1 { return f; },
                   [&](const typename instruction::LDM _args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        i->v());
  }

  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);

  template <typename T1>
  static std::shared_ptr<List<T1>> drop(const unsigned int n,
                                        std::shared_ptr<List<T1>> l) {
    if (n <= 0) {
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (l.use_count() == 1 && l->v().index() == 0) {
        return l;
      } else {
        return std::visit(
            Overloaded{
                [](const typename List<T1>::Nil) -> std::shared_ptr<List<T1>> {
                  return List<T1>::nil();
                },
                [&](const typename List<T1>::Cons _args)
                    -> std::shared_ptr<List<T1>> {
                  return drop<T1>(n_, _args.d_a1);
                }},
            l->v());
      }
    }
  }

  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<instruction>, unsigned int>>
  disassemble(const std::shared_ptr<List<unsigned int>> &rom,
              const unsigned int addr);
  static inline const unsigned int test_page_base_alignment =
      (256u ? page_base(777u) % 256u : page_base(777u));
  static inline const unsigned int test_page_base_next_pc = []() {
    std::shared_ptr<state> s = std::make_shared<state>(state{511u});
    return (base_for_next1(s) + base_for_next2(s));
  }();
  static inline const unsigned int test_page_boundary_cross =
      base_for_next1(std::make_shared<state>(state{255u}));
  static inline const unsigned int test_base_for_next_page_cross_1 =
      base_for_next1(std::make_shared<state>(state{255u}));
  static inline const unsigned int test_base_for_next_page_cross_2 =
      base_for_next2(std::make_shared<state>(state{255u}));
  static inline const bool test_page_decomp_roundtrip =
      (((256u ? 1027u / 256u : 0) * 256u) + (256u ? 1027u % 256u : 1027u)) ==
      1027u;
  static inline const unsigned int test_page_offset_recompose =
      recompose(addr12_of_nat(1027u));
  static inline const unsigned int test_page_recompose =
      recompose(addr12_of_nat(1027u));
  static inline const unsigned int test_pc_inc2_wraparound =
      pc_inc2(std::make_shared<state>(state{max_addr}));
  static inline const unsigned int test_pc_inc1_wrap =
      pc_inc1(std::make_shared<state>(state{max_addr}));
  static inline const unsigned int test_pc_inc2_wrap =
      pc_inc2(std::make_shared<state>(state{max_addr}));
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
      std::pair<std::shared_ptr<instruction>, unsigned int> p = *_cs;
      std::shared_ptr<instruction> _x = p.first;
      unsigned int next = p.second;
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
