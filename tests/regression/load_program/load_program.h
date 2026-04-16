#ifndef INCLUDED_LOAD_PROGRAM
#define INCLUDED_LOAD_PROGRAM

#include <memory>
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
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
};

struct LoadProgram {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(x, d_a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, d_a10));
      }
    }
  }

  struct state {
    std::shared_ptr<List<unsigned int>> rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;
  };

  struct state_extended {
    unsigned int regs_len;
    std::shared_ptr<List<unsigned int>> rom_ext;
    unsigned int pc;
    unsigned int stack_len;
    unsigned int prom_addr_ext;
    unsigned int prom_data_ext;
    bool prom_enable_ext;
  };

  struct state_simple {
    std::shared_ptr<List<unsigned int>> rom_;
    unsigned int ptr_;
  };

  static std::shared_ptr<state> set_prom_params(const std::shared_ptr<state> &s,
                                                const unsigned int addr,
                                                const unsigned int data,
                                                const bool enable);
  static std::shared_ptr<state> execute_wpm(const std::shared_ptr<state> &s);
  static std::shared_ptr<state>
  load_program(std::shared_ptr<state> s, const unsigned int base,
               const std::shared_ptr<List<unsigned int>> &bytes);
  static std::shared_ptr<state_extended>
  set_prom_params_ext(const std::shared_ptr<state_extended> &s,
                      const unsigned int addr, const unsigned int data,
                      const bool enable);
  static std::shared_ptr<state_extended>
  execute_wpm_ext(const std::shared_ptr<state_extended> &s);
  static std::shared_ptr<state_simple>
  write_byte(const std::shared_ptr<state_simple> &s, const unsigned int b);
  static std::shared_ptr<state_simple>
  load_program_simple(std::shared_ptr<state_simple> s,
                      const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const bool test_load_program_nil = []() {
    std::shared_ptr<state> sample = std::make_shared<state>(
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false});
    std::shared_ptr<state> after =
        load_program(std::move(sample), 1u, List<unsigned int>::nil());
    return (ListDef::template nth<unsigned int>(0u, after->rom, 0u) == 10u &&
            (ListDef::template nth<unsigned int>(1u, after->rom, 0u) == 11u &&
             (ListDef::template nth<unsigned int>(2u, after->rom, 0u) == 12u &&
              ListDef::template nth<unsigned int>(3u, after->rom, 0u) == 13u)));
  }();
  static inline const bool test_load_program_cons_rom = []() {
    std::shared_ptr<state> sample = std::make_shared<state>(
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false});
    std::shared_ptr<state> after = load_program(
        std::move(sample), 1u,
        List<unsigned int>::cons(
            99u, List<unsigned int>::cons(88u, List<unsigned int>::nil())));
    return (ListDef::template nth<unsigned int>(0u, after->rom, 0u) == 10u &&
            (ListDef::template nth<unsigned int>(1u, after->rom, 0u) == 99u &&
             (ListDef::template nth<unsigned int>(2u, after->rom, 0u) == 88u &&
              ListDef::template nth<unsigned int>(3u, after->rom, 0u) == 13u)));
  }();
  static inline const bool test_load_preserves_rom_length = []() {
    std::shared_ptr<state> sample = std::make_shared<state>(
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false});
    std::shared_ptr<state> after =
        load_program(std::move(sample), 1u,
                     List<unsigned int>::cons(
                         99u, List<unsigned int>::cons(
                                  88u, List<unsigned int>::cons(
                                           77u, List<unsigned int>::nil()))));
    return std::move(after)->rom->length() == 4u;
  }();
  static inline const bool test_load_program_step_preserves_wf_simple = []() {
    std::shared_ptr<state_extended> sample =
        std::make_shared<state_extended>(state_extended{
            4u,
            List<unsigned int>::cons(
                10u, List<unsigned int>::cons(
                         11u, List<unsigned int>::cons(
                                  12u, List<unsigned int>::cons(
                                           13u, List<unsigned int>::nil())))),
            100u, 2u, 0u, 0u, false});
    std::shared_ptr<state_extended> after =
        execute_wpm_ext(set_prom_params_ext(std::move(sample), 1u, 99u, true));
    return (after->regs_len == 4u &&
            (after->rom_ext->length() == 4u &&
             (after->pc < 4096u && after->stack_len <= 3u)));
  }();
  static inline const bool test_load_program_step_rom_length_weak = []() {
    std::shared_ptr<state> sample = std::make_shared<state>(
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false});
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(std::move(sample), 1u, 99u, true));
    return std::move(after)->rom->length() == 4u;
  }();
  static inline const bool test_load_program_step_writes_at_base = []() {
    std::shared_ptr<state> sample = std::make_shared<state>(
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false});
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(std::move(sample), 1u, 99u, true));
    return ListDef::template nth<unsigned int>(1u, std::move(after)->rom, 0u) ==
           99u;
  }();
  static inline const unsigned int test_sequential_program_load = []() {
    std::shared_ptr<state_simple> sample =
        std::make_shared<state_simple>(state_simple{
            List<unsigned int>::cons(
                0u,
                List<unsigned int>::cons(
                    0u, List<unsigned int>::cons(
                            0u, List<unsigned int>::cons(
                                    0u, List<unsigned int>::cons(
                                            0u, List<unsigned int>::nil()))))),
            1u});
    return ListDef::template nth<unsigned int>(
        2u,
        load_program_simple(
            std::move(sample),
            List<unsigned int>::cons(
                5u, List<unsigned int>::cons(
                        6u, List<unsigned int>::cons(
                                7u, List<unsigned int>::nil()))))
            ->rom_,
        0u);
  }();
  static inline const std::pair<
      std::pair<
          std::pair<std::pair<std::pair<std::pair<bool, bool>, bool>, bool>,
                    bool>,
          bool>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(std::make_pair(test_load_program_nil,
                                                    test_load_program_cons_rom),
                                     test_load_preserves_rom_length),
                      test_load_program_step_preserves_wf_simple),
                  test_load_program_step_rom_length_weak),
              test_load_program_step_writes_at_base),
          test_sequential_program_load);
};

template <typename T1>
T1 ListDef::nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
      return ListDef::template nth<T1>(m, d_a10, default0);
    }
  }
}

#endif // INCLUDED_LOAD_PROGRAM
