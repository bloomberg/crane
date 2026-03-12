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

  A nth(const unsigned int n, const A default0) const {
    if (n <= 0) {
      return std::visit(Overloaded{[&](const typename List<A>::nil _args) -> A {
                                     return default0;
                                   },
                                   [](const typename List<A>::cons _args) -> A {
                                     A x = _args._a0;
                                     return x;
                                   }},
                        this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<A>::nil _args) -> A { return default0; },
              [&](const typename List<A>::cons _args) -> A {
                std::shared_ptr<List<A>> l_ = _args._a1;
                return std::move(l_)->nth(m, default0);
              }},
          this->v());
    }
  }

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

struct LoadProgram {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args._a0;
                                     std::shared_ptr<List<T1>> ys = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(ys)));
                                   }},
                        l->v());
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

  static std::shared_ptr<state> set_prom_params(std::shared_ptr<state> s,
                                                const unsigned int addr,
                                                const unsigned int data,
                                                const bool enable);
  static std::shared_ptr<state> execute_wpm(std::shared_ptr<state> s);
  static std::shared_ptr<state>
  load_program(std::shared_ptr<state> s, const unsigned int base,
               const std::shared_ptr<List<unsigned int>> &bytes);
  static std::shared_ptr<state_extended>
  set_prom_params_ext(std::shared_ptr<state_extended> s,
                      const unsigned int addr, const unsigned int data,
                      const bool enable);
  static std::shared_ptr<state_extended>
  execute_wpm_ext(std::shared_ptr<state_extended> s);
  static std::shared_ptr<state_simple>
  write_byte(std::shared_ptr<state_simple> s, const unsigned int b);
  static std::shared_ptr<state_simple>
  load_program_simple(std::shared_ptr<state_simple> s,
                      const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const bool test_load_program_nil = [](void) {
    std::unique_ptr<state> sample = std::make_unique<state>(state{
        List<unsigned int>::ctor::cons_(
            10u,
            List<unsigned int>::ctor::cons_(
                11u, List<unsigned int>::ctor::cons_(
                         12u, List<unsigned int>::ctor::cons_(
                                  13u, List<unsigned int>::ctor::nil_())))),
        0u, 0u, false});
    std::shared_ptr<state> after =
        load_program(std::move(sample), 1u, List<unsigned int>::ctor::nil_());
    return ((after->rom->nth(0u, 0u) == 10u) &&
            ((after->rom->nth(1u, 0u) == 11u) &&
             ((after->rom->nth(2u, 0u) == 12u) &&
              (after->rom->nth(3u, 0u) == 13u))));
  }();
  static inline const bool test_load_program_cons_rom = [](void) {
    std::unique_ptr<state> sample = std::make_unique<state>(state{
        List<unsigned int>::ctor::cons_(
            10u,
            List<unsigned int>::ctor::cons_(
                11u, List<unsigned int>::ctor::cons_(
                         12u, List<unsigned int>::ctor::cons_(
                                  13u, List<unsigned int>::ctor::nil_())))),
        0u, 0u, false});
    std::shared_ptr<state> after =
        load_program(std::move(sample), 1u,
                     List<unsigned int>::ctor::cons_(
                         99u, List<unsigned int>::ctor::cons_(
                                  88u, List<unsigned int>::ctor::nil_())));
    return ((after->rom->nth(0u, 0u) == 10u) &&
            ((after->rom->nth(1u, 0u) == 99u) &&
             ((after->rom->nth(2u, 0u) == 88u) &&
              (after->rom->nth(3u, 0u) == 13u))));
  }();
  static inline const bool test_load_preserves_rom_length = [](void) {
    std::unique_ptr<state> sample = std::make_unique<state>(state{
        List<unsigned int>::ctor::cons_(
            10u,
            List<unsigned int>::ctor::cons_(
                11u, List<unsigned int>::ctor::cons_(
                         12u, List<unsigned int>::ctor::cons_(
                                  13u, List<unsigned int>::ctor::nil_())))),
        0u, 0u, false});
    std::shared_ptr<state> after = load_program(
        std::move(sample), 1u,
        List<unsigned int>::ctor::cons_(
            99u, List<unsigned int>::ctor::cons_(
                     88u, List<unsigned int>::ctor::cons_(
                              77u, List<unsigned int>::ctor::nil_()))));
    return (std::move(after)->rom->length() == 4u);
  }();
  static inline const bool test_load_program_step_preserves_wf_simple =
      [](void) {
        std::unique_ptr<state_extended> sample =
            std::make_unique<state_extended>(state_extended{
                4u,
                List<unsigned int>::ctor::cons_(
                    10u,
                    List<unsigned int>::ctor::cons_(
                        11u,
                        List<unsigned int>::ctor::cons_(
                            12u, List<unsigned int>::ctor::cons_(
                                     13u, List<unsigned int>::ctor::nil_())))),
                100u, 2u, 0u, 0u, false});
        std::shared_ptr<state_extended> after = execute_wpm_ext(
            set_prom_params_ext(std::move(sample), 1u, 99u, true));
        return ((after->regs_len == 4u) &&
                ((after->rom_ext->length() == 4u) &&
                 ((after->pc < 4096u) && (after->stack_len <= 3u))));
      }();
  static inline const bool test_load_program_step_rom_length_weak = [](void) {
    std::unique_ptr<state> sample = std::make_unique<state>(state{
        List<unsigned int>::ctor::cons_(
            10u,
            List<unsigned int>::ctor::cons_(
                11u, List<unsigned int>::ctor::cons_(
                         12u, List<unsigned int>::ctor::cons_(
                                  13u, List<unsigned int>::ctor::nil_())))),
        0u, 0u, false});
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(std::move(sample), 1u, 99u, true));
    return (std::move(after)->rom->length() == 4u);
  }();
  static inline const bool test_load_program_step_writes_at_base = [](void) {
    std::unique_ptr<state> sample = std::make_unique<state>(state{
        List<unsigned int>::ctor::cons_(
            10u,
            List<unsigned int>::ctor::cons_(
                11u, List<unsigned int>::ctor::cons_(
                         12u, List<unsigned int>::ctor::cons_(
                                  13u, List<unsigned int>::ctor::nil_())))),
        0u, 0u, false});
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(std::move(sample), 1u, 99u, true));
    return (std::move(after)->rom->nth(1u, 0u) == 99u);
  }();
  static inline const unsigned int test_sequential_program_load = [](void) {
    std::unique_ptr<state_simple> sample =
        std::make_unique<state_simple>(state_simple{
            List<unsigned int>::ctor::cons_(
                0u,
                List<unsigned int>::ctor::cons_(
                    0u,
                    List<unsigned int>::ctor::cons_(
                        0u,
                        List<unsigned int>::ctor::cons_(
                            0u, List<unsigned int>::ctor::cons_(
                                    0u, List<unsigned int>::ctor::nil_()))))),
            1u});
    return load_program_simple(
               std::move(sample),
               List<unsigned int>::ctor::cons_(
                   5u, List<unsigned int>::ctor::cons_(
                           6u, List<unsigned int>::ctor::cons_(
                                   7u, List<unsigned int>::ctor::nil_()))))
        ->rom_->nth(2u, 0u);
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
