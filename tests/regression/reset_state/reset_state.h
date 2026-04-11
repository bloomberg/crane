#ifndef INCLUDED_RESET_STATE
#define INCLUDED_RESET_STATE

#include <memory>
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

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil) -> t_A { return default0; },
              [](const typename List<t_A>::Cons _args) -> t_A {
                return _args.d_a0;
              }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil) -> t_A { return default0; },
              [&](const typename List<t_A>::Cons _args0) -> t_A {
                return _args0.d_a1->nth(m, default0);
              }},
          this->v());
    }
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil) -> unsigned int { return 0u; },
            [](const typename List<t_A>::Cons _args) -> unsigned int {
              return (_args.d_a1->length() + 1);
            }},
        this->v());
  }
};

struct ResetState {
  struct state_full {
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> regs_full;
    bool carry;
    unsigned int pc_full;
    std::shared_ptr<List<unsigned int>> stack;
    std::shared_ptr<List<unsigned int>> ram_sys;
    std::shared_ptr<List<unsigned int>> rom;
  };

  struct state_minimal {
    std::shared_ptr<List<unsigned int>> regs_minimal;
    bool carry_minimal;
    unsigned int pc_minimal;
    std::shared_ptr<List<unsigned int>> ram_sys_minimal;
    std::shared_ptr<List<unsigned int>> rom_minimal;
  };

  static std::shared_ptr<state_full>
  reset_state_full(std::shared_ptr<state_full> s);
  static inline const unsigned int memory_preserve_test = []() {
    std::shared_ptr<state_full> s = std::make_shared<state_full>(state_full{
        9u,
        List<unsigned int>::cons(
            1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
        true, 55u,
        List<unsigned int>::cons(
            8u, List<unsigned int>::cons(7u, List<unsigned int>::nil())),
        List<unsigned int>::cons(
            3u,
            List<unsigned int>::cons(
                4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()))),
        List<unsigned int>::cons(
            10u, List<unsigned int>::cons(11u, List<unsigned int>::nil()))});
    std::shared_ptr<state_full> s_ = reset_state_full(std::move(s));
    return (((s_->acc + s_->ram_sys->nth(1u, 0u)) + s_->rom->nth(0u, 0u)) +
            s_->stack->length());
  }();
  static std::shared_ptr<state_minimal>
  reset_state_minimal(std::shared_ptr<state_minimal> s);
  static inline const unsigned int pc_clear_test =
      reset_state_minimal(
          std::make_shared<state_minimal>(state_minimal{
              List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
              true, 99u,
              List<unsigned int>::cons(3u, List<unsigned int>::nil()),
              List<unsigned int>::cons(
                  4u,
                  List<unsigned int>::cons(5u, List<unsigned int>::nil()))}))
          ->pc_minimal;
  static inline const std::pair<unsigned int, unsigned int> t =
      std::make_pair(memory_preserve_test, pc_clear_test);
};

#endif // INCLUDED_RESET_STATE
