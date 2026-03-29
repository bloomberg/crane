#ifndef INCLUDED_STEP_FETCH_DECODE_EXEC
#define INCLUDED_STEP_FETCH_DECODE_EXEC

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

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       return _args.d_a0;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args0) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args0) -> t_A {
                       return _args0.d_a1->nth(m, default0);
                     }},
          this->v());
    }
  }
};

struct StepFetchDecodeExec {
  struct instruction {
    // TYPES
    struct NOP {};

    struct ADD_ACC {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP, ADD_ACC>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

    explicit instruction(ADD_ACC _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    static std::shared_ptr<instruction> add_acc(unsigned int a0) {
      return std::make_shared<instruction>(ADD_ACC{std::move(a0)});
    }

    static std::unique_ptr<instruction> nop_uptr() {
      return std::make_unique<instruction>(NOP{});
    }

    static std::unique_ptr<instruction> add_acc_uptr(unsigned int a0) {
      return std::make_unique<instruction>(ADD_ACC{std::move(a0)});
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
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              return f0(_args.d_a0);
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              return f0(_args.d_a0);
            }},
        i->v());
  }

  struct state {
    unsigned int acc;
    unsigned int pc;
    std::shared_ptr<List<unsigned int>> rom;
  };

  __attribute__((pure)) static unsigned int
  fetch_byte(const std::shared_ptr<state> &s, const unsigned int addr);
  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);
  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const std::shared_ptr<instruction> &i);
  static std::shared_ptr<state> step(const std::shared_ptr<state> &s);
  static inline const unsigned int t = [](void) {
    std::shared_ptr<state> s1 = step(std::make_shared<state>(
        state{3u, 0u,
              List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          6u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::nil())))}));
    return (s1->acc + s1->pc);
  }();
};

#endif // INCLUDED_STEP_FETCH_DECODE_EXEC
