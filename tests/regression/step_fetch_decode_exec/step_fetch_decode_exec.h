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
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
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
    explicit instruction(NOP _v) : d_v_(_v) {}

    explicit instruction(ADD_ACC _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    static std::shared_ptr<instruction> add_acc(unsigned int a0) {
      return std::make_shared<instruction>(ADD_ACC{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::NOP>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::ADD_ACC>(i->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0,
                            const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::NOP>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::ADD_ACC>(i->v());
      return f0(d_a0);
    }
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
  static std::shared_ptr<state> execute(const std::shared_ptr<state> &s,
                                        const std::shared_ptr<instruction> &i);
  static std::shared_ptr<state> step(const std::shared_ptr<state> &s);
  static inline const unsigned int t = []() {
    std::shared_ptr<state> s1 = step(std::make_shared<state>(
        state{3u, 0u,
              List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          6u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::nil())))}));
    return (s1->acc + s1->pc);
  }();
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

#endif // INCLUDED_STEP_FETCH_DECODE_EXEC
