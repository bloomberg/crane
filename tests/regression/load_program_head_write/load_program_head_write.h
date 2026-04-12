#ifndef INCLUDED_LOAD_PROGRAM_HEAD_WRITE
#define INCLUDED_LOAD_PROGRAM_HEAD_WRITE

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
              [&](const typename List<t_A>::Nil &) -> t_A { return default0; },
              [](const typename List<t_A>::Cons &_args) -> t_A {
                return _args.d_a0;
              }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil &) -> t_A { return default0; },
              [&](const typename List<t_A>::Cons &_args0) -> t_A {
                return _args0.d_a1->nth(m, default0);
              }},
          this->v());
    }
  }
};

struct LoadProgramHeadWrite {
  struct state {
    std::shared_ptr<List<unsigned int>> rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;
  };

  static std::shared_ptr<List<unsigned int>>
  update_nth(const unsigned int n, const unsigned int x,
             std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<state> set_prom_params(const std::shared_ptr<state> &s,
                                                const unsigned int addr,
                                                const unsigned int data,
                                                const bool enable);
  static std::shared_ptr<state> execute_wpm(const std::shared_ptr<state> &s);
  static std::shared_ptr<state>
  load_program(std::shared_ptr<state> s, const unsigned int base,
               const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const unsigned int t = []() {
    std::shared_ptr<state> s0 = std::make_shared<state>(
        state{List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil())))),
              0u, 0u, false});
    std::shared_ptr<state> s1 = load_program(
        std::move(s0), 1u,
        List<unsigned int>::cons(
            7u, List<unsigned int>::cons(8u, List<unsigned int>::nil())));
    return std::move(s1)->rom->nth(1u, 0u);
  }();
};

#endif // INCLUDED_LOAD_PROGRAM_HEAD_WRITE
