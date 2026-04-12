#ifndef INCLUDED_WRR_PRESERVES_OTHER_PORTS
#define INCLUDED_WRR_PRESERVES_OTHER_PORTS

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

struct WrrPreservesOtherPorts {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(
          Overloaded{
              [](const typename List<T1>::Nil &) -> std::shared_ptr<List<T1>> {
                return List<T1>::nil();
              },
              [&](const typename List<T1>::Cons &_args)
                  -> std::shared_ptr<List<T1>> {
                return List<T1>::cons(x, _args.d_a1);
              }},
          l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(
          Overloaded{
              [](const typename List<T1>::Nil &) -> std::shared_ptr<List<T1>> {
                return List<T1>::nil();
              },
              [&](const typename List<T1>::Cons &_args0)
                  -> std::shared_ptr<List<T1>> {
                return List<T1>::cons(_args0.d_a0,
                                      update_nth<T1>(n_, x, _args0.d_a1));
              }},
          l->v());
    }
  }

  struct state {
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> rom_ports;
    unsigned int sel_rom;
  };

  static std::shared_ptr<state> execute_wrr(const std::shared_ptr<state> &s);
  static inline const std::shared_ptr<state> sample = std::make_shared<state>(
      state{11u,
            List<unsigned int>::cons(
                1u, List<unsigned int>::cons(
                        2u, List<unsigned int>::cons(
                                3u, List<unsigned int>::cons(
                                        4u, List<unsigned int>::nil())))),
            2u});
  static inline const bool t =
      execute_wrr(sample)->rom_ports->nth(0u, 0u) == 1u;
};

#endif // INCLUDED_WRR_PRESERVES_OTHER_PORTS
