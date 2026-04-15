#ifndef INCLUDED_TAIL_REC_REV
#define INCLUDED_TAIL_REC_REV

#include <functional>
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

template <typename T1>
std::shared_ptr<List<T1>> better_rev(const std::shared_ptr<List<T1>> &l) {
  std::function<std::shared_ptr<List<T1>>(std::shared_ptr<List<T1>>,
                                          std::shared_ptr<List<T1>>)>
      go;
  go = [&](std::shared_ptr<List<T1>> l0,
           std::shared_ptr<List<T1>> acc) -> std::shared_ptr<List<T1>> {
    if (std::holds_alternative<typename List<T1>::Nil>(l0->v())) {
      return acc;
    } else {
      const auto &_m = *std::get_if<typename List<T1>::Cons>(&l0->v());
      return go(_m.d_a1, List<T1>::cons(_m.d_a0, acc));
    }
  };
  return go(l, List<T1>::nil());
}

#endif // INCLUDED_TAIL_REC_REV
