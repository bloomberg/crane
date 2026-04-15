#ifndef INCLUDED_TAIL_REC_ZIP
#define INCLUDED_TAIL_REC_ZIP

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

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Prod<t_A, t_B>> pair(t_A a0, t_B a1) {
    return std::make_shared<Prod<t_A, t_B>>(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

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

  std::shared_ptr<List<t_A>> rev() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return d_a1->rev()->app(List<t_A>::cons(d_a0, List<t_A>::nil()));
    }
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(m));
    }
  }
};

template <typename T1, typename T2>
std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>>
better_zip(const std::shared_ptr<List<T1>> &la,
           const std::shared_ptr<List<T2>> &lb) {
  std::function<std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>>(
      std::shared_ptr<List<T1>>, std::shared_ptr<List<T2>>,
      std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>>)>
      go;
  go = [&](std::shared_ptr<List<T1>> la0, std::shared_ptr<List<T2>> lb0,
           std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>> acc)
      -> std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>> {
    if (std::holds_alternative<typename List<T1>::Nil>(la0->v())) {
      return std::move(acc)->rev();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(la0->v());
      if (std::holds_alternative<typename List<T2>::Nil>(lb0->v())) {
        return std::move(acc)->rev();
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<T2>::Cons>(lb0->v());
        return go(d_a1, d_a10,
                  List<std::shared_ptr<Prod<T1, T2>>>::cons(
                      Prod<T1, T2>::pair(d_a0, d_a00), acc));
      }
    }
  };
  return go(la, lb, List<std::shared_ptr<Prod<T1, T2>>>::nil());
}

#endif // INCLUDED_TAIL_REC_ZIP
