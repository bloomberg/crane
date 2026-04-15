#ifndef INCLUDED_LIST
#define INCLUDED_LIST

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

  t_A last(const t_A x) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return x;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return d_a1->last(d_a0);
    }
  }

  t_A hd(const t_A x) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return x;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return d_a0;
    }
  }

  template <typename T1, MapsTo<T1, t_A, std::shared_ptr<List<t_A>>, T1> F1>
  T1 list_rec(const T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return f0(d_a0, d_a1, d_a1->template list_rec<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, t_A, std::shared_ptr<List<t_A>>, T1> F1>
  T1 list_rect(const T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return f0(d_a0, d_a1, d_a1->template list_rect<T1>(f, f0));
    }
  }

  std::shared_ptr<List<t_A>> tl() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return d_a1;
    }
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> l2) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return l2;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(l2));
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<T1>::cons(f(d_a0), d_a1->template map<T1>(f));
    }
  }

  static const std::shared_ptr<List<unsigned int>> &mytest() {
    static const std::shared_ptr<List<unsigned int>> v =
        List<unsigned int>::cons(
            3u,
            List<unsigned int>::cons(
                1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())))
            ->app(List<unsigned int>::cons(
                8u, List<unsigned int>::cons(
                        3u, List<unsigned int>::cons(
                                7u, List<unsigned int>::cons(
                                        9u, List<unsigned int>::nil())))));
    return v;
  }
};

#endif // INCLUDED_LIST
