#ifndef INCLUDED_MOVE_CAPTURE_REUSE
#define INCLUDED_MOVE_CAPTURE_REUSE

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

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<T1>::cons(f(d_a0), d_a1->template map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
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

struct MoveCaptureReuse {
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> prefix_each(
      std::shared_ptr<List<unsigned int>> prefix,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss);
  static inline const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
      sample = prefix_each(
          List<unsigned int>::cons(1u, List<unsigned int>::nil()),
          List<std::shared_ptr<List<unsigned int>>>::cons(
              List<unsigned int>::cons(10u, List<unsigned int>::nil()),
              List<std::shared_ptr<List<unsigned int>>>::cons(
                  List<unsigned int>::cons(20u, List<unsigned int>::nil()),
                  List<std::shared_ptr<List<unsigned int>>>::nil())));
  static inline const unsigned int len_sum = []() {
    auto &&_sv = sample;
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
            _sv->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _sv->v());
      if (std::holds_alternative<
              typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
              d_a1->v())) {
        return 0u;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                d_a1->v());
        return (d_a0->length() + d_a00->length());
      }
    }
  }();
};

#endif // INCLUDED_MOVE_CAPTURE_REUSE
