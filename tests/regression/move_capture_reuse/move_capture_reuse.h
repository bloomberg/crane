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
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil &)
                       -> std::shared_ptr<List<T1>> { return List<T1>::nil(); },
                   [&](const typename List<t_A>::Cons &_args)
                       -> std::shared_ptr<List<T1>> {
                     return List<T1>::cons(f(_args.d_a0),
                                           _args.d_a1->template map<T1>(f));
                   }},
        this->v());
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil &) -> unsigned int { return 0u; },
            [](const typename List<t_A>::Cons &_args) -> unsigned int {
              return (_args.d_a1->length() + 1);
            }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil &)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons &_args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::cons(_args.d_a0, _args.d_a1->app(m));
                   }},
        this->v());
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
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<List<unsigned int>>>::Nil &)
                -> unsigned int { return 0u; },
            [](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                   &_args) -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil &)
                          -> unsigned int { return 0u; },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args0)
                          -> unsigned int {
                        return (_args.d_a0->length() + _args0.d_a0->length());
                      }},
                  _args.d_a1->v());
            }},
        sample->v());
  }();
};

#endif // INCLUDED_MOVE_CAPTURE_REUSE
