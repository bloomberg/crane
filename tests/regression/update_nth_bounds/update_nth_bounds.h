#ifndef INCLUDED_UPDATE_NTH_BOUNDS
#define INCLUDED_UPDATE_NTH_BOUNDS

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

template <typename t_A>
struct List : public std::enable_shared_from_this<List<t_A>> {
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

  std::shared_ptr<List<t_A>> skipn(const unsigned int n) const {
    if (n <= 0) {
      return std::const_pointer_cast<List<t_A>>(this->shared_from_this());
    } else {
      unsigned int n0 = n - 1;
      return std::visit(Overloaded{[](const typename List<t_A>::Nil _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     return List<t_A>::nil();
                                   },
                                   [&](const typename List<t_A>::Cons _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     return _args.d_a1->skipn(n0);
                                   }},
                        this->v());
    }
  }

  std::shared_ptr<List<t_A>> firstn(const unsigned int n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int n0 = n - 1;
      return std::visit(
          Overloaded{
              [](const typename List<t_A>::Nil _args)
                  -> std::shared_ptr<List<t_A>> { return List<t_A>::nil(); },
              [&](const typename List<t_A>::Cons _args)
                  -> std::shared_ptr<List<t_A>> {
                return List<t_A>::cons(_args.d_a0, _args.d_a1->firstn(n0));
              }},
          this->v());
    }
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::cons(_args.d_a0, _args.d_a1->app(m));
                   }},
        this->v());
  }
};

struct UpdateNthBounds {
  template <typename T1>
  static std::shared_ptr<List<T1>> update_nth(const unsigned int n, const T1 x,
                                              std::shared_ptr<List<T1>> l) {
    if (n < l->length()) {
      return l->firstn(n)->app(List<T1>::cons(x, l->skipn((n + 1))));
    } else {
      return std::move(l);
    }
  }

  static inline const unsigned int in_bounds_length =
      update_nth<unsigned int>(
          2u, 9u,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))))
          ->length();
  static inline const unsigned int out_of_bounds_length =
      update_nth<unsigned int>(
          9u, 7u,
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))))
          ->length();
};

#endif // INCLUDED_UPDATE_NTH_BOUNDS
