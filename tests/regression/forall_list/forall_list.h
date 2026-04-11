#ifndef INCLUDED_FORALL_LIST
#define INCLUDED_FORALL_LIST

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

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil) -> unsigned int { return 0u; },
            [](const typename List<t_A>::Cons _args) -> unsigned int {
              return (_args.d_a1->length() + 1);
            }},
        this->v());
  }
};

struct ForallList {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(
          Overloaded{
              [](const typename List<T1>::Nil) -> std::shared_ptr<List<T1>> {
                return List<T1>::nil();
              },
              [&](const typename List<T1>::Cons _args)
                  -> std::shared_ptr<List<T1>> {
                return List<T1>::cons(x, _args.d_a1);
              }},
          l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(
          Overloaded{
              [](const typename List<T1>::Nil) -> std::shared_ptr<List<T1>> {
                return List<T1>::nil();
              },
              [&](const typename List<T1>::Cons _args0)
                  -> std::shared_ptr<List<T1>> {
                return List<T1>::cons(_args0.d_a0,
                                      update_nth<T1>(n_, x, _args0.d_a1));
              }},
          l->v());
    }
  }

  static inline const std::shared_ptr<List<unsigned int>> sample =
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::nil()))));
  static inline const unsigned int updated_length =
      update_nth<unsigned int>(1u, 9u, sample)->length();
};

#endif // INCLUDED_FORALL_LIST
