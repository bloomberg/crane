#ifndef INCLUDED_REGION_PATCH_WRITE
#define INCLUDED_REGION_PATCH_WRITE

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
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       return _args.d_a0;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args0) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args0) -> t_A {
                       return _args0.d_a1->nth(m, default0);
                     }},
          this->v());
    }
  }
};

struct RegionPatchWrite {
  static std::shared_ptr<List<unsigned int>>
  update_region(const std::shared_ptr<List<unsigned int>> &rom,
                const unsigned int base,
                std::shared_ptr<List<unsigned int>> bytes);
  static inline const unsigned int t =
      update_region(
          List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      0u, List<unsigned int>::cons(
                              0u, List<unsigned int>::cons(
                                      0u, List<unsigned int>::nil())))),
          1u,
          List<unsigned int>::cons(
              7u, List<unsigned int>::cons(8u, List<unsigned int>::nil())))
          ->nth(2u, 0u);
};

#endif // INCLUDED_REGION_PATCH_WRITE
