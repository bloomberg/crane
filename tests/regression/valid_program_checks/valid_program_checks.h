#ifndef INCLUDED_VALID_PROGRAM_CHECKS
#define INCLUDED_VALID_PROGRAM_CHECKS

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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil) -> bool { return true; },
                   [&](const typename List<t_A>::Cons _args) -> bool {
                     return (f(_args.d_a0) && _args.d_a1->forallb(f));
                   }},
        this->v());
  }

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

struct ValidProgramChecks {
  __attribute__((pure)) static bool
  valid_program(const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const unsigned int t = ([]() -> unsigned int {
    if (valid_program(List<unsigned int>::cons(
            1u, List<unsigned int>::cons(
                    2u, List<unsigned int>::cons(
                            3u, List<unsigned int>::cons(
                                    4u, List<unsigned int>::nil())))))) {
      return 1u;
    } else {
      return 0u;
    }
  }() + []() -> unsigned int {
    if (valid_program(List<unsigned int>::cons(
            1u, List<unsigned int>::cons(
                    2u, List<unsigned int>::cons(
                            300u, List<unsigned int>::nil()))))) {
      return 1u;
    } else {
      return 0u;
    }
  }());
};

#endif // INCLUDED_VALID_PROGRAM_CHECKS
