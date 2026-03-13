#ifndef INCLUDED_COMPUTATIONAL_PROOF
#define INCLUDED_COMPUTATIONAL_PROOF

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct ComputationalProof {
  __attribute__((pure)) static bool nat_eq_dec(const unsigned int n,
                                               const unsigned int x);
  __attribute__((pure)) static bool nat_eqb_dec(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static bool le_dec(const unsigned int n,
                                           const unsigned int m);
  __attribute__((pure)) static bool nat_leb_dec(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static unsigned int min_dec(const unsigned int n,
                                                    const unsigned int m);
  __attribute__((pure)) static unsigned int max_dec(const unsigned int n,
                                                    const unsigned int m);
  static std::shared_ptr<List<unsigned int>>
  insert_dec(const unsigned int x,
             const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  isort_dec(const std::shared_ptr<List<unsigned int>> &l);
  static inline const bool test_eq_true = nat_eqb_dec(5u, 5u);
  static inline const bool test_eq_false = nat_eqb_dec(3u, 7u);
  static inline const bool test_leb_true = nat_leb_dec(3u, 5u);
  static inline const bool test_leb_false = nat_leb_dec(8u, 2u);
  static inline const unsigned int test_min = min_dec(4u, 9u);
  static inline const unsigned int test_max = max_dec(4u, 9u);
  static inline const std::shared_ptr<List<unsigned int>> test_sort =
      isort_dec(List<unsigned int>::ctor::Cons_(
          5u,
          List<unsigned int>::ctor::Cons_(
              1u,
              List<unsigned int>::ctor::Cons_(
                  4u, List<unsigned int>::ctor::Cons_(
                          2u, List<unsigned int>::ctor::Cons_(
                                  3u, List<unsigned int>::ctor::Nil_()))))));
};

#endif // INCLUDED_COMPUTATIONAL_PROOF
