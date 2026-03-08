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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct ComputationalProof {
  static bool nat_eq_dec(const unsigned int n, const unsigned int x);

  static bool nat_eqb_dec(const unsigned int n, const unsigned int m);

  static bool le_dec(const unsigned int n, const unsigned int m);

  static bool nat_leb_dec(const unsigned int n, const unsigned int m);

  static unsigned int min_dec(const unsigned int n, const unsigned int m);

  static unsigned int max_dec(const unsigned int n, const unsigned int m);

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
      isort_dec(List<unsigned int>::ctor::cons_(
          5u,
          List<unsigned int>::ctor::cons_(
              1u,
              List<unsigned int>::ctor::cons_(
                  4u, List<unsigned int>::ctor::cons_(
                          2u, List<unsigned int>::ctor::cons_(
                                  3u, List<unsigned int>::ctor::nil_()))))));
};
