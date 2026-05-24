#ifndef INCLUDED_WELL_FOUNDED_REC
#define INCLUDED_WELL_FOUNDED_REC

#include <any>
#include <memory>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct WellFoundedRec {
  static List<uint64_t> countdown_acc(uint64_t n);
  static List<uint64_t> countdown(uint64_t _x0);
  static uint64_t div2_wf(uint64_t x);
  static uint64_t gcd_wf(uint64_t x, uint64_t b);
  static inline const uint64_t test_div2_0 = div2_wf(UINT64_C(0));
  static inline const uint64_t test_div2_1 = div2_wf(UINT64_C(1));
  static inline const uint64_t test_div2_7 = div2_wf(UINT64_C(7));
  static inline const uint64_t test_div2_10 = div2_wf(UINT64_C(10));
  static inline const List<uint64_t> test_countdown = countdown(UINT64_C(5));
  static inline const uint64_t test_gcd_1 = gcd_wf(UINT64_C(12), UINT64_C(8));
  static inline const uint64_t test_gcd_2 = gcd_wf(UINT64_C(35), UINT64_C(14));
  static inline const uint64_t test_gcd_3 = gcd_wf(UINT64_C(0), UINT64_C(5));
};

#endif // INCLUDED_WELL_FOUNDED_REC
