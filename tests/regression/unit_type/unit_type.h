#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Unit {
  struct unit {
  public:
    struct tt {};
    using variant_t = std::variant<tt>;

  private:
    variant_t v_;
    explicit unit(tt _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Unit::unit> tt_() {
        return std::shared_ptr<Unit::unit>(new Unit::unit(tt{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct UnitType {
  static inline const std::shared_ptr<Unit::unit> unit_val =
      Unit::unit::ctor::tt_();

  static std::shared_ptr<Unit::unit> return_unit(const unsigned int _x);

  static unsigned int take_unit(const std::shared_ptr<Unit::unit> &_x);

  static unsigned int match_unit(const std::shared_ptr<Unit::unit> &u);

  template <typename A, typename B> struct pair {
  public:
    struct Pair {
      A _a0;
      B _a1;
    };
    using variant_t = std::variant<Pair>;

  private:
    variant_t v_;
    explicit pair(Pair _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<pair<A, B>> Pair_(A a0, B a1) {
        return std::shared_ptr<pair<A, B>>(new pair<A, B>(Pair{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  static inline const std::shared_ptr<
      pair<unsigned int, std::shared_ptr<Unit::unit>>>
      pair_with_unit =
          pair<unsigned int, std::shared_ptr<Unit::unit>>::ctor::Pair_(
              3u, Unit::unit::ctor::tt_());

  static inline const std::shared_ptr<
      pair<std::shared_ptr<Unit::unit>, std::shared_ptr<Unit::unit>>>
      unit_pair =
          pair<std::shared_ptr<Unit::unit>, std::shared_ptr<Unit::unit>>::ctor::
              Pair_(Unit::unit::ctor::tt_(), Unit::unit::ctor::tt_());

  static std::shared_ptr<Unit::unit>
  unit_to_unit(const std::shared_ptr<Unit::unit> &u);

  template <typename T1, typename T2> static T2 seq(const T1 _x, const T2 b) {
    return b;
  }

  static inline const unsigned int sequenced =
      seq<std::shared_ptr<Unit::unit>, unsigned int>(
          Unit::unit::ctor::tt_(),
          seq<std::shared_ptr<Unit::unit>, unsigned int>(
              Unit::unit::ctor::tt_(), 5u));

  static inline const unsigned int test_take =
      take_unit(Unit::unit::ctor::tt_());

  static inline const unsigned int test_match =
      match_unit(Unit::unit::ctor::tt_());

  static inline const unsigned int test_seq = sequenced;
};
