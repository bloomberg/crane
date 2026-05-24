#ifndef INCLUDED_ROCQ_BUG_7228
#define INCLUDED_ROCQ_BUG_7228

#include <any>
#include <memory>
#include <utility>
#include <variant>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct RocqBug7228 {
  struct data {
    // DATA
    std::any t;

    // ACCESSORS
    data clone() const { return {t}; }

    // CREATORS
    static data data0(std::any t) { return {std::move(t)}; }
  };

  template <typename T1, typename F0>
  static T1 data_rect(F0 &&f, const data &d) {
    const auto &[t0] = d;
    return std::any_cast<T1>(f(t0));
  }

  template <typename T1, typename F0>
  static T1 data_rec(F0 &&f, const data &d) {
    const auto &[t0] = d;
    return std::any_cast<T1>(f(t0));
  }

  using t_of = std::any;
  static t_of v_of(const data &d);
  static inline const data test_data =
      data::data0(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                          Nat::o())))))))))))))))))))))))))))))))))))))))))));
};

#endif // INCLUDED_ROCQ_BUG_7228
