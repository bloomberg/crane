#ifndef INCLUDED_ROCQ_BUG_7228
#define INCLUDED_ROCQ_BUG_7228

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RocqBug7228 {
  struct data {
    // TYPES
    struct Data0 {
      std::any d_t;
    };

    using variant_t = std::variant<Data0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit data(Data0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<data> data0(std::any t) {
      return std::make_shared<data>(Data0{std::move(t)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0>
  static T1 data_rect(F0 &&f, const std::shared_ptr<data> &d) {
    const auto &[d_t] = std::get<typename data::Data0>(d->v());
    return std::any_cast<T1>(f(d_t));
  }

  template <typename T1, typename F0>
  static T1 data_rec(F0 &&f, const std::shared_ptr<data> &d) {
    const auto &[d_t] = std::get<typename data::Data0>(d->v());
    return std::any_cast<T1>(f(d_t));
  }

  using t_of = std::any;
  __attribute__((pure)) static t_of v_of(const std::shared_ptr<data> &d);
  static inline const std::shared_ptr<data> test_data =
      data::data0(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                          Nat::o())))))))))))))))))))))))))))))))))))))))))));
};

#endif // INCLUDED_ROCQ_BUG_7228
