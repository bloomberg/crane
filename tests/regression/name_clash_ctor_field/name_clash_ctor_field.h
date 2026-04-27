#ifndef INCLUDED_NAME_CLASH_CTOR_FIELD
#define INCLUDED_NAME_CLASH_CTOR_FIELD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NameClashCtorField {
  /// Fields named like structured binding names: d_a0, d_a1
  struct clash1 {
    // TYPES
    struct C1 {
      unsigned int d_d_a0;
      unsigned int d_d_a1;
    };

    using variant_t = std::variant<C1>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    clash1() {}

    explicit clash1(C1 _v) : d_v_(std::move(_v)) {}

    clash1(const clash1 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    clash1(clash1 &&_other) : d_v_(std::move(_other.d_v_)) {}

    clash1 &operator=(const clash1 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    clash1 &operator=(clash1 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) clash1 clone() const {
      auto &&_sv = *(this);
      const auto &[d_d_a0, d_d_a1] = std::get<C1>(_sv.v());
      return clash1(C1{d_d_a0, d_d_a1});
    }

    // CREATORS
    __attribute__((pure)) static clash1 c1(unsigned int d_a0,
                                           unsigned int d_a1) {
      return clash1(C1{std::move(d_a0), std::move(d_a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int sum_clash1() const {
      auto &&_sv = *(this);
      const auto &[d_d_a0, d_d_a1] = std::get<typename clash1::C1>(_sv.v());
      return (d_d_a0 + d_d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 clash1_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_d_a0, d_d_a1] = std::get<typename clash1::C1>(_sv.v());
      return f(d_d_a0, d_d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 clash1_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_d_a0, d_d_a1] = std::get<typename clash1::C1>(_sv.v());
      return f(d_d_a0, d_d_a1);
    }
  };

  /// Field named like the scrutinee variable
  struct clash2 {
    // TYPES
    struct C2a {
      unsigned int d_v;
    };

    struct C2b {
      unsigned int d_result;
    };

    using variant_t = std::variant<C2a, C2b>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    clash2() {}

    explicit clash2(C2a _v) : d_v_(std::move(_v)) {}

    explicit clash2(C2b _v) : d_v_(std::move(_v)) {}

    clash2(const clash2 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    clash2(clash2 &&_other) : d_v_(std::move(_other.d_v_)) {}

    clash2 &operator=(const clash2 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    clash2 &operator=(clash2 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) clash2 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<C2a>(_sv.v())) {
        const auto &[d_v] = std::get<C2a>(_sv.v());
        return clash2(C2a{d_v});
      } else {
        const auto &[d_result] = std::get<C2b>(_sv.v());
        return clash2(C2b{d_result});
      }
    }

    // CREATORS
    __attribute__((pure)) static clash2 c2a(unsigned int v) {
      return clash2(C2a{std::move(v)});
    }

    __attribute__((pure)) static clash2 c2b(unsigned int result) {
      return clash2(C2b{std::move(result)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int get_clash2() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename clash2::C2a>(_sv.v())) {
        const auto &[d_v] = std::get<typename clash2::C2a>(_sv.v());
        return d_v;
      } else {
        const auto &[d_result] = std::get<typename clash2::C2b>(_sv.v());
        return d_result;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 clash2_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename clash2::C2a>(_sv.v())) {
        const auto &[d_v] = std::get<typename clash2::C2a>(_sv.v());
        return f(d_v);
      } else {
        const auto &[d_result] = std::get<typename clash2::C2b>(_sv.v());
        return f0(d_result);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 clash2_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename clash2::C2a>(_sv.v())) {
        const auto &[d_v] = std::get<typename clash2::C2a>(_sv.v());
        return f(d_v);
      } else {
        const auto &[d_result] = std::get<typename clash2::C2b>(_sv.v());
        return f0(d_result);
      }
    }
  };

  /// Two constructors with fields, match on both in sequence
  struct pair_ind {
    // TYPES
    struct MkPair {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<MkPair>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pair_ind() {}

    explicit pair_ind(MkPair _v) : d_v_(std::move(_v)) {}

    pair_ind(const pair_ind &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair_ind(pair_ind &&_other) : d_v_(std::move(_other.d_v_)) {}

    pair_ind &operator=(const pair_ind &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    pair_ind &operator=(pair_ind &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pair_ind clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<MkPair>(_sv.v());
      return pair_ind(MkPair{d_a0, d_a1});
    }

    // CREATORS
    __attribute__((pure)) static pair_ind mkpair(unsigned int a0,
                                                 unsigned int a1) {
      return pair_ind(MkPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) pair_ind swap_pair() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename pair_ind::MkPair>(_sv.v());
      return pair_ind::mkpair(d_a1, d_a0);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_ind_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename pair_ind::MkPair>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_ind_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename pair_ind::MkPair>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  /// Nested match where inner and outer have same-named fields
  struct box {
    // TYPES
    struct Box0 {
      pair_ind d_a0;
    };

    struct EmptyBox {};

    using variant_t = std::variant<Box0, EmptyBox>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    box() {}

    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    explicit box(EmptyBox _v) : d_v_(_v) {}

    box(const box &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    box(box &&_other) : d_v_(std::move(_other.d_v_)) {}

    box &operator=(const box &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    box &operator=(box &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) box clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Box0>(_sv.v())) {
        const auto &[d_a0] = std::get<Box0>(_sv.v());
        return box(Box0{d_a0.clone()});
      } else {
        return box(EmptyBox{});
      }
    }

    // CREATORS
    __attribute__((pure)) static box box0(pair_ind a0) {
      return box(Box0{std::move(a0)});
    }

    __attribute__((pure)) static box emptybox() { return box(EmptyBox{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int unbox_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename box::Box0>(_sv.v())) {
        const auto &[d_a0] = std::get<typename box::Box0>(_sv.v());
        const auto &[d_a00, d_a10] =
            std::get<typename pair_ind::MkPair>(d_a0.v());
        return (d_a00 + d_a10);
      } else {
        return 0u;
      }
    }
  };

  template <typename T1, MapsTo<T1, pair_ind> F0>
  static T1 box_rect(F0 &&f, const T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, pair_ind> F0>
  static T1 box_rec(F0 &&f, const T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_CTOR_FIELD
