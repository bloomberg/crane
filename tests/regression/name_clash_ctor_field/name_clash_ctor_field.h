#ifndef INCLUDED_NAME_CLASH_CTOR_FIELD
#define INCLUDED_NAME_CLASH_CTOR_FIELD

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
    explicit clash1(C1 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<clash1> c1(unsigned int d_a0, unsigned int d_a1) {
      return std::make_shared<clash1>(C1{std::move(d_a0), std::move(d_a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int sum_clash1() const {
      const auto &[d_d_a0, d_d_a1] = std::get<typename clash1::C1>(this->v());
      return (d_d_a0 + d_d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 clash1_rec(F0 &&f) const {
      const auto &[d_d_a0, d_d_a1] = std::get<typename clash1::C1>(this->v());
      return f(d_d_a0, d_d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 clash1_rect(F0 &&f) const {
      const auto &[d_d_a0, d_d_a1] = std::get<typename clash1::C1>(this->v());
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
    explicit clash2(C2a _v) : d_v_(std::move(_v)) {}

    explicit clash2(C2b _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<clash2> c2a(unsigned int v) {
      return std::make_shared<clash2>(C2a{std::move(v)});
    }

    static std::shared_ptr<clash2> c2b(unsigned int result) {
      return std::make_shared<clash2>(C2b{std::move(result)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int get_clash2() const {
      if (std::holds_alternative<typename clash2::C2a>(this->v())) {
        const auto &[d_v] = std::get<typename clash2::C2a>(this->v());
        return d_v;
      } else {
        const auto &[d_result] = std::get<typename clash2::C2b>(this->v());
        return d_result;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 clash2_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename clash2::C2a>(this->v())) {
        const auto &[d_v] = std::get<typename clash2::C2a>(this->v());
        return f(d_v);
      } else {
        const auto &[d_result] = std::get<typename clash2::C2b>(this->v());
        return f0(d_result);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 clash2_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename clash2::C2a>(this->v())) {
        const auto &[d_v] = std::get<typename clash2::C2a>(this->v());
        return f(d_v);
      } else {
        const auto &[d_result] = std::get<typename clash2::C2b>(this->v());
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
    explicit pair_ind(MkPair _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pair_ind> mkpair(unsigned int a0, unsigned int a1) {
      return std::make_shared<pair_ind>(MkPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<pair_ind> swap_pair() const {
      const auto &[d_a0, d_a1] = std::get<typename pair_ind::MkPair>(this->v());
      return pair_ind::mkpair(d_a1, d_a0);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_ind_rec(F0 &&f) const {
      const auto &[d_a0, d_a1] = std::get<typename pair_ind::MkPair>(this->v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_ind_rect(F0 &&f) const {
      const auto &[d_a0, d_a1] = std::get<typename pair_ind::MkPair>(this->v());
      return f(d_a0, d_a1);
    }
  };

  /// Nested match where inner and outer have same-named fields
  struct box {
    // TYPES
    struct Box0 {
      std::shared_ptr<pair_ind> d_a0;
    };

    struct EmptyBox {};

    using variant_t = std::variant<Box0, EmptyBox>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    explicit box(EmptyBox _v) : d_v_(_v) {}

    static std::shared_ptr<box> box0(const std::shared_ptr<pair_ind> &a0) {
      return std::make_shared<box>(Box0{a0});
    }

    static std::shared_ptr<box> box0(std::shared_ptr<pair_ind> &&a0) {
      return std::make_shared<box>(Box0{std::move(a0)});
    }

    static std::shared_ptr<box> emptybox() {
      return std::make_shared<box>(EmptyBox{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int unbox_sum() const {
      if (std::holds_alternative<typename box::Box0>(this->v())) {
        const auto &[d_a0] = std::get<typename box::Box0>(this->v());
        const auto &[d_a00, d_a10] =
            std::get<typename pair_ind::MkPair>(d_a0->v());
        return (d_a00 + d_a10);
      } else {
        return 0u;
      }
    }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<pair_ind>> F0>
  static T1 box_rect(F0 &&f, const T1 f0, const std::shared_ptr<box> &b) {
    if (std::holds_alternative<typename box::Box0>(b->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<pair_ind>> F0>
  static T1 box_rec(F0 &&f, const T1 f0, const std::shared_ptr<box> &b) {
    if (std::holds_alternative<typename box::Box0>(b->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return f(d_a0);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_CTOR_FIELD
