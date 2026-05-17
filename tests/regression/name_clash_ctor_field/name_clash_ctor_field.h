#ifndef INCLUDED_NAME_CLASH_CTOR_FIELD
#define INCLUDED_NAME_CLASH_CTOR_FIELD

#include <type_traits>
#include <utility>
#include <variant>

struct NameClashCtorField {
  /// Fields named like structured binding names: d_a0, d_a1
  struct clash1 {
    // DATA
    unsigned int d_a0;
    unsigned int d_a1;

    // ACCESSORS
    clash1 clone() const { return {d_a0, d_a1}; }

    // CREATORS
    static clash1 c1(unsigned int d_a0, unsigned int d_a1) {
      return {d_a0, d_a1};
    }

    unsigned int sum_clash1() const {
      const auto &_sv = *this;
      const auto &[d_a0, d_a1] = _sv;
      return (d_a0 + d_a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
    T1 clash1_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[d_a2, d_a3] = _sv;
      return f(d_a2, d_a3);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
    T1 clash1_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[d_a2, d_a3] = _sv;
      return f(d_a2, d_a3);
    }
  };

  /// Field named like the scrutinee variable
  struct clash2 {
    // TYPES
    struct C2a {
      unsigned int v;
    };

    struct C2b {
      unsigned int result;
    };

    using variant_t = std::variant<C2a, C2b>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    clash2() {}

    explicit clash2(C2a _v) : v_(std::move(_v)) {}

    explicit clash2(C2b _v) : v_(std::move(_v)) {}

    clash2(const clash2 &_other) : v_(std::move(_other.clone().v_)) {}

    clash2(clash2 &&_other) noexcept : v_(std::move(_other.v_)) {}

    clash2 &operator=(const clash2 &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    clash2 &operator=(clash2 &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    clash2 clone() const {
      if (std::holds_alternative<C2a>(this->v())) {
        const auto &[v] = std::get<C2a>(this->v());
        return clash2(C2a{v});
      } else {
        const auto &[result] = std::get<C2b>(this->v());
        return clash2(C2b{result});
      }
    }

    // CREATORS
    static clash2 c2a(unsigned int v) { return clash2(C2a{v}); }

    static clash2 c2b(unsigned int result) { return clash2(C2b{result}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    unsigned int get_clash2() const {
      if (std::holds_alternative<typename clash2::C2a>(this->v())) {
        const auto &[v0] = std::get<typename clash2::C2a>(this->v());
        return v0;
      } else {
        const auto &[result] = std::get<typename clash2::C2b>(this->v());
        return result;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 clash2_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename clash2::C2a>(this->v())) {
        const auto &[v0] = std::get<typename clash2::C2a>(this->v());
        return f(v0);
      } else {
        const auto &[result0] = std::get<typename clash2::C2b>(this->v());
        return f0(result0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 clash2_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename clash2::C2a>(this->v())) {
        const auto &[v0] = std::get<typename clash2::C2a>(this->v());
        return f(v0);
      } else {
        const auto &[result0] = std::get<typename clash2::C2b>(this->v());
        return f0(result0);
      }
    }
  };

  /// Two constructors with fields, match on both in sequence
  struct pair_ind {
    // DATA
    unsigned int a0;
    unsigned int a1;

    // ACCESSORS
    pair_ind clone() const { return {a0, a1}; }

    // CREATORS
    static pair_ind mkpair(unsigned int a0, unsigned int a1) {
      return {a0, a1};
    }

    pair_ind swap_pair() const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return pair_ind::mkpair(a1, a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
    T1 pair_ind_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
    T1 pair_ind_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }
  };

  /// Nested match where inner and outer have same-named fields
  struct box {
    // TYPES
    struct Box0 {
      pair_ind a0;
    };

    struct EmptyBox {};

    using variant_t = std::variant<Box0, EmptyBox>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    box() {}

    explicit box(Box0 _v) : v_(std::move(_v)) {}

    explicit box(EmptyBox _v) : v_(_v) {}

    box(const box &_other) : v_(std::move(_other.clone().v_)) {}

    box(box &&_other) noexcept : v_(std::move(_other.v_)) {}

    box &operator=(const box &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    box &operator=(box &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    box clone() const {
      if (std::holds_alternative<Box0>(this->v())) {
        const auto &[a0] = std::get<Box0>(this->v());
        return box(Box0{a0.clone()});
      } else {
        return box(EmptyBox{});
      }
    }

    // CREATORS
    static box box0(pair_ind a0) { return box(Box0{std::move(a0)}); }

    static box emptybox() { return box(EmptyBox{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    unsigned int unbox_sum() const {
      if (std::holds_alternative<typename box::Box0>(this->v())) {
        const auto &[a0] = std::get<typename box::Box0>(this->v());
        const auto &[a00, a10] = a0;
        return (a00 + a10);
      } else {
        return 0u;
      }
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, pair_ind &>
  static T1 box_rect(F0 &&f, T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[a0] = std::get<typename box::Box0>(b.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, pair_ind &>
  static T1 box_rec(F0 &&f, T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[a0] = std::get<typename box::Box0>(b.v());
      return f(a0);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_CTOR_FIELD
