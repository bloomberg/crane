#ifndef INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
#define INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SimpleLambdaFieldCapture {
  /// Control test: a SIMPLE lambda (not a local fixpoint) captures
  /// pattern variables from a match on a value-type inductive.
  ///
  /// Simple lambdas should use = capture, so this SHOULD be safe.
  /// If this test fails, it means even simple lambdas have the
  /// dangling capture bug.
  struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      unsigned int d_a0;
      std::unique_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist &operator=(const mylist &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist(Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist(Mycons{
            d_a0, d_a1 ? std::make_unique<SimpleLambdaFieldCapture::mylist>(
                             d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist mycons(unsigned int a0,
                                               const mylist &a1) {
      return mylist(Mycons{std::move(a0), std::make_unique<mylist>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist *operator->() { return this; }

    __attribute__((pure)) const mylist *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Simple lambda captures h and t from match.
    /// Should use = capture (safe).
    __attribute__((pure))
    std::optional<std::function<unsigned int(unsigned int)>>
    head_adder() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(_sv.v());
        mylist d_a1_value = *(d_a1);
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](const unsigned int &x) mutable {
              return ((x + d_a0) + d_a1_value.mylist_sum());
            });
      }
    }

    __attribute__((pure)) unsigned int mylist_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(_sv.v());
        return (d_a0 + (*(d_a1)).mylist_sum());
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// A second inductive to prevent methodification.
  struct tag {
    // TYPES
    struct MkTag {
      unsigned int d_a0;
    };

    using variant_t = std::variant<MkTag>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tag() {}

    explicit tag(MkTag _v) : d_v_(std::move(_v)) {}

    tag(const tag &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tag(tag &&_other) : d_v_(std::move(_other.d_v_)) {}

    tag &operator=(const tag &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tag &operator=(tag &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tag clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<MkTag>(_sv.v());
      return tag(MkTag{d_a0});
    }

    // CREATORS
    __attribute__((pure)) static tag mktag(unsigned int a0) {
      return tag(MkTag{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tag *operator->() { return this; }

    __attribute__((pure)) const tag *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tag(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename tag::MkTag>(_sv.v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename tag::MkTag>(_sv.v());
      return f(d_a0);
    }
  };

  /// test1: l = 10, 20, 30, h=10, t=20,30, mylist_sum(t)=50.
  /// f(5) = 5 + 10 + 50 = 65.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs =
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil())))
            .head_adder();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// test2: With noise to clobber stack.
  /// l = 100, 200, h=100, t=200, mylist_sum(t)=200.
  /// f(0) = 0 + 100 + 200 = 300.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> opt =
        mylist::mycons(100u, mylist::mycons(200u, mylist::mynil()))
            .head_adder();
    unsigned int noise =
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil())))
            .mylist_sum();
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(0u);
    } else {
      return noise;
    }
  }();
  /// Dummy use of tag.
  __attribute__((pure)) static tag mk_tag(unsigned int n);
};

#endif // INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
