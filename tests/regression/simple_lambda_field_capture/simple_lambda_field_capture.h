#ifndef INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
#define INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
      std::shared_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist> mynil() {
      return std::make_shared<mylist>(Mynil{});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          const std::shared_ptr<mylist> &a1) {
      return std::make_shared<mylist>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          std::shared_ptr<mylist> &&a1) {
      return std::make_shared<mylist>(Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Simple lambda captures h and t from match.
    /// Should use = capture (safe).
    __attribute__((pure))
    std::optional<std::function<unsigned int(unsigned int)>>
    head_adder() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](const unsigned int x) mutable {
              return ((x + d_a0) + d_a1->mylist_sum());
            });
      }
    }

    __attribute__((pure)) unsigned int mylist_sum() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return (d_a0 + d_a1->mylist_sum());
      }
    }

    template <typename T1,
              MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1,
              MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rect<T1>(f, f0));
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
    explicit tag(MkTag _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tag> mktag(unsigned int a0) {
      return std::make_shared<tag>(MkTag{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rec(F0 &&f) const {
      const auto &[d_a0] = std::get<typename tag::MkTag>(this->v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rect(F0 &&f) const {
      const auto &[d_a0] = std::get<typename tag::MkTag>(this->v());
      return f(d_a0);
    }
  };

  /// test1: l = 10, 20, 30, h=10, t=20,30, mylist_sum(t)=50.
  /// f(5) = 5 + 10 + 50 = 65.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs =
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil())))
            ->head_adder();
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
            ->head_adder();
    unsigned int noise =
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil())))
            ->mylist_sum();
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(0u);
    } else {
      return noise;
    }
  }();
  /// Dummy use of tag.
  static std::shared_ptr<tag> mk_tag(const unsigned int n);
};

#endif // INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
