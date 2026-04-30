#ifndef INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
#define INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
    mylist clone() const {
      mylist _out{};

      struct _CloneFrame {
        const mylist *_src;
        mylist *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          const auto &_alt = std::get<Mynil>(_src->v());
          _dst->d_v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{_alt.d_a0,
                              _alt.d_a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mynil() { return mylist(Mynil{}); }

    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack;
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.d_v_)) {
          auto &_alt = std::get<Mycons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    /// Simple lambda captures h and t from match.
    /// Should use = capture (safe).
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

    unsigned int mylist_sum() const {
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
    tag clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<MkTag>(_sv.v());
      return tag(MkTag{d_a0});
    }

    // CREATORS
    static tag mktag(unsigned int a0) { return tag(MkTag{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

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
  static tag mk_tag(unsigned int n);
};

#endif // INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
