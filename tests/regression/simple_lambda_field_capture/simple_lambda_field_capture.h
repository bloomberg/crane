#ifndef INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
#define INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
      uint64_t a0;
      std::unique_ptr<mylist> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    mylist(const mylist &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist &operator=(const mylist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist clone() const {
      mylist _out{};

      struct _CloneFrame {
        const mylist *_src;
        mylist *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ =
              Mycons{_alt.a0, _alt.a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mynil() { return mylist(Mynil{}); }

    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_unique<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// Simple lambda captures h and t from match.
    /// Should use = capture (safe).
    std::optional<std::function<uint64_t(uint64_t)>> head_adder() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return std::optional<std::function<uint64_t(uint64_t)>>();
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        const mylist &a1_value = *a1;
        return std::make_optional<std::function<uint64_t(uint64_t)>>(
            [=](uint64_t x) mutable {
              return ((x + a0) + a1_value.mylist_sum());
            });
      }
    }

    uint64_t mylist_sum() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return (a0 + (*a1).mylist_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// A second inductive to prevent methodification.
  struct tag {
    // DATA
    uint64_t a0;

    // ACCESSORS
    tag clone() const { return {a0}; }

    // CREATORS
    static tag mktag(uint64_t a0) { return {a0}; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 tag_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 tag_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
    }
  };

  /// test1: l = 10, 20, 30, h=10, t=20,30, mylist_sum(t)=50.
  /// f(5) = 5 + 10 + 50 = 65.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = mylist::mycons(UINT64_C(10),
                              mylist::mycons(UINT64_C(20),
                                             mylist::mycons(UINT64_C(30),
                                                            mylist::mynil())))
                   .head_adder();
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test2: With noise to clobber stack.
  /// l = 100, 200, h=100, t=200, mylist_sum(t)=200.
  /// f(0) = 0 + 100 + 200 = 300.
  static inline const uint64_t test2 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> opt =
        mylist::mycons(UINT64_C(100),
                       mylist::mycons(UINT64_C(200), mylist::mynil()))
            .head_adder();
    uint64_t noise =
        mylist::mycons(
            UINT64_C(1),
            mylist::mycons(UINT64_C(2),
                           mylist::mycons(UINT64_C(3), mylist::mynil())))
            .mylist_sum();
    if (opt.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *opt;
      return f(UINT64_C(0));
    } else {
      return noise;
    }
  }();
  /// Dummy use of tag.
  static tag mk_tag(uint64_t n);
};

#endif // INCLUDED_SIMPLE_LAMBDA_FIELD_CAPTURE
