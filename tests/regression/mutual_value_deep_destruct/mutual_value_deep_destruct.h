#ifndef INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT
#define INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MutualValueDeepDestruct {
  /// Same mutual-recursive ownership shape as the copy test, but this test does
  /// not copy the value.  It isolates destruction: dropping a deep alternating
  /// a/b value currently recurses through the default unique_ptr destructor
  /// chain.  The generated classes do not get an iterative mutual destructor,
  /// so leaving scope after building a deep value overflows the C++ stack.
  struct a;
  struct b;

  struct a {
    // TYPES
    struct AEnd {};

    struct ANode {
      bool a0;
      std::shared_ptr<b> a1;
    };

    using variant_t = std::variant<AEnd, ANode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    a() {}

    explicit a(AEnd _v) : v_(_v) {}

    explicit a(ANode _v) : v_(std::move(_v)) {}

    a(const a &_other) : v_(std::move(_other.clone().v_)) {}

    a(a &&_other) noexcept : v_(std::move(_other.v_)) {}

    a &operator=(const a &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    a &operator=(a &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    a clone() const {
      a _out{};

      struct _CloneFrame {
        const a *_src;
        a *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const a *_src = _frame._src;
        a *_dst = _frame._dst;
        if (std::holds_alternative<AEnd>(_src->v())) {
          _dst->v_ = AEnd{};
        } else {
          const auto &_alt = std::get<ANode>(_src->v());
          _dst->v_ = ANode{_alt.a0, _alt.a1 ? std::make_shared<b>() : nullptr};
          auto &_dst_alt = std::get<ANode>(_dst->v_);
          if (_alt.a1) {
            if (std::holds_alternative<
                    typename MutualValueDeepDestruct::b::BNode>(_alt.a1->v())) {
              const auto &_psrc =
                  std::get<typename MutualValueDeepDestruct::b::BNode>(
                      _alt.a1->v());
              auto &_pdst =
                  std::get<typename MutualValueDeepDestruct::b::BNode>(
                      _dst_alt.a1->v_mut());
              if (_psrc.a0) {
                _pdst.a0 = std::make_shared<a>();
                _stack.push_back({_psrc.a0.get(), _pdst.a0.get()});
              }
            }
          }
        }
      }
      return _out;
    }

    // CREATORS
    static a aend() { return a(AEnd{}); }

    static a anode(bool a0, b a1) {
      return a(ANode{a0, std::make_shared<b>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct b {
    // TYPES
    struct BNode {
      std::shared_ptr<a> a0;
    };

    using variant_t = std::variant<BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    b() {}

    explicit b(BNode _v) : v_(std::move(_v)) {}

    b(const b &_other) : v_(std::move(_other.clone().v_)) {}

    b(b &&_other) noexcept : v_(std::move(_other.v_)) {}

    b &operator=(const b &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    b &operator=(b &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    b clone() const {
      const auto &[a0] = std::get<BNode>(this->v());
      return b(
          BNode{a0 ? std::make_shared<MutualValueDeepDestruct::a>(a0->clone())
                   : nullptr});
    }

    // CREATORS
    static b bnode(a a0) {
      return b(BNode{std::make_shared<a>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rect(T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[a1, a2] = std::get<typename a::ANode>(a0.v());
      return f0(a1, *a2);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rec(T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[a1, a2] = std::get<typename a::ANode>(a0.v());
      return f0(a1, *a2);
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, a &>
  static T1 b_rect(F0 &&f, const b &b0) {
    const auto &[a1] = std::get<typename b::BNode>(b0.v());
    return f(*a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, a &>
  static T1 b_rec(F0 &&f, const b &b0) {
    const auto &[a1] = std::get<typename b::BNode>(b0.v());
    return f(*a1);
  }

  static a keep_a(a x);
};

#endif // INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT
