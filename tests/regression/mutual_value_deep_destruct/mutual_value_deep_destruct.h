#ifndef INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT
#define INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT

#include <memory>
#include <optional>
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
      bool d_a0;
      std::unique_ptr<b> d_a1;
    };

    using variant_t = std::variant<AEnd, ANode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    a() {}

    explicit a(AEnd _v) : d_v_(_v) {}

    explicit a(ANode _v) : d_v_(std::move(_v)) {}

    a(const a &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    a(a &&_other) : d_v_(std::move(_other.d_v_)) {}

    a &operator=(const a &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    a &operator=(a &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = AEnd{};
        } else {
          const auto &_alt = std::get<ANode>(_src->v());
          _dst->d_v_ =
              ANode{_alt.d_a0, _alt.d_a1 ? std::make_unique<b>() : nullptr};
          auto &_dst_alt = std::get<ANode>(_dst->d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<
                    typename MutualValueDeepDestruct::b::BNode>(
                    _alt.d_a1->v())) {
              const auto &_psrc =
                  std::get<typename MutualValueDeepDestruct::b::BNode>(
                      _alt.d_a1->v());
              auto &_pdst =
                  std::get<typename MutualValueDeepDestruct::b::BNode>(
                      _dst_alt.d_a1->v_mut());
              if (_psrc.d_a0) {
                _pdst.d_a0 = std::make_unique<a>();
                _stack.push_back({_psrc.d_a0.get(), _pdst.d_a0.get()});
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
      return a(ANode{std::move(a0), std::make_unique<b>(std::move(a1))});
    }

    // MANIPULATORS
    ~a() {
      std::vector<std::unique_ptr<a>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](a &_node) {
        if (std::holds_alternative<ANode>(_node.d_v_)) {
          auto &_alt = std::get<ANode>(_node.d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<
                    typename MutualValueDeepDestruct::b::BNode>(
                    _alt.d_a1->v())) {
              auto &_palt =
                  std::get<typename MutualValueDeepDestruct::b::BNode>(
                      _alt.d_a1->v_mut());
              if (_palt.d_a0) {
                _stack.push_back(std::move(_palt.d_a0));
              }
            }
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  struct b {
    // TYPES
    struct BNode {
      std::unique_ptr<a> d_a0;
    };

    using variant_t = std::variant<BNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    b() {}

    explicit b(BNode _v) : d_v_(std::move(_v)) {}

    b(const b &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    b(b &&_other) : d_v_(std::move(_other.d_v_)) {}

    b &operator=(const b &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    b &operator=(b &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    b clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<BNode>(_sv.v());
      return b(BNode{
          d_a0 ? std::make_unique<MutualValueDeepDestruct::a>(d_a0->clone())
               : nullptr});
    }

    // CREATORS
    static b bnode(a a0) {
      return b(BNode{std::make_unique<a>(std::move(a0))});
    }

    // MANIPULATORS
    ~b() {
      std::vector<std::unique_ptr<b>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](b &_node) {
        if (std::holds_alternative<BNode>(_node.d_v_)) {
          auto &_alt = std::get<BNode>(_node.d_v_);
          if (_alt.d_a0) {
            if (std::holds_alternative<
                    typename MutualValueDeepDestruct::a::ANode>(
                    _alt.d_a0->v())) {
              auto &_palt =
                  std::get<typename MutualValueDeepDestruct::a::ANode>(
                      _alt.d_a0->v_mut());
              if (_palt.d_a1) {
                _stack.push_back(std::move(_palt.d_a1));
              }
            }
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rect(T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename a::ANode>(a0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rec(T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename a::ANode>(a0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, a &>
  static T1 b_rect(F0 &&f, const b &b0) {
    const auto &[d_a0] = std::get<typename b::BNode>(b0.v());
    return f(*(d_a0));
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, a &>
  static T1 b_rec(F0 &&f, const b &b0) {
    const auto &[d_a0] = std::get<typename b::BNode>(b0.v());
    return f(*(d_a0));
  }

  static a keep_a(a x);
};

#endif // INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT
