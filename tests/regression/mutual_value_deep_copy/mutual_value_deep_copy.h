#ifndef INCLUDED_MUTUAL_VALUE_DEEP_COPY
#define INCLUDED_MUTUAL_VALUE_DEEP_COPY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MutualValueDeepCopy {
  /// Direct self-recursive value ADTs now get iterative clone/destruct paths.
  /// This test uses mutual recursion instead: a owns b, and b owns a.
  /// Crane currently generates recursive a::clone and b::clone methods that
  /// call each other through unique_ptr children.  Copying a deep alternating
  /// value with dup_a therefore overflows the C++ stack before the copied value
  /// can be used.
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
          _dst->d_v_ = ANode{
              _alt.d_a0,
              _alt.d_a1 ? std::make_unique<MutualValueDeepCopy::b>() : nullptr};
          auto &_dst_alt = std::get<ANode>(_dst->d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<typename MutualValueDeepCopy::b::BNode>(
                    _alt.d_a1->v())) {
              const auto &_psrc =
                  std::get<typename MutualValueDeepCopy::b::BNode>(
                      _alt.d_a1->v());
              auto &_pdst = std::get<typename MutualValueDeepCopy::b::BNode>(
                  _dst_alt.d_a1->v_mut());
              if (_psrc.d_a0) {
                _pdst.d_a0 = std::make_unique<MutualValueDeepCopy::a>();
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
      auto _drain = [&](a &_node) {
        if (std::holds_alternative<ANode>(_node.d_v_)) {
          auto &_alt = std::get<ANode>(_node.d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<typename MutualValueDeepCopy::b::BNode>(
                    _alt.d_a1->v())) {
              auto &_palt = std::get<typename MutualValueDeepCopy::b::BNode>(
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
      return b(
          BNode{d_a0 ? std::make_unique<MutualValueDeepCopy::a>(d_a0->clone())
                     : nullptr});
    }

    // CREATORS
    static b bnode(a a0) {
      return b(BNode{std::make_unique<a>(std::move(a0))});
    }

    // MANIPULATORS
    ~b() {
      std::vector<std::unique_ptr<b>> _stack{};
      auto _drain = [&](b &_node) {
        if (std::holds_alternative<BNode>(_node.d_v_)) {
          auto &_alt = std::get<BNode>(_node.d_v_);
          if (_alt.d_a0) {
            if (std::holds_alternative<typename MutualValueDeepCopy::a::ANode>(
                    _alt.d_a0->v())) {
              auto &_palt = std::get<typename MutualValueDeepCopy::a::ANode>(
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
  static T1 a_rect(const T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename a::ANode>(a0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rec(const T1 f, F1 &&f0, const a &a0) {
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

  static bool reaches_end_a(const a &x);
  static bool reaches_end_b(const b &y);
  static std::pair<a, a> dup_a(a x);
  static bool copied_reaches_end(const a &x);
};

#endif // INCLUDED_MUTUAL_VALUE_DEEP_COPY
