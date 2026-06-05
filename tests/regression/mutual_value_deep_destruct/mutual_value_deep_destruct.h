#ifndef INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT
#define INCLUDED_MUTUAL_VALUE_DEEP_DESTRUCT

#include <any>
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

    static a aend() { return a(AEnd{}); }

    static a anode(bool a0, b a1) {
      return a(ANode{a0, std::make_shared<b>(std::move(a1))});
    }

    // MANIPULATORS
    ~a() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<ANode>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<a>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<b>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename b::BNode>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

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

    static b bnode(a a0) {
      return b(BNode{std::make_shared<a>(std::move(a0))});
    }

    // MANIPULATORS
    ~b() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<b>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<a>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename a::ANode>(&_pv)) {
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
        }
      }
    }

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
