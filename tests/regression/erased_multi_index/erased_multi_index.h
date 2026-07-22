#ifndef INCLUDED_ERASED_MULTI_INDEX
#define INCLUDED_ERASED_MULTI_INDEX

#include "crane_fn.h"
#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Memory safety probe: type-indexed inductives with multiple indices.
///
/// Tests code generation for inductives indexed by multiple types.
/// These should all be erased to std::any, and any_cast must use
/// the correct type.
struct ErasedMultiIndex {
  /// Two type indices — both erased
  struct tagged {
    // DATA
    std::any k;
    std::any v;

    // ACCESSORS
    tagged clone() const { return {k, v}; }

    // CREATORS
    static tagged mktagged(std::any k, std::any v) {
      return {std::move(k), std::move(v)};
    }

    template <typename T2> T2 get_val() const {
      const auto &[k, v0] = *this;
      return std::any_cast<T2>(v0);
    }

    template <typename T1> T1 get_key() const {
      const auto &[k0, v] = *this;
      return std::any_cast<T1>(k0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, std::any &, std::any &>
    T1 tagged_rec(F0 &&f) const {
      const auto &[k0, v0] = *this;
      return crane_call_erased(f, k0, v0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, std::any &, std::any &>
    T1 tagged_rect(F0 &&f) const {
      const auto &[k0, v0] = *this;
      return crane_call_erased(f, k0, v0);
    }
  };

  static inline const uint64_t test_tagged = []() {
    tagged t = tagged::mktagged(UINT64_C(42), true);
    return std::move(t).template get_key<uint64_t>();
  }();

  /// Heterogeneous list using type-indexed existential
  struct hlist {
    // TYPES
    struct HNil {};

    struct HCons {
      std::any a;
      std::shared_ptr<hlist> a1;
    };

    using variant_t = std::variant<HNil, HCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    hlist() {}

    explicit hlist(HNil _v) : v_(_v) {}

    explicit hlist(HCons _v) : v_(std::move(_v)) {}

    static hlist hnil() { return hlist(HNil{}); }

    static hlist hcons(std::any a, hlist a1) {
      return hlist(HCons{std::move(a), std::make_shared<hlist>(std::move(a1))});
    }

    // MANIPULATORS
    ~hlist() {
      std::vector<std::shared_ptr<hlist>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<HCons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t hlist_length() const {
      if (std::holds_alternative<typename hlist::HNil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a, a1] = std::get<typename hlist::HCons>(this->v());
        return (UINT64_C(1) + a1->hlist_length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, std::any &, hlist &, T1 &>
    T1 hlist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename hlist::HNil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename hlist::HCons>(this->v());
        return f0(a0, *a1, a1->template hlist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, std::any &, hlist &, T1 &>
    T1 hlist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename hlist::HNil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename hlist::HCons>(this->v());
        return f0(a0, *a1, a1->template hlist_rect<T1>(f, f0));
      }
    }
  };

  static inline const uint64_t test_hlist = []() {
    hlist l = hlist::hcons(
        UINT64_C(42),
        hlist::hcons(true, hlist::hcons(UINT64_C(7), hlist::hnil())));
    return std::move(l).hlist_length();
  }();
};

#endif // INCLUDED_ERASED_MULTI_INDEX
