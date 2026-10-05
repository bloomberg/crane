#ifndef INCLUDED_ERASED_MULTI_INDEX
#define INCLUDED_ERASED_MULTI_INDEX

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Memory safety probe: type-indexed inductives with multiple indices.
///
/// Tests code generation for inductives indexed by multiple types.
/// These should all be erased to std::any, and any_cast must use
/// the correct type.
struct ErasedMultiIndex {
  /// Two type indices — both erased
  struct tagged {
    // DATA
    crane::obj k;
    crane::obj v_1;

    // ACCESSORS
    tagged clone() const { return {k, v_1}; }

    // CREATORS
    static tagged mktagged(crane::obj k, crane::obj v_1) {
      return {std::move(k), std::move(v_1)};
    }

    template <typename T2> T2 get_val() const {
      const auto &[k, v_1] = *this;
      return crane_any_cast<T2>(v_1);
    }

    template <typename T1> T1 get_key() const {
      const auto &[k0, v_1] = *this;
      return crane_any_cast<T1>(k0);
    }

    template <typename T1, typename T2, typename T3, typename F0>
    T1 tagged_rec(F0 &&f) const {
      return this->template tagged_rect<T2, T3>(crane_erase_fn<T1>(f));
    }

    template <typename T2, typename T3, typename F0>
    crane::obj tagged_rect(F0 &&f) const {
      const auto &[k0, v_1] = *this;
      return crane_call_erased(f, crane_any_cast<T2>(k0),
                               crane_any_cast<T3>(v_1));
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
      crane::obj a;
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

    static hlist hcons(crane::obj a, hlist a1) {
      return hlist(HCons{std::move(a), std::make_shared<hlist>(std::move(a1))});
    }

    // MANIPULATORS
    ~hlist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<hlist> {
        if (auto *_alt = std::get_if<HCons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<hlist> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    hlist(const hlist &) = default;
    hlist &operator=(const hlist &) = default;
    hlist(hlist &&) = default;
    hlist &operator=(hlist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t hlist_length() const {
      const hlist *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const hlist *_self;
      };

      /// CraneCont_HCons: resumes after recursive call, then processes rest.
      struct CraneCont_HCons {};

      using CraneFrame = std::variant<CraneEnter, CraneCont_HCons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified hlist_length: CraneEnter -> CraneCont_HCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const hlist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename hlist::HNil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a, a1] = std::get<typename hlist::HCons>(_sv.v());
            _stack.emplace_back(CraneCont_HCons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_HCons>(_frame));
          _result = (UINT64_C(1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 hlist_rec(T1 f, F1 &&f0) const {
      return this->template hlist_rect<T1>(std::move(f),
                                           crane_erase_fn<T1>(f0));
    }

    template <typename T1, typename F1> T1 hlist_rect(T1 f, F1 &&f0) const {
      const hlist *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const hlist *_self;
        std::decay_t<F1> f0;
      };

      /// CraneCont_HCons: saves [a0, a1, f0], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_HCons {
        crane::obj a0;
        std::shared_ptr<hlist> a1;
        std::decay_t<F1> f0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_HCons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, std::move(f0)});
      /// Loopified hlist_rect: CraneEnter -> CraneCont_HCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const hlist *_self = _f._self;
          auto f0 = std::move(_f.f0);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename hlist::HNil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename hlist::HCons>(_sv.v());
            _stack.emplace_back(CraneCont_HCons{a0, a1, f0});
            _stack.emplace_back(
                CraneEnter{crane_raw(a1), crane_erase_fn<T1>(std::move(f0))});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_HCons>(_frame));
          crane::obj a0 = std::move(_f.a0);
          std::shared_ptr<hlist> a1 = std::move(_f.a1);
          std::decay_t<F1> f0 = std::move(_f.f0);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
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
