#ifndef INCLUDED_FAMILY_CALL_RESULT_MAPPED_LIST
#define INCLUDED_FAMILY_CALL_RESULT_MAPPED_LIST

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <deque>
#include <memory>
#include <utility>
#include <variant>

struct ListDef {
  static std::deque<uint64_t> seq(uint64_t start, uint64_t len);
};

struct FamilyCallResultMappedList {
  struct ty {
    // TYPES
    struct TNat {};

    struct TList {
      std::shared_ptr<ty> a0;
    };

    using variant_t = std::variant<TNat, TList>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TNat _v) : v_(_v) {}

    explicit ty(TList _v) : v_(std::move(_v)) {}

    static ty tnat() { return ty(TNat{}); }

    static ty tlist(ty a0) {
      return ty(TList{std::make_shared<ty>(std::move(a0))});
    }

    // MANIPULATORS
    ~ty() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<ty> {
        if (auto *_alt = std::get_if<TList>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<ty> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    ty(const ty &) = default;
    ty &operator=(const ty &) = default;
    ty(ty &&) = default;
    ty &operator=(ty &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 ty_rect(T1 f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TNat>(t.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename ty::TList>(t.v());
      return f0(*a0, ty_rect<T1>(std::move(f), f0, *a0));
    }
  }

  template <typename T1, typename F1>
  static T1 ty_rec(T1 f, F1 &&f0, const ty &t) {
    return ty_rect<T1>(std::move(f), f0, t);
  }

  using den = crane::obj;
  static uint64_t size(const ty &t, den n);
  static den mk(uint64_t n);
  static inline const uint64_t result =
      size(ty::tlist(ty::tnat()), mk(UINT64_C(4)));
};

#endif // INCLUDED_FAMILY_CALL_RESULT_MAPPED_LIST
