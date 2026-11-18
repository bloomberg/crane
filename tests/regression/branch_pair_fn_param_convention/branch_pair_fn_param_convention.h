#pragma once

#include "crane_fn.h"
#include "fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct Ascii;
struct String;

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, crane::shared_child_slot<String> a1) {
    return String(String0{std::move(a0), a1.take()});
  }

  // MANIPULATORS
  ~String() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two if branches each build a pair holding a function on Rocq's string
/// (no Std mapping): one lambda reads its argument (a match), the other
/// ignores it.  After the callable-join fix both become crane::fn, but one
/// takes const String & and the other String, so the conditional is
/// ambiguous ("pair<fn<pt (const String &)>, ..> can be converted to
/// pair<fn<pt (String)>, ..> and vice versa").  A closure stored at a
/// field instantiated at a function type now converts to that type, spelled
/// from the instantiation, not deduced from the closure.
struct BranchPairFnParamConvention {
  struct pt {
    uint64_t px;
    bool py;
  };

  static uint64_t t(bool b);
};
