#ifndef INCLUDED_STRING_
#define INCLUDED_STRING_

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

#include "Ascii.h"

namespace String {

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii::Ascii a0;
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

  static String string0(Ascii::Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    crane::small_vector<std::shared_ptr<String>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<String0>(&_v)) {
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) noexcept = default;
  String &operator=(String &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  String append(String s2) const {
    std::shared_ptr<String> _head{};
    std::shared_ptr<String> *_write = &_head;
    const String *_loop_self = this;
    String _loop_s2 = std::move(s2);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
        *_write = std::make_shared<String>(std::move(_loop_s2));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
        auto _cell =
            std::make_shared<String>(typename String::String0(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename String::String0>((*_write)->v_mut()).a1;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

} // namespace String

#endif // INCLUDED_STRING_
