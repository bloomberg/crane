#ifndef INCLUDED_STRING_
#define INCLUDED_STRING_

#include "crane_fn.h"
#include <atomic>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

#include "Ascii.h"

namespace String {

struct String;

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

  String append(String s2) const {
    std::optional<String> _root{};
    std::shared_ptr<String> *_write = nullptr;
    const String *_loop_self = this;
    String _loop_s2 = std::move(s2);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
        auto _value = std::move(_loop_s2);
        (_write ? *(*_write = std::make_shared<String>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
        auto _cell = typename String::String0(a0, nullptr);
        String &_node =
            (_write ? *(*_write = std::make_shared<String>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename String::String0>(_node.v_mut()).a1;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

} // namespace String

#endif // INCLUDED_STRING_
