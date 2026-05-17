#ifndef INCLUDED_STRING_
#define INCLUDED_STRING_

#include <memory>
#include <utility>
#include <variant>
#include <vector>

#include "Ascii.h"

namespace String {

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii::Ascii a0;
    std::unique_ptr<String> a1;
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

  String(const String &_other) : v_(std::move(_other.clone().v_)) {}

  String(String &&_other) noexcept : v_(std::move(_other.v_)) {}

  String &operator=(const String &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  String &operator=(String &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  String clone() const {
    String _out{};

    struct _CloneFrame {
      const String *_src;
      String *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const String *_src = _frame._src;
      String *_dst = _frame._dst;
      if (std::holds_alternative<EmptyString>(_src->v())) {
        _dst->v_ = EmptyString{};
      } else {
        const auto &_alt = std::get<String0>(_src->v());
        _dst->v_ = String0{_alt.a0.clone(),
                           _alt.a1 ? std::make_unique<String>() : nullptr};
        auto &_dst_alt = std::get<String0>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii::Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_unique<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    std::vector<std::unique_ptr<String>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](String &_node) {
      if (std::holds_alternative<String0>(_node.v_)) {
        auto &_alt = std::get<String0>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  String append(String s2) const {
    if (std::holds_alternative<typename String::EmptyString>(this->v())) {
      return s2;
    } else {
      const auto &[a0, a1] = std::get<typename String::String0>(this->v());
      return String::string0(a0, (*a1).append(std::move(s2)));
    }
  }
};

} // namespace String

#endif // INCLUDED_STRING_
