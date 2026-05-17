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
    Ascii::Ascii d_a0;
    std::unique_ptr<String> d_a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : d_v_(_v) {}

  explicit String(String0 _v) : d_v_(std::move(_v)) {}

  String(const String &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  String(String &&_other) : d_v_(std::move(_other.d_v_)) {}

  String &operator=(const String &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  String &operator=(String &&_other) {
    d_v_ = std::move(_other.d_v_);
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
        _dst->d_v_ = EmptyString{};
      } else {
        const auto &_alt = std::get<String0>(_src->v());
        _dst->d_v_ = String0{_alt.d_a0.clone(),
                             _alt.d_a1 ? std::make_unique<String>() : nullptr};
        auto &_dst_alt = std::get<String0>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
      if (std::holds_alternative<String0>(_node.d_v_)) {
        auto &_alt = std::get<String0>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  String append(String s2) const {
    if (std::holds_alternative<typename String::EmptyString>(this->v())) {
      return s2;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename String::String0>(this->v());
      return String::string0(d_a0, (*d_a1).append(std::move(s2)));
    }
  }
};

} // namespace String

#endif // INCLUDED_STRING_
