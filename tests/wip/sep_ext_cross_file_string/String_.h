#ifndef INCLUDED_STRING_
#define INCLUDED_STRING_

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  String append(String s2) const {
    if (std::holds_alternative<typename String::EmptyString>(this->v())) {
      return s2;
    } else {
      const auto &[a0, a1] = std::get<typename String::String0>(this->v());
      return String::string0(a0, a1->append(std::move(s2)));
    }
  }
};

} // namespace String

#endif // INCLUDED_STRING_
