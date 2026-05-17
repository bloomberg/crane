#ifndef INCLUDED_ASCII
#define INCLUDED_ASCII

#include <utility>
#include <variant>

namespace Ascii {

struct Ascii {
  // TYPES
  struct Ascii0 {
    bool a0;
    bool a1;
    bool a2;
    bool a3;
    bool a4;
    bool a5;
    bool a6;
    bool a7;
  };

  using variant_t = std::variant<Ascii0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Ascii() {}

  explicit Ascii(Ascii0 _v) : v_(std::move(_v)) {}

  Ascii(const Ascii &_other) : v_(std::move(_other.clone().v_)) {}

  Ascii(Ascii &&_other) : v_(std::move(_other.v_)) {}

  Ascii &operator=(const Ascii &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Ascii &operator=(Ascii &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Ascii clone() const {
    const auto &[a0, a1, a2, a3, a4, a5, a6, a7] = std::get<Ascii0>(this->v());
    return Ascii(Ascii0{a0, a1, a2, a3, a4, a5, a6, a7});
  }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return Ascii(Ascii0{a0, a1, a2, a3, a4, a5, a6, a7});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

} // namespace Ascii

#endif // INCLUDED_ASCII
