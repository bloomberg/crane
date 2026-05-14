#ifndef INCLUDED_ASCII
#define INCLUDED_ASCII

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

namespace Ascii {

struct Ascii {
  // TYPES
  struct Ascii0 {
    bool d_a0;
    bool d_a1;
    bool d_a2;
    bool d_a3;
    bool d_a4;
    bool d_a5;
    bool d_a6;
    bool d_a7;
  };

  using variant_t = std::variant<Ascii0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Ascii() {}

  explicit Ascii(Ascii0 _v) : d_v_(std::move(_v)) {}

  Ascii(const Ascii &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Ascii(Ascii &&_other) : d_v_(std::move(_other.d_v_)) {}

  Ascii &operator=(const Ascii &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Ascii &operator=(Ascii &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Ascii clone() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1, d_a2, d_a3, d_a4, d_a5, d_a6, d_a7] =
        std::get<Ascii0>(_sv.v());
    return Ascii(Ascii0{d_a0, d_a1, d_a2, d_a3, d_a4, d_a5, d_a6, d_a7});
  }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return Ascii(Ascii0{std::move(a0), std::move(a1), std::move(a2),
                        std::move(a3), std::move(a4), std::move(a5),
                        std::move(a6), std::move(a7)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

} // namespace Ascii

#endif // INCLUDED_ASCII
