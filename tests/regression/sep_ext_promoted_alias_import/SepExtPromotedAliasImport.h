#ifndef INCLUDED_SEPEXTPROMOTEDALIASIMPORT
#define INCLUDED_SEPEXTPROMOTEDALIASIMPORT

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <stdexcept>
#include <utility>
#include <variant>

#include "Datatypes.h"
#include "ParamsDef.h"
#include "ProvDef.h"

namespace SepExtPromotedAliasImport {

template <typename ptr> struct Mbit;
using ParamsDef::ptr;
using ProvDef::prov;

template <typename ptr> struct Mbit {
  // TYPES
  struct Bit_ptr {
    ptr p;
  };

  struct Bit_byte {
    typename Datatypes::Nat n;
  };

  using variant_t = std::variant<Bit_ptr, Bit_byte>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Mbit() {}

  explicit Mbit(Bit_ptr _v) : v_(std::move(_v)) {}

  explicit Mbit(Bit_byte _v) : v_(std::move(_v)) {}

  template <typename _U>
  Mbit(const Mbit<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Mbit<_U>::Bit_ptr>(_other.v())) {
            const auto &[p] = std::get<typename Mbit<_U>::Bit_ptr>(_other.v());
            return Bit_ptr{[&]() -> ptr {
              if constexpr (crane_convertible<ptr, const _U &>) {
                return crane_convert<ptr>(p);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[n] = std::get<typename Mbit<_U>::Bit_byte>(_other.v());
            return Bit_byte{n};
          }
        }()) {}

  static Mbit<ptr> bit_ptr(ptr p) { return Mbit<ptr>(Bit_ptr{std::move(p)}); }

  static Mbit<ptr> bit_byte(typename Datatypes::Nat n) {
    return Mbit<ptr>(Bit_byte{std::move(n)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename _tcI0>
    requires ParamsDef::Params<_tcI0, prov>
  typename Datatypes::Nat show() const {
    if (std::holds_alternative<typename Mbit<ptr>::Bit_ptr>(this->v())) {
      return Datatypes::Nat::o();
    } else {
      const auto &[n0] = std::get<typename Mbit<ptr>::Bit_byte>(this->v());
      return n0;
    }
  }
};

} // namespace SepExtPromotedAliasImport

#endif // INCLUDED_SEPEXTPROMOTEDALIASIMPORT
