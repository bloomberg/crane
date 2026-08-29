#ifndef INCLUDED_DEQUEELEMENTCAST
#define INCLUDED_DEQUEELEMENTCAST

#include <any>
#include <cstdint>
#include <deque>
#include <utility>
#include <variant>

#include "Specif.h"

namespace DequeElementCast {

struct DequeElementCast {
  struct Val {
    // TYPES
    struct VNum {
      uint64_t n;
    };

    struct VStr {
      uint64_t s;
    };

    using variant_t = std::variant<VNum, VStr>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Val() {}

    explicit Val(VNum _v) : v_(std::move(_v)) {}

    explicit Val(VStr _v) : v_(std::move(_v)) {}

    static Val vnum(uint64_t n) { return Val(VNum{n}); }

    static Val vstr(uint64_t s) { return Val(VStr{s}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };
  enum class Nonterm { NT_ITEM, NT_ITEMS };
  using sem_ty = std::any;
  using grammar_entry = Specif::SigT<Nonterm, sem_ty>;

  static const grammar_entry &items_value() {
    static const grammar_entry v =
        Specif::template SigT<Nonterm, std::any>::existt(
            Nonterm::NT_ITEMS, [](auto _a0, auto _a1) {
              _a1.push_front(_a0);
              return _a1;
            }(std::any(Val::vnum(UINT64_C(42))), [](auto _a0, auto _a1) {
              _a1.push_front(_a0);
              return _a1;
            }(std::any(Val::vstr(UINT64_C(7))), [](auto _a0, auto _a1) {
                _a1.push_front(_a0);
                return _a1;
              }(std::any(Val::vnum(UINT64_C(3))), std::deque<std::any>{}))));
    return v;
  }

  static const grammar_entry &item_value() {
    static const grammar_entry v =
        Specif::template SigT<Nonterm, std::any>::existt(
            Nonterm::NT_ITEM, Val::vnum(UINT64_C(99)));
    return v;
  }

  static uint64_t count_items(const Specif::SigT<Nonterm, std::any> &e);
  static uint64_t get_item_num(const Specif::SigT<Nonterm, std::any> &e);

  static const uint64_t &test_count() {
    static const uint64_t v = count_items(items_value());
    return v;
  }

  static const uint64_t &test_item_num() {
    static const uint64_t v = get_item_num(item_value());
    return v;
  }
};

} // namespace DequeElementCast

#endif // INCLUDED_DEQUEELEMENTCAST
