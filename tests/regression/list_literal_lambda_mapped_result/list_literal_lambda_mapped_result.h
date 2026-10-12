#ifndef INCLUDED_LIST_LITERAL_LAMBDA_MAPPED_RESULT
#define INCLUDED_LIST_LITERAL_LAMBDA_MAPPED_RESULT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  A hd(A default0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return a0;
    }
  }
};

struct ListLiteralLambdaMappedResult {
  static inline const List<crane::fn<std::optional<uint64_t>(uint64_t)>> fs =
      List<crane::fn<std::optional<uint64_t>(uint64_t)>>::cons(
          [](uint64_t x) { return std::make_optional<uint64_t>(x); },
          List<crane::fn<std::optional<uint64_t>(uint64_t)>>::nil());
  static inline const uint64_t from_option = []() -> uint64_t {
    static const auto hd_1 = crane::immortal(
        fs.hd([](uint64_t) { return std::optional<uint64_t>(); }));
    auto _cs = hd_1(UINT64_C(4));
    if (_cs.has_value()) {
      const uint64_t &x = *_cs;
      return x;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const List<crane::fn<std::pair<uint64_t, uint64_t>(uint64_t)>>
      gs = List<crane::fn<std::pair<uint64_t, uint64_t>(uint64_t)>>::cons(
          [](uint64_t x) { return std::make_pair(x, x); },
          List<crane::fn<std::pair<uint64_t, uint64_t>(uint64_t)>>::nil());
  static inline const uint64_t from_pair =
      gs.hd([](uint64_t x) { return std::make_pair(x, x); })(UINT64_C(3)).first;
};

#endif // INCLUDED_LIST_LITERAL_LAMBDA_MAPPED_RESULT
