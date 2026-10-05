#ifndef INCLUDED_SEPEXTUPTRCLONEQUAL
#define INCLUDED_SEPEXTUPTRCLONEQUAL

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

namespace SepExtUptrCloneQual {

template <typename A> struct MyList;
template <typename M>
concept OrderedType = requires { typename M::t; };

template <typename A> struct MyList {
  // TYPES
  struct Mynil {};

  struct Mycons {
    A a0;
    std::shared_ptr<MyList<A>> a1;
  };

  using variant_t = std::variant<Mynil, Mycons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  MyList() {}

  explicit MyList(Mynil _v) : v_(_v) {}

  explicit MyList(Mycons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  MyList(const MyList<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<MyList<A>>(nullptr),
            [](const MyList<CraneU> &_cell) -> const MyList<CraneU> * {
              if (std::holds_alternative<typename MyList<CraneU>::Mycons>(
                      _cell.v())) {
                return std::get<typename MyList<CraneU>::Mycons>(_cell.v())
                    .a1.get();
              } else {
                return nullptr;
              }
            },
            [&](const MyList<CraneU> &_other,
                std::shared_ptr<MyList<A>> _below) -> variant_t {
              if (std::holds_alternative<typename MyList<CraneU>::Mynil>(
                      _other.v())) {
                return Mynil{};
              } else {
                const auto &[a0, a1] =
                    std::get<typename MyList<CraneU>::Mycons>(_other.v());
                return Mycons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a0);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<MyList<A>>(std::move(_alt));
            })) {}

  static MyList<A> mynil() { return MyList<A>(Mynil{}); }

  static MyList<A> mycons(A a0, MyList<A> a1) {
    return MyList<A>(
        Mycons{std::move(a0), std::make_shared<MyList<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~MyList() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<MyList<A>> {
      if (auto *_alt = std::get_if<Mycons>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<MyList<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  MyList(const MyList &) = default;
  MyList &operator=(const MyList &) = default;
  MyList(MyList &&) = default;
  MyList &operator=(MyList &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <OrderedType X> struct FMap {
  template <typename T1>
  static MyList<std::pair<typename X::t, T1>>
  tail(const MyList<std::pair<typename X::t, T1>> &l) {
    if (std::holds_alternative<
            typename MyList<std::pair<typename X::t, T1>>::Mynil>(l.v())) {
      return MyList<std::pair<typename X::t, T1>>::mynil();
    } else {
      const auto &[a0, a1] =
          std::get<typename MyList<std::pair<typename X::t, T1>>::Mycons>(
              l.v());
      return *a1;
    }
  }
};

} // namespace SepExtUptrCloneQual

#endif // INCLUDED_SEPEXTUPTRCLONEQUAL
