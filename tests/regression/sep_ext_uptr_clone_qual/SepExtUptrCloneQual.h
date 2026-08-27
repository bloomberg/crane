#ifndef INCLUDED_SEPEXTUPTRCLONEQUAL
#define INCLUDED_SEPEXTUPTRCLONEQUAL

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

namespace SepExtUptrCloneQual {

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

  template <typename _U> MyList(const MyList<_U> &_other) {
    if (std::holds_alternative<typename MyList<_U>::Mynil>(_other.v())) {
      this->v_ = Mynil{};
    } else {
      const auto &[a0, a1] = std::get<typename MyList<_U>::Mycons>(_other.v());
      this->v_ = Mycons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a0.type() == typeid(A))
                return std::any_cast<A>(a0);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a0);
            } else
              return A(a0);
          }(),
          a1 ? std::make_shared<MyList<A>>(*a1) : nullptr};
    }
  }

  static MyList<A> mynil() { return MyList<A>(Mynil{}); }

  static MyList<A> mycons(A a0, MyList<A> a1) {
    return MyList<A>(
        Mycons{std::move(a0), std::make_shared<MyList<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~MyList() {
    crane::small_vector<std::shared_ptr<MyList<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Mycons>(&_v)) {
        if (_alt->a1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  MyList(const MyList &) = default;
  MyList &operator=(const MyList &) = default;
  MyList(MyList &&) noexcept = default;
  MyList &operator=(MyList &&) noexcept = default;

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
