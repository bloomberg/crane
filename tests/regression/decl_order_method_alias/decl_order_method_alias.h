#ifndef INCLUDED_DECL_ORDER_METHOD_ALIAS
#define INCLUDED_DECL_ORDER_METHOD_ALIAS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Rv;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Rv {
  // TYPES
  struct RU {};

  struct RS {
    uint64_t n;
  };

  using variant_t = std::variant<RU, RS>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Rv() {}

  explicit Rv(RU _v) : v_(_v) {}

  explicit Rv(RS _v) : v_(std::move(_v)) {}

  static Rv ru() { return Rv(RU{}); }

  static Rv rs(uint64_t n) { return Rv(RS{n}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

using rfile = List<Rv>;

struct RegFile {
  template <typename T1>
  static std::optional<List<T1>> replace_nth(const List<T1> &l, uint64_t i,
                                             T1 x);
  static std::optional<rfile> write_r(rfile x0_, uint64_t x1_, const Rv &x2_);
};

const std::optional<rfile> written = RegFile::write_r(
    List<Rv>::cons(Rv::ru(),
                   List<Rv>::cons(Rv::rs(UINT64_C(1)),
                                  List<Rv>::cons(Rv::ru(), List<Rv>::nil()))),
    UINT64_C(1), Rv::rs(UINT64_C(7)));
const uint64_t written_second = []() -> uint64_t {
  if (written.has_value()) {
    const List<Rv> &r = *written;
    if (std::holds_alternative<typename List<Rv>::Nil>(r.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<Rv>::Cons>(r.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<Rv>::Nil>(_sv0.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a00, a10] = std::get<typename List<Rv>::Cons>(_sv0.v());
        if (std::holds_alternative<typename Rv::RU>(a00.v())) {
          return UINT64_C(0);
        } else {
          const auto &[n1] = std::get<typename Rv::RS>(a00.v());
          return n1;
        }
      }
    }
  } else {
    return UINT64_C(0);
  }
}();
const bool out_of_range = []() -> bool {
  auto _cs = RegFile::write_r(List<Rv>::cons(Rv::ru(), List<Rv>::nil()),
                              UINT64_C(5), Rv::ru());
  if (_cs.has_value()) {
    const List<Rv> &_x = *_cs;
    return false;
  } else {
    return true;
  }
}();

template <typename T1>
std::optional<List<T1>> RegFile::replace_nth(const List<T1> &l, uint64_t i,
                                             T1 x) {
  if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
    return std::optional<List<T1>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
    if (i <= 0) {
      return std::make_optional<List<T1>>(List<T1>::cons(x, *a1));
    } else {
      uint64_t i_ = i - 1;
      auto _cs = RegFile::template replace_nth<T1>(*a1, i_, x);
      if (_cs.has_value()) {
        const List<T1> &t_ = *_cs;
        return std::make_optional<List<T1>>(List<T1>::cons(a0, t_));
      } else {
        return std::optional<List<T1>>();
      }
    }
  }
}

#endif // INCLUDED_DECL_ORDER_METHOD_ALIAS
