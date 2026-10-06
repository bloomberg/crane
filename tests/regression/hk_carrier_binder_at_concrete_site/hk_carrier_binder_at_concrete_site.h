#ifndef INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE
#define INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename T> struct box;
struct TFunctor_box;
template <typename T, typename Body> struct holder;
struct Convert_holder;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool ltb(const Nat &m) const { return Nat::s(*this).leb(m); }

  bool leb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return true;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

template <typename I>
concept TFunctor = requires {
  typename I::template T<crane::obj>;
  {
    I::template tfmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template T<crane::obj>>())
  } -> std::convertible_to<typename I::template T<crane::obj>>;
};

template <TFunctor _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template T<T3> tfmap(F0 &&f, typename _tcI0::template T<T2> x) {
  return _tcI0::template tfmap<T2, T3>(f, std::move(x));
}

template <typename T> struct box {
  T b_payload;

  // ACCESSORS
  template <typename CraneU> operator box<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const T &>) {
        return crane_convert<CraneU>(b_payload);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }
};

struct TFunctor_box {
  template <typename CraneA0> using T = box<CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static box<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> f, box<CraneA0> b) {
    return box<CraneA1>{f(std::move(b).b_payload)};
  }
};

static_assert(TFunctor<TFunctor_box>);

template <typename T, typename Body> struct holder {
  T h_head;
  Body h_body;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator holder<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const T &>) {
                return crane_convert<CraneU0>(h_head);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const Body &>) {
                return crane_convert<CraneU1>(h_body);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }
};

template <TFunctor _tcI0> struct TFunctor_holder {
  template <typename CraneA0>
  using T = holder<CraneA0, typename _tcI0::template T<CraneA0>>;

  template <typename CraneA0, typename CraneA1>
  static holder<CraneA1, typename _tcI0::template T<CraneA1>>
  tfmap(crane::fn<CraneA1(CraneA0)> f,
        holder<CraneA0, typename _tcI0::template T<CraneA0>> m) {
    return holder<CraneA1, typename _tcI0::template T<CraneA1>>{
        f(m.h_head), _tcI0::template tfmap<CraneA0, CraneA1>(f, m.h_body)};
  }
};

template <typename I>
concept Convert = requires {
  typename I::template F<crane::obj>;
  {
    I::convert(std::declval<Nat>(), std::declval<typename I::template F<Nat>>())
  } -> std::convertible_to<typename I::template F<bool>>;
};

template <Convert _tcI0>
typename _tcI0::template F<bool> convert(const Nat &x0_,
                                         typename _tcI0::template F<Nat> x1_) {
  return _tcI0::convert(x0_, std::move(x1_));
}

struct Convert_holder {
  template <typename CraneA0> using F = holder<CraneA0, box<CraneA0>>;

  static holder<bool, box<bool>> convert(Nat n, holder<Nat, box<Nat>> a0) {
    return TFunctor_holder<TFunctor_box>::template tfmap<Nat, bool>(
        [=](const Nat &x) { return n.ltb(x); }, std::move(a0));
  }
};

static_assert(Convert<Convert_holder>);
holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m);

#endif // INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE
