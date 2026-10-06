#ifndef INCLUDED_INSTANCE_FORWARDS_DICTS
#define INCLUDED_INSTANCE_FORWARDS_DICTS

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename I, typename T>
concept Endo = requires {
  { I::endo(std::declval<T>()) } -> std::convertible_to<T>;
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

struct InstanceForwardsDicts {
  template <typename _tcI0, typename T1>
    requires Endo<_tcI0, T1>
  static T1 endo(T1 x0_) {
    return _tcI0::endo(std::move(x0_));
  }

  template <TFunctor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template T<T3>
  tfmap(F0 &&f, typename _tcI0::template T<T2> x) {
    return _tcI0::template tfmap<T2, T3>(f, std::move(x));
  }
  enum class Tag { A, B };

  template <typename T1> static T1 tag_rect(T1 f, T1 f0, Tag t) {
    switch (t) {
    case Tag::A: {
      return f;
    }
    case Tag::B: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 tag_rec(T1 f, T1 f0, Tag t) {
    return tag_rect<T1>(std::move(f), std::move(f0), t);
  }
  enum class Op { C, D };

  template <typename T1> static T1 op_rect(T1 f, T1 f0, Op o) {
    switch (o) {
    case Op::C: {
      return f;
    }
    case Op::D: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 op_rec(T1 f, T1 f0, Op o) {
    return op_rect<T1>(std::move(f), std::move(f0), o);
  }
  enum class Cmp { E, F };

  template <typename T1> static T1 cmp_rect(T1 f, T1 f0, Cmp c) {
    switch (c) {
    case Cmp::E: {
      return f;
    }
    case Cmp::F: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 cmp_rec(T1 f, T1 f0, Cmp c) {
    return cmp_rect<T1>(std::move(f), std::move(f0), c);
  }
  enum class Flag { G, H };

  template <typename T1> static T1 flag_rect(T1 f, T1 f0, Flag f1) {
    switch (f1) {
    case Flag::G: {
      return f;
    }
    case Flag::H: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 flag_rec(T1 f, T1 f0, Flag f1) {
    return flag_rect<T1>(std::move(f), std::move(f0), f1);
  }
  template <typename T> struct exp;
  template <typename T> struct meta;

  template <typename T> struct exp {
    // TYPES
    struct Lit {
      Tag a0;
      T a1;
    };

    struct Ops {
      Op a0;
      Cmp a1;
      Flag a2;
    };

    struct Neg {
      uint64_t a0;
      std::shared_ptr<exp<T>> a1;
    };

    struct EMeta {
      std::shared_ptr<meta<T>> a0;
    };

    using variant_t = std::variant<Lit, Ops, Neg, EMeta>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    exp() {}

    explicit exp(Lit _v) : v_(std::move(_v)) {}

    explicit exp(Ops _v) : v_(std::move(_v)) {}

    explicit exp(Neg _v) : v_(std::move(_v)) {}

    explicit exp(EMeta _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    exp(const exp<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename exp<CraneU>::Lit>(_other.v())) {
              const auto &[a0, a1] =
                  std::get<typename exp<CraneU>::Lit>(_other.v());
              return Lit{a0, [&]() -> T {
                           if constexpr (crane_convertible<T, const CraneU &>) {
                             return crane_convert<T>(a1);
                           } else {
                             throw std::logic_error(
                                 "unreachable: inactive constructor field at "
                                 "this instantiation");
                           }
                         }()};
            } else {
              if (std::holds_alternative<typename exp<CraneU>::Ops>(
                      _other.v())) {
                const auto &[a0, a1, a2] =
                    std::get<typename exp<CraneU>::Ops>(_other.v());
                return Ops{a0, a1, a2};
              } else {
                if (std::holds_alternative<typename exp<CraneU>::Neg>(
                        _other.v())) {
                  const auto &[a0, a1] =
                      std::get<typename exp<CraneU>::Neg>(_other.v());
                  return Neg{a0, (a1 ? std::make_shared<exp<T>>(
                                           crane_convert<exp<T>>(*a1))
                                     : nullptr)};
                } else {
                  const auto &[a0] =
                      std::get<typename exp<CraneU>::EMeta>(_other.v());
                  return EMeta{(a0 ? std::make_shared<meta<T>>(
                                         crane_convert<meta<T>>(*a0))
                                   : nullptr)};
                }
              }
            }
          }()) {}

    static exp<T> lit(Tag a0, T a1) { return exp<T>(Lit{a0, std::move(a1)}); }

    static exp<T> ops(Op a0, Cmp a1, Flag a2) {
      return exp<T>(Ops{a0, a1, a2});
    }

    static exp<T> neg(uint64_t a0, exp<T> a1) {
      return exp<T>(Neg{a0, std::make_shared<exp<T>>(std::move(a1))});
    }

    static exp<T> emeta(meta<T> a0) {
      return exp<T>(EMeta{std::make_shared<meta<T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~exp() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Neg>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<EMeta>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<exp<T>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<meta<T>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename meta<T>::MExp>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

    exp(const exp &) = default;
    exp &operator=(const exp &) = default;
    exp(exp &&) = default;
    exp &operator=(exp &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T> struct meta {
    // TYPES
    struct MNull {};

    struct MExp {
      std::shared_ptr<exp<T>> a0;
    };

    using variant_t = std::variant<MNull, MExp>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    meta() {}

    explicit meta(MNull _v) : v_(_v) {}

    explicit meta(MExp _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    meta(const meta<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename meta<CraneU>::MNull>(
                    _other.v())) {
              return MNull{};
            } else {
              const auto &[a0] =
                  std::get<typename meta<CraneU>::MExp>(_other.v());
              return MExp{
                  (a0 ? std::make_shared<exp<T>>(crane_convert<exp<T>>(*a0))
                      : nullptr)};
            }
          }()) {}

    static meta<T> mnull() { return meta<T>(MNull{}); }

    static meta<T> mexp(exp<T> a0) {
      return meta<T>(MExp{std::make_shared<exp<T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~meta() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MExp>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<meta<T>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<exp<T>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename exp<T>::Neg>(&_pv)) {
                if (_alt->a1 && _alt->a1.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename exp<T>::EMeta>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

    meta(const meta &) = default;
    meta &operator=(const meta &) = default;
    meta(meta &&) = default;
    meta &operator=(meta &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1, typename F2,
            typename F3>
    requires std::is_invocable_r_v<T2, F0 &, const Tag &, const T1 &> &&
             std::is_invocable_r_v<T2, F1 &, const Op &, const Cmp &,
                                   const Flag &>
  static T2 exp_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const exp<T1> &e) {
    if (std::holds_alternative<typename exp<T1>::Lit>(e.v())) {
      const auto &[a0, a1] = std::get<typename exp<T1>::Lit>(e.v());
      return f(a0, a1);
    } else if (std::holds_alternative<typename exp<T1>::Ops>(e.v())) {
      const auto &[a0, a1, a2] = std::get<typename exp<T1>::Ops>(e.v());
      return f0(a0, a1, a2);
    } else if (std::holds_alternative<typename exp<T1>::Neg>(e.v())) {
      const auto &[a0, a1] = std::get<typename exp<T1>::Neg>(e.v());
      return f1(a0, *a1, exp_rect<T1, T2>(f, f0, f1, f2, *a1));
    } else {
      const auto &[a0] = std::get<typename exp<T1>::EMeta>(e.v());
      return f2(*a0);
    }
  }

  template <typename T1, typename T2, typename F0, typename F1, typename F2,
            typename F3>
  static T2 exp_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const exp<T1> &e) {
    return exp_rect<T1, T2>(f, f0, f1, f2, e);
  }

  template <typename T1, typename T2, typename F1>
  static T2 meta_rect(T2 f, F1 &&f0, const meta<T1> &m) {
    if (std::holds_alternative<typename meta<T1>::MNull>(m.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename meta<T1>::MExp>(m.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 meta_rec(T2 f, F1 &&f0, const meta<T1> &m) {
    return meta_rect<T1, T2>(std::move(f), f0, m);
  }

  template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
            typename _tcI4, typename T1, typename T2, typename F0>
    requires Endo<_tcI0, Flag> && Endo<_tcI1, Cmp> && Endo<_tcI2, Op> &&
             Endo<_tcI3, uint64_t> && Endo<_tcI4, Tag> &&
             std::is_invocable_r_v<T2, F0 &, const T1 &>
  static exp<T2> ft_exp(F0 &&f, const exp<T1> &e) {
    if (std::holds_alternative<typename exp<T1>::Lit>(e.v())) {
      const auto &[a0, a1] = std::get<typename exp<T1>::Lit>(e.v());
      return exp<T2>::lit(_tcI4::endo(a0), f(a1));
    } else if (std::holds_alternative<typename exp<T1>::Ops>(e.v())) {
      const auto &[a0, a1, a2] = std::get<typename exp<T1>::Ops>(e.v());
      return exp<T2>::ops(_tcI2::endo(a0), _tcI1::endo(a1), _tcI0::endo(a2));
    } else if (std::holds_alternative<typename exp<T1>::Neg>(e.v())) {
      const auto &[a0, a1] = std::get<typename exp<T1>::Neg>(e.v());
      return exp<T2>::neg(
          _tcI3::endo(a0),
          ft_exp<_tcI0, _tcI1, _tcI2, _tcI3, _tcI4, T1, T2>(f, *a1));
    } else {
      const auto &[a0] = std::get<typename exp<T1>::EMeta>(e.v());
      return exp<T2>::emeta(
          ft_meta<_tcI0, _tcI1, _tcI2, _tcI3, _tcI4, T1, T2>(f, *a0));
    }
  }

  template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
            typename _tcI4, typename T1, typename T2, typename F0>
    requires Endo<_tcI0, Flag> && Endo<_tcI1, Cmp> && Endo<_tcI2, Op> &&
             Endo<_tcI3, uint64_t> && Endo<_tcI4, Tag>
  static meta<T2> ft_meta(F0 &&f, const meta<T1> &m) {
    if (std::holds_alternative<typename meta<T1>::MNull>(m.v())) {
      return meta<T2>::mnull();
    } else {
      const auto &[a0] = std::get<typename meta<T1>::MExp>(m.v());
      return meta<T2>::mexp(
          ft_exp<_tcI0, _tcI1, _tcI2, _tcI3, _tcI4, T1, T2>(f, *a0));
    }
  }

  template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
            typename _tcI4>
    requires Endo<_tcI0, Tag> && Endo<_tcI1, uint64_t> && Endo<_tcI2, Op> &&
             Endo<_tcI3, Cmp> && Endo<_tcI4, Flag>
  struct TFunctor_exp {
    template <typename CraneA0> using T = exp<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static exp<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> a0, exp<CraneA0> a1) {
      return ft_exp<_tcI4, _tcI3, _tcI2, _tcI1, _tcI0, CraneA0, CraneA1>(
          std::move(a0), std::move(a1));
    }
  };

  struct Endo_tag {
    constexpr static Tag endo(Tag t) {
      switch (t) {
      case Tag::A: {
        return Tag::B;
      }
      case Tag::B: {
        return Tag::A;
      }
      default:
        std::unreachable();
      }
    }
  };

  static_assert(Endo<Endo_tag, Tag>);

  struct Endo_nat {
    constexpr static uint64_t endo(uint64_t x) { return (x + 1); }
  };

  static_assert(Endo<Endo_nat, uint64_t>);

  struct Endo_op {
    constexpr static Op endo(Op x) { return x; }
  };

  static_assert(Endo<Endo_op, Op>);

  struct Endo_cmp {
    constexpr static Cmp endo(Cmp x) { return x; }
  };

  static_assert(Endo<Endo_cmp, Cmp>);

  struct Endo_flag {
    constexpr static Flag endo(Flag x) { return x; }
  };

  static_assert(Endo<Endo_flag, Flag>);
  static inline const exp<uint64_t> e0 = exp<uint64_t>::neg(
      UINT64_C(1), exp<uint64_t>::emeta(meta<uint64_t>::mexp(
                       exp<uint64_t>::lit(Tag::A, UINT64_C(2)))));
  static inline const exp<uint64_t> e1 =
      TFunctor_exp<Endo_tag, Endo_nat, Endo_op, Endo_cmp, Endo_flag>::
          template tfmap<uint64_t, uint64_t>(
              [](uint64_t n) { return (n + UINT64_C(10)); }, e0);
  static uint64_t sum_exp(const exp<uint64_t> &e);
  static inline const uint64_t result = sum_exp(e1);
};

#endif // INCLUDED_INSTANCE_FORWARDS_DICTS
