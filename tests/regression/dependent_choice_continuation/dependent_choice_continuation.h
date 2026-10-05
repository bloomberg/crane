#ifndef INCLUDED_DEPENDENT_CHOICE_CONTINUATION
#define INCLUDED_DEPENDENT_CHOICE_CONTINUATION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <stdexcept>
#include <utility>
#include <variant>

struct DependentChoiceContinuation {
  enum class MemC { CNEXT_KEY, CFRESH_PROV };

  template <typename T1> static T1 MemC_rect(T1 f, T1 f0, MemC m) {
    switch (m) {
    case MemC::CNEXT_KEY: {
      return f;
    }
    case MemC::CFRESH_PROV: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 MemC_rec(const T1 &f, const T1 &f0, MemC m) {
    return MemC_rect<T1>(f, f0, m);
  }

  using memCType = crane::obj;

  template <typename A> struct MemS {
    // TYPES
    struct MRet {
      A a;
    };

    struct Mchoose {
      MemC c;
      crane::fn<MemS<A>(memCType)> k;
    };

    using variant_t = std::variant<MRet, Mchoose>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    MemS() {}

    explicit MemS(MRet _v) : v_(std::move(_v)) {}

    explicit MemS(Mchoose _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    MemS(const MemS<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename MemS<CraneU>::MRet>(
                    _other.v())) {
              const auto &[a] =
                  std::get<typename MemS<CraneU>::MRet>(_other.v());
              return MRet{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU &>) {
                  return crane_convert<A>(a);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[c, k] =
                  std::get<typename MemS<CraneU>::Mchoose>(_other.v());
              return Mchoose{c, crane_convert<crane::fn<MemS<A>(memCType)>>(k)};
            }
          }()) {}

    static MemS<A> mret(A a) { return MemS<A>(MRet{std::move(a)}); }

    static MemS<A> mchoose(MemC c, crane::fn<MemS<A>(memCType)> k) {
      return MemS<A>(Mchoose{c, std::move(k)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2>
  static T2 MemS_rect(
      std::type_identity_t<crane::fn<T2(T1)>> f,
      std::type_identity_t<crane::fn<T2(MemC, crane::fn<MemS<T1>(memCType)>,
                                        crane::fn<T2(memCType)>)>>
          f0,
      const MemS<T1> &m) {
    if (std::holds_alternative<typename MemS<T1>::MRet>(m.v())) {
      const auto &[a0] = std::get<typename MemS<T1>::MRet>(m.v());
      return f(a0);
    } else {
      const auto &[c0, k0] = std::get<typename MemS<T1>::Mchoose>(m.v());
      return f0(c0, k0, [=](const auto &m0) {
        return MemS_rect<T1, T2>(f, crane_erase_fn<T2>(f0), k0(m0));
      });
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
  static T2 MemS_rec(F0 &&f, F1 &&f0, const MemS<T1> &m) {
    return MemS_rect<T1, T2>(f, crane_erase_fn<T2>(f0), m);
  }

  template <typename T1, typename F0> static MemS<T1> Mfresh_prov(F0 &&k) {
    return MemS<T1>::mchoose(MemC::CFRESH_PROV, crane_erase_fn<MemS<T1>>(k));
  }

  static inline const MemS<bool> fresh_prov =
      Mfresh_prov<bool>([](bool p) { return MemS<bool>::mret(p); });
  static bool run(const MemS<bool> &m);
  static constexpr bool is_true = true;
};

#endif // INCLUDED_DEPENDENT_CHOICE_CONTINUATION
