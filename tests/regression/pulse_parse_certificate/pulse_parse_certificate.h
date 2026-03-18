#ifndef INCLUDED_PULSE_PARSE_CERTIFICATE
#define INCLUDED_PULSE_PARSE_CERTIFICATE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<t_A>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::Cons_(f(_args.d_a0),
                                           _args.d_a1->template map<T1>(f));
            }},
        this->v());
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }
};

struct PulseParseCertificateCase {
  using Trace = std::shared_ptr<List<bool>>;
  using Runs = std::shared_ptr<List<unsigned int>>;
  __attribute__((pure)) static std::optional<unsigned int>
  first_true(const std::shared_ptr<List<bool>> &xs);
  __attribute__((pure)) static std::optional<unsigned int>
  last_true(const std::shared_ptr<List<bool>> &xs);
  __attribute__((pure)) static Runs
  trace_to_runs(const std::shared_ptr<List<bool>> &xs);
  __attribute__((pure)) static unsigned int
  pulse_base_from_runs(const std::shared_ptr<List<unsigned int>> &rs);
  enum class PulseClass { e_MARKSHORT, e_MARKLONG };

  template <typename T1>
  static T1 PulseClass_rect(const T1 f, const T1 f0, const PulseClass p) {
    return [&](void) {
      switch (p) {
      case PulseClass::e_MARKSHORT: {
        return f;
      }
      case PulseClass::e_MARKLONG: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 PulseClass_rec(const T1 f, const T1 f0, const PulseClass p) {
    return [&](void) {
      switch (p) {
      case PulseClass::e_MARKSHORT: {
        return f;
      }
      case PulseClass::e_MARKLONG: {
        return f0;
      }
      }
    }();
  }

  __attribute__((pure)) static PulseClass
  classify_run_with_base(const unsigned int base, const unsigned int n);
  static std::shared_ptr<List<PulseClass>>
  classify_runs_with_base(const unsigned int base,
                          const std::shared_ptr<List<unsigned int>> &rs);
  __attribute__((pure)) static bool pulse_class_eqb(const PulseClass x,
                                                    const PulseClass y);
  __attribute__((pure)) static bool
  pulse_class_list_eqb(const std::shared_ptr<List<PulseClass>> &xs,
                       const std::shared_ptr<List<PulseClass>> &ys);

  struct PulseCertificate {
    std::optional<unsigned int> certificate_first_active;
    std::optional<unsigned int> certificate_last_active;
    Runs certificate_runs;
    unsigned int certificate_base;
    std::shared_ptr<List<PulseClass>> certificate_classes;
  };

  __attribute__((pure)) static bool pulse_parse_certificate_self_consistent(
      const std::shared_ptr<PulseCertificate> &cert);
  static std::shared_ptr<PulseCertificate>
  certify_trace(std::shared_ptr<List<bool>> xs);
  static inline const Trace sample_trace = List<bool>::ctor::Cons_(
      false,
      List<bool>::ctor::Cons_(
          true, List<bool>::ctor::Cons_(
                    true, List<bool>::ctor::Cons_(
                              false, List<bool>::ctor::Cons_(
                                         true, List<bool>::ctor::Nil_())))));
  static inline const std::shared_ptr<PulseCertificate> sample_certificate =
      certify_trace(sample_trace);
  static inline const bool sample_certificate_consistent =
      pulse_parse_certificate_self_consistent(sample_certificate);
  static inline const unsigned int sample_certificate_base =
      sample_certificate->certificate_base;
  static inline const unsigned int sample_certificate_first_active = [](void) {
    if (sample_certificate->certificate_first_active.has_value()) {
      unsigned int idx = *sample_certificate->certificate_first_active;
      return std::move(idx);
    } else {
      return 99u;
    }
  }();
  static inline const unsigned int sample_certificate_last_active = [](void) {
    if (sample_certificate->certificate_last_active.has_value()) {
      unsigned int idx = *sample_certificate->certificate_last_active;
      return std::move(idx);
    } else {
      return 99u;
    }
  }();
  static inline const unsigned int sample_certificate_class_count =
      sample_certificate->certificate_classes->length();
};

#endif // INCLUDED_PULSE_PARSE_CERTIFICATE
