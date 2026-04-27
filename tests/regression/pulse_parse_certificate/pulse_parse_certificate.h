#ifndef INCLUDED_PULSE_PARSE_CERTIFICATE
#define INCLUDED_PULSE_PARSE_CERTIFICATE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct PulseParseCertificateCase {
  using Trace = List<bool>;
  using Runs = List<unsigned int>;
  __attribute__((pure)) static std::optional<unsigned int>
  first_true(const List<bool> &xs);
  __attribute__((pure)) static std::optional<unsigned int>
  last_true(const List<bool> &xs);
  __attribute__((pure)) static Runs trace_to_runs(const List<bool> &xs);
  __attribute__((pure)) static unsigned int
  pulse_base_from_runs(const List<unsigned int> &rs);
  enum class PulseClass { e_MARKSHORT, e_MARKLONG };

  template <typename T1>
  static T1 PulseClass_rect(const T1 f, const T1 f0, const PulseClass p) {
    switch (p) {
    case PulseClass::e_MARKSHORT: {
      return f;
    }
    case PulseClass::e_MARKLONG: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 PulseClass_rec(const T1 f, const T1 f0, const PulseClass p) {
    switch (p) {
    case PulseClass::e_MARKSHORT: {
      return f;
    }
    case PulseClass::e_MARKLONG: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static PulseClass
  classify_run_with_base(unsigned int base, const unsigned int &n);
  __attribute__((pure)) static List<PulseClass>
  classify_runs_with_base(unsigned int base, const List<unsigned int> &rs);
  __attribute__((pure)) static bool pulse_class_eqb(const PulseClass x,
                                                    const PulseClass y);
  __attribute__((pure)) static bool
  pulse_class_list_eqb(const List<PulseClass> &xs, const List<PulseClass> &ys);

  struct PulseCertificate {
    std::optional<unsigned int> certificate_first_active;
    std::optional<unsigned int> certificate_last_active;
    Runs certificate_runs;
    unsigned int certificate_base;
    List<PulseClass> certificate_classes;

    __attribute__((pure)) PulseCertificate *operator->() { return this; }

    __attribute__((pure)) const PulseCertificate *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) PulseCertificate clone() const {
      return PulseCertificate{
          (*(this)).certificate_first_active, (*(this)).certificate_last_active,
          (*(this)).certificate_runs, (*(this)).certificate_base,
          (*(this)).certificate_classes.clone()};
    }
  };

  __attribute__((pure)) static bool
  pulse_parse_certificate_self_consistent(const PulseCertificate &cert);
  __attribute__((pure)) static PulseCertificate
  certify_trace(const List<bool> &xs);
  static inline const Trace sample_trace = List<bool>::cons(
      false,
      List<bool>::cons(
          true,
          List<bool>::cons(
              true, List<bool>::cons(
                        false, List<bool>::cons(true, List<bool>::nil())))));
  static inline const PulseCertificate sample_certificate =
      certify_trace(sample_trace);
  static inline const bool sample_certificate_consistent =
      pulse_parse_certificate_self_consistent(sample_certificate);
  static inline const unsigned int sample_certificate_base =
      sample_certificate.certificate_base;
  static inline const unsigned int sample_certificate_first_active =
      []() -> unsigned int {
    if (sample_certificate.certificate_first_active.has_value()) {
      const unsigned int &idx = *sample_certificate.certificate_first_active;
      return idx;
    } else {
      return 99u;
    }
  }();
  static inline const unsigned int sample_certificate_last_active =
      []() -> unsigned int {
    if (sample_certificate.certificate_last_active.has_value()) {
      const unsigned int &idx = *sample_certificate.certificate_last_active;
      return idx;
    } else {
      return 99u;
    }
  }();
  static inline const unsigned int sample_certificate_class_count =
      sample_certificate.certificate_classes.length();
};

#endif // INCLUDED_PULSE_PARSE_CERTIFICATE
