#ifndef INCLUDED_PULSE_PARSE_CERTIFICATE
#define INCLUDED_PULSE_PARSE_CERTIFICATE

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
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
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct PulseParseCertificateCase {
  using Trace = List<bool>;
  using Runs = List<uint64_t>;
  static std::optional<uint64_t> first_true(const List<bool> &xs);
  static std::optional<uint64_t> last_true(const List<bool> &xs);
  static Runs trace_to_runs(const List<bool> &xs);
  static uint64_t pulse_base_from_runs(const List<uint64_t> &rs);
  enum class PulseClass { MARKSHORT, MARKLONG };

  template <typename T1> static T1 PulseClass_rect(T1 f, T1 f0, PulseClass p) {
    switch (p) {
    case PulseClass::MARKSHORT: {
      return f;
    }
    case PulseClass::MARKLONG: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 PulseClass_rec(T1 f, T1 f0, PulseClass p) {
    switch (p) {
    case PulseClass::MARKSHORT: {
      return f;
    }
    case PulseClass::MARKLONG: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static PulseClass classify_run_with_base(uint64_t base, uint64_t n);
  static List<PulseClass> classify_runs_with_base(uint64_t base,
                                                  const List<uint64_t> &rs);
  static bool pulse_class_eqb(PulseClass x, PulseClass y);
  static bool pulse_class_list_eqb(const List<PulseClass> &xs,
                                   const List<PulseClass> &ys);

  struct PulseCertificate {
    std::optional<uint64_t> certificate_first_active;
    std::optional<uint64_t> certificate_last_active;
    Runs certificate_runs;
    uint64_t certificate_base;
    List<PulseClass> certificate_classes;
  };

  static bool
  pulse_parse_certificate_self_consistent(const PulseCertificate &cert);
  static PulseCertificate certify_trace(const List<bool> &xs);
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
  static inline const uint64_t sample_certificate_base =
      sample_certificate.certificate_base;
  static inline const uint64_t sample_certificate_first_active =
      []() -> uint64_t {
    if (sample_certificate.certificate_first_active.has_value()) {
      const uint64_t &idx = *sample_certificate.certificate_first_active;
      return idx;
    } else {
      return UINT64_C(99);
    }
  }();
  static inline const uint64_t sample_certificate_last_active =
      []() -> uint64_t {
    if (sample_certificate.certificate_last_active.has_value()) {
      const uint64_t &idx = *sample_certificate.certificate_last_active;
      return idx;
    } else {
      return UINT64_C(99);
    }
  }();
  static inline const uint64_t sample_certificate_class_count =
      sample_certificate.certificate_classes.length();
};

#endif // INCLUDED_PULSE_PARSE_CERTIFICATE
