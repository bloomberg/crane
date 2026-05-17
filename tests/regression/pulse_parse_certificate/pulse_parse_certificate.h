#ifndef INCLUDED_PULSE_PARSE_CERTIFICATE
#define INCLUDED_PULSE_PARSE_CERTIFICATE

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
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
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
      return List<T1>::cons(f(a0), (*a1).template map<T1>(f));
    }
  }

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }
};

struct PulseParseCertificateCase {
  using Trace = List<bool>;
  using Runs = List<unsigned int>;
  static std::optional<unsigned int> first_true(const List<bool> &xs);
  static std::optional<unsigned int> last_true(const List<bool> &xs);
  static Runs trace_to_runs(const List<bool> &xs);
  static unsigned int pulse_base_from_runs(const List<unsigned int> &rs);
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

  static PulseClass classify_run_with_base(unsigned int base, unsigned int n);
  static List<PulseClass> classify_runs_with_base(unsigned int base,
                                                  const List<unsigned int> &rs);
  static bool pulse_class_eqb(PulseClass x, PulseClass y);
  static bool pulse_class_list_eqb(const List<PulseClass> &xs,
                                   const List<PulseClass> &ys);

  struct PulseCertificate {
    std::optional<unsigned int> certificate_first_active;
    std::optional<unsigned int> certificate_last_active;
    Runs certificate_runs;
    unsigned int certificate_base;
    List<PulseClass> certificate_classes;

    // ACCESSORS
    PulseCertificate clone() const {
      return PulseCertificate{
          (*this).certificate_first_active, (*this).certificate_last_active,
          (*this).certificate_runs, (*this).certificate_base,
          (*this).certificate_classes.clone()};
    }
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
