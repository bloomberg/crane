#include "pulse_parse_certificate.h"

std::optional<uint64_t>
PulseParseCertificateCase::first_true(const List<bool> &xs) {
  if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
    return std::optional<uint64_t>();
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
    if (a0) {
      return std::make_optional<uint64_t>(UINT64_C(0));
    } else {
      auto _cs = first_true(*a1);
      if (_cs.has_value()) {
        const uint64_t &idx = *_cs;
        return std::make_optional<uint64_t>((idx + 1));
      } else {
        return std::optional<uint64_t>();
      }
    }
  }
}

std::optional<uint64_t>
PulseParseCertificateCase::last_true(const List<bool> &xs) {
  if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
    return std::optional<uint64_t>();
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
    auto _cs = last_true(*a1);
    if (_cs.has_value()) {
      const uint64_t &idx = *_cs;
      return std::make_optional<uint64_t>((idx + 1));
    } else {
      if (a0) {
        return std::make_optional<uint64_t>(UINT64_C(0));
      } else {
        return std::optional<uint64_t>();
      }
    }
  }
}

PulseParseCertificateCase::Runs
PulseParseCertificateCase::trace_to_runs(const List<bool> &xs) {
  if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
    if (a0) {
      return List<uint64_t>::cons(UINT64_C(2), trace_to_runs(*a1));
    } else {
      return List<uint64_t>::cons(UINT64_C(1), trace_to_runs(*a1));
    }
  }
}

uint64_t
PulseParseCertificateCase::pulse_base_from_runs(const List<uint64_t> &rs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(rs.v())) {
    return UINT64_C(1);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(rs.v());
    return a0;
  }
}

PulseParseCertificateCase::PulseClass
PulseParseCertificateCase::classify_run_with_base(uint64_t base, uint64_t n) {
  if ((base + 1) <= n) {
    return PulseClass::MARKLONG;
  } else {
    return PulseClass::MARKSHORT;
  }
}

List<PulseParseCertificateCase::PulseClass>
PulseParseCertificateCase::classify_runs_with_base(uint64_t base,
                                                   const List<uint64_t> &rs) {
  return rs.template map<PulseParseCertificateCase::PulseClass>(
      [=](uint64_t _x0) mutable -> PulseParseCertificateCase::PulseClass {
        return classify_run_with_base(base, _x0);
      });
}

bool PulseParseCertificateCase::pulse_class_eqb(
    PulseParseCertificateCase::PulseClass x,
    PulseParseCertificateCase::PulseClass y) {
  switch (x) {
  case PulseClass::MARKSHORT: {
    switch (y) {
    case PulseClass::MARKSHORT: {
      return true;
    }
    case PulseClass::MARKLONG: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case PulseClass::MARKLONG: {
    switch (y) {
    case PulseClass::MARKSHORT: {
      return false;
    }
    case PulseClass::MARKLONG: {
      return true;
    }
    default:
      std::unreachable();
    }
  }
  default:
    std::unreachable();
  }
}

bool PulseParseCertificateCase::pulse_class_list_eqb(
    const List<PulseParseCertificateCase::PulseClass> &xs,
    const List<PulseParseCertificateCase::PulseClass> &ys) {
  if (std::holds_alternative<
          typename List<PulseParseCertificateCase::PulseClass>::Nil>(xs.v())) {
    if (std::holds_alternative<
            typename List<PulseParseCertificateCase::PulseClass>::Nil>(
            ys.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0, a1] =
        std::get<typename List<PulseParseCertificateCase::PulseClass>::Cons>(
            xs.v());
    if (std::holds_alternative<
            typename List<PulseParseCertificateCase::PulseClass>::Nil>(
            ys.v())) {
      return false;
    } else {
      const auto &[a00, a10] =
          std::get<typename List<PulseParseCertificateCase::PulseClass>::Cons>(
              ys.v());
      return (pulse_class_eqb(a0, a00) && pulse_class_list_eqb(*a1, *a10));
    }
  }
}

bool PulseParseCertificateCase::pulse_parse_certificate_self_consistent(
    const PulseParseCertificateCase::PulseCertificate &cert) {
  return (
      (cert.certificate_base == pulse_base_from_runs(cert.certificate_runs) &&
       cert.certificate_classes.length() == cert.certificate_runs.length()) &&
      pulse_class_list_eqb(cert.certificate_classes,
                           classify_runs_with_base(cert.certificate_base,
                                                   cert.certificate_runs)));
}

PulseParseCertificateCase::PulseCertificate
PulseParseCertificateCase::certify_trace(const List<bool> &xs) {
  List<uint64_t> runs = trace_to_runs(xs);
  uint64_t base = pulse_base_from_runs(runs);
  List<PulseParseCertificateCase::PulseClass> classes =
      classify_runs_with_base(base, runs);
  return PulseCertificate{first_true(xs), last_true(xs), runs, base, classes};
}
