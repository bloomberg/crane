#include <pulse_parse_certificate.h>

std::optional<unsigned int>
PulseParseCertificateCase::first_true(const List<bool> &xs) {
  if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename List<bool>::Cons>(xs.v());
    if (d_a0) {
      return std::make_optional<unsigned int>(0u);
    } else {
      auto _cs = first_true(*(d_a1));
      if (_cs.has_value()) {
        const unsigned int &idx = *_cs;
        return std::make_optional<unsigned int>((idx + 1));
      } else {
        return std::optional<unsigned int>();
      }
    }
  }
}

std::optional<unsigned int>
PulseParseCertificateCase::last_true(const List<bool> &xs) {
  if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename List<bool>::Cons>(xs.v());
    auto _cs = last_true(*(d_a1));
    if (_cs.has_value()) {
      const unsigned int &idx = *_cs;
      return std::make_optional<unsigned int>((idx + 1));
    } else {
      if (d_a0) {
        return std::make_optional<unsigned int>(0u);
      } else {
        return std::optional<unsigned int>();
      }
    }
  }
}

PulseParseCertificateCase::Runs
PulseParseCertificateCase::trace_to_runs(const List<bool> &xs) {
  if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename List<bool>::Cons>(xs.v());
    if (d_a0) {
      return List<unsigned int>::cons(2u, trace_to_runs(*(d_a1)));
    } else {
      return List<unsigned int>::cons(1u, trace_to_runs(*(d_a1)));
    }
  }
}

unsigned int
PulseParseCertificateCase::pulse_base_from_runs(const List<unsigned int> &rs) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(rs.v())) {
    return 1u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(rs.v());
    return d_a0;
  }
}

PulseParseCertificateCase::PulseClass
PulseParseCertificateCase::classify_run_with_base(unsigned int base,
                                                  const unsigned int &n) {
  if ((base + 1) <= n) {
    return PulseClass::e_MARKLONG;
  } else {
    return PulseClass::e_MARKSHORT;
  }
}

List<PulseParseCertificateCase::PulseClass>
PulseParseCertificateCase::classify_runs_with_base(
    unsigned int base, const List<unsigned int> &rs) {
  return rs.template map<PulseParseCertificateCase::PulseClass>(
      [=](unsigned int _x0) mutable -> PulseParseCertificateCase::PulseClass {
        return classify_run_with_base(base, _x0);
      });
}

bool PulseParseCertificateCase::pulse_class_eqb(
    const PulseParseCertificateCase::PulseClass x,
    const PulseParseCertificateCase::PulseClass y) {
  switch (x) {
  case PulseClass::e_MARKSHORT: {
    switch (y) {
    case PulseClass::e_MARKSHORT: {
      return true;
    }
    case PulseClass::e_MARKLONG: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case PulseClass::e_MARKLONG: {
    switch (y) {
    case PulseClass::e_MARKSHORT: {
      return false;
    }
    case PulseClass::e_MARKLONG: {
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
    const auto &[d_a0, d_a1] =
        std::get<typename List<PulseParseCertificateCase::PulseClass>::Cons>(
            xs.v());
    if (std::holds_alternative<
            typename List<PulseParseCertificateCase::PulseClass>::Nil>(
            ys.v())) {
      return false;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<PulseParseCertificateCase::PulseClass>::Cons>(
              ys.v());
      return (pulse_class_eqb(d_a0, d_a00) &&
              pulse_class_list_eqb(*(d_a1), *(d_a10)));
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
  List<unsigned int> runs = trace_to_runs(xs);
  unsigned int base = pulse_base_from_runs(runs);
  List<PulseParseCertificateCase::PulseClass> classes =
      classify_runs_with_base(base, runs);
  return PulseCertificate{first_true(xs), last_true(xs), runs, base, classes};
}
