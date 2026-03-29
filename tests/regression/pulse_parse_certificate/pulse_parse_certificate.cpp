#include <pulse_parse_certificate.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
PulseParseCertificateCase::first_true(const std::shared_ptr<List<bool>> &xs) {
  return std::visit(Overloaded{[](const typename List<bool>::Nil _args)
                                   -> std::optional<unsigned int> {
                                 return std::optional<unsigned int>();
                               },
                               [](const typename List<bool>::Cons _args)
                                   -> std::optional<unsigned int> {
                                 if (_args.d_a0) {
                                   return std::make_optional<unsigned int>(0u);
                                 } else {
                                   if (first_true(_args.d_a1).has_value()) {
                                     unsigned int idx = *first_true(_args.d_a1);
                                     return std::make_optional<unsigned int>(
                                         (idx + 1));
                                   } else {
                                     return std::optional<unsigned int>();
                                   }
                                 }
                               }},
                    xs->v());
}

__attribute__((pure)) std::optional<unsigned int>
PulseParseCertificateCase::last_true(const std::shared_ptr<List<bool>> &xs) {
  return std::visit(
      Overloaded{[](const typename List<bool>::Nil _args)
                     -> std::optional<unsigned int> {
                   return std::optional<unsigned int>();
                 },
                 [](const typename List<bool>::Cons _args)
                     -> std::optional<unsigned int> {
                   if (last_true(_args.d_a1).has_value()) {
                     unsigned int idx = *last_true(_args.d_a1);
                     return std::make_optional<unsigned int>((idx + 1));
                   } else {
                     if (_args.d_a0) {
                       return std::make_optional<unsigned int>(0u);
                     } else {
                       return std::optional<unsigned int>();
                     }
                   }
                 }},
      xs->v());
}

__attribute__((pure)) PulseParseCertificateCase::Runs
PulseParseCertificateCase::trace_to_runs(
    const std::shared_ptr<List<bool>> &xs) {
  return std::visit(Overloaded{[](const typename List<bool>::Nil _args)
                                   -> std::shared_ptr<List<unsigned int>> {
                                 return List<unsigned int>::nil();
                               },
                               [](const typename List<bool>::Cons _args)
                                   -> std::shared_ptr<List<unsigned int>> {
                                 if (_args.d_a0) {
                                   return List<unsigned int>::cons(
                                       2u, trace_to_runs(_args.d_a1));
                                 } else {
                                   return List<unsigned int>::cons(
                                       1u, trace_to_runs(_args.d_a1));
                                 }
                               }},
                    xs->v());
}

__attribute__((pure)) unsigned int
PulseParseCertificateCase::pulse_base_from_runs(
    const std::shared_ptr<List<unsigned int>> &rs) {
  return std::visit(Overloaded{[](const typename List<unsigned int>::Nil _args)
                                   -> unsigned int { return 1u; },
                               [](const typename List<unsigned int>::Cons _args)
                                   -> unsigned int { return _args.d_a0; }},
                    rs->v());
}

__attribute__((pure)) PulseParseCertificateCase::PulseClass
PulseParseCertificateCase::classify_run_with_base(const unsigned int base,
                                                  const unsigned int n) {
  if ((std::move(base) + 1) <= n) {
    return PulseClass::e_MARKLONG;
  } else {
    return PulseClass::e_MARKSHORT;
  }
}

std::shared_ptr<List<PulseParseCertificateCase::PulseClass>>
PulseParseCertificateCase::classify_runs_with_base(
    const unsigned int base, const std::shared_ptr<List<unsigned int>> &rs) {
  return rs->template map<PulseParseCertificateCase::PulseClass>(
      [&](unsigned int _x0) -> PulseParseCertificateCase::PulseClass {
        return classify_run_with_base(base, _x0);
      });
}

__attribute__((pure)) bool PulseParseCertificateCase::pulse_class_eqb(
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
    }
  }
  }
}

__attribute__((pure)) bool PulseParseCertificateCase::pulse_class_list_eqb(
    const std::shared_ptr<List<PulseParseCertificateCase::PulseClass>> &xs,
    const std::shared_ptr<List<PulseParseCertificateCase::PulseClass>> &ys) {
  return std::visit(
      Overloaded{
          [&](const typename List<PulseParseCertificateCase::PulseClass>::Nil
                  _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename List<
                        PulseParseCertificateCase::PulseClass>::Nil _args0)
                        -> bool { return true; },
                    [](const typename List<
                        PulseParseCertificateCase::PulseClass>::Cons _args0)
                        -> bool { return false; }},
                ys->v());
          },
          [&](const typename List<PulseParseCertificateCase::PulseClass>::Cons
                  _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename List<
                        PulseParseCertificateCase::PulseClass>::Nil _args0)
                        -> bool { return false; },
                    [&](const typename List<
                        PulseParseCertificateCase::PulseClass>::Cons _args0)
                        -> bool {
                      return (pulse_class_eqb(_args.d_a0, _args0.d_a0) &&
                              pulse_class_list_eqb(_args.d_a1, _args0.d_a1));
                    }},
                ys->v());
          }},
      xs->v());
}

__attribute__((pure)) bool
PulseParseCertificateCase::pulse_parse_certificate_self_consistent(
    const std::shared_ptr<PulseParseCertificateCase::PulseCertificate> &cert) {
  return (
      (cert->certificate_base == pulse_base_from_runs(cert->certificate_runs) &&
       cert->certificate_classes->length() ==
           cert->certificate_runs->length()) &&
      pulse_class_list_eqb(cert->certificate_classes,
                           classify_runs_with_base(cert->certificate_base,
                                                   cert->certificate_runs)));
}

std::shared_ptr<PulseParseCertificateCase::PulseCertificate>
PulseParseCertificateCase::certify_trace(std::shared_ptr<List<bool>> xs) {
  std::shared_ptr<List<unsigned int>> runs = trace_to_runs(xs);
  unsigned int base = pulse_base_from_runs(runs);
  std::shared_ptr<List<PulseParseCertificateCase::PulseClass>> classes =
      classify_runs_with_base(base, runs);
  return std::make_shared<PulseParseCertificateCase::PulseCertificate>(
      PulseCertificate{first_true(xs), last_true(xs), std::move(runs),
                       std::move(base), std::move(classes)});
}
