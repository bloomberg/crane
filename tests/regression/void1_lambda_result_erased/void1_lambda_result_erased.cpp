#include "void1_lambda_result_erased.h"

std::optional<Nat> Void1LambdaResultErased::run(
    const Nat &fuel,
    Void1LambdaResultErased::tree<Void1LambdaResultErased::noE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = observe<Void1LambdaResultErased::noE, Nat>(t);
      if (std::holds_alternative<typename Void1LambdaResultErased::treeF<
              Void1LambdaResultErased::noE, Nat,
              Void1LambdaResultErased::tree<Void1LambdaResultErased::noE,
                                            Nat>>::RetF>(_sv0.v())) {
        const auto &[r0] = std::get<typename Void1LambdaResultErased::treeF<
            Void1LambdaResultErased::noE, Nat,
            Void1LambdaResultErased::tree<Void1LambdaResultErased::noE,
                                          Nat>>::RetF>(_sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<typename Void1LambdaResultErased::treeF<
                     Void1LambdaResultErased::noE, Nat,
                     Void1LambdaResultErased::tree<Void1LambdaResultErased::noE,
                                                   Nat>>::TauF>(_sv0.v())) {
        const auto &[t0] = std::get<typename Void1LambdaResultErased::treeF<
            Void1LambdaResultErased::noE, Nat,
            Void1LambdaResultErased::tree<Void1LambdaResultErased::noE,
                                          Nat>>::TauF>(_sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}

Void1LambdaResultErased::tree<crane::obj, Sum<std::pair<Nat, Nat>, Nat>>
Void1LambdaResultErased::step(const std::pair<Nat, Nat> &p) {
  return apply_step<crane::obj, std::pair<Nat, Nat>, Nat>(
      [](std::pair<Nat, Nat> pat)
          -> Void1LambdaResultErased::tree<crane::obj,
                                           Sum<std::pair<Nat, Nat>, Nat>> {
        const auto &[k, acc] = pat;
        if (std::holds_alternative<typename Nat::O>(k.v())) {
          return tree<crane::obj, Sum<std::pair<Nat, Nat>, Nat>>::go(
              treeF<crane::obj, Sum<std::pair<Nat, Nat>, Nat>,
                    Void1LambdaResultErased::tree<
                        crane::obj, Sum<std::pair<Nat, Nat>, Nat>>>::
                  retf(Sum<std::pair<Nat, Nat>, Nat>::inr(acc)));
        } else {
          const auto &[a0] = std::get<typename Nat::S>(k.v());
          const Nat &a0_value = *a0;
          return tree<crane::obj, Sum<std::pair<Nat, Nat>, Nat>>::go(
              treeF<crane::obj, Sum<std::pair<Nat, Nat>, Nat>,
                    Void1LambdaResultErased::tree<
                        crane::obj, Sum<std::pair<Nat, Nat>, Nat>>>::
                  retf(Sum<std::pair<Nat, Nat>, Nat>::inl(
                      std::make_pair(a0_value, Nat::s(acc)))));
        }
      },
      p);
}

Nat Void1LambdaResultErased::first(const std::pair<Nat, Nat> &p) {
  auto &&_sv = observe(step(p));
  if (std::holds_alternative<typename Void1LambdaResultErased::treeF<
          crane::obj, Sum<std::pair<Nat, Nat>, Nat>,
          Void1LambdaResultErased::tree<crane::obj,
                                        Sum<std::pair<Nat, Nat>, Nat>>>::RetF>(
          _sv.v())) {
    const auto &[r0] = std::get<typename Void1LambdaResultErased::treeF<
        crane::obj, Sum<std::pair<Nat, Nat>, Nat>,
        Void1LambdaResultErased::tree<crane::obj,
                                      Sum<std::pair<Nat, Nat>, Nat>>>::RetF>(
        _sv.v());
    if (std::holds_alternative<typename Sum<std::pair<Nat, Nat>, Nat>::Inl>(
            r0.v())) {
      const auto &[a00] =
          std::get<typename Sum<std::pair<Nat, Nat>, Nat>::Inl>(r0.v());
      const auto &[k, _x] = a00;
      return k;
    } else {
      const auto &[a00] =
          std::get<typename Sum<std::pair<Nat, Nat>, Nat>::Inr>(r0.v());
      return a00;
    }
  } else {
    return Nat::o();
  }
}
