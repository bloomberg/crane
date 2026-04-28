#include <sigma_types.h>

__attribute__((pure)) SigT<unsigned int, std::any>
SigmaTypes::nat_with_double(const unsigned int &n) {
  return SigT<unsigned int, std::any>::existt((n + n), std::any{});
}

__attribute__((pure)) Sig<unsigned int>
SigmaTypes::positive_succ(unsigned int n) {
  return Sig<unsigned int>::exist((n + 1));
}

__attribute__((pure)) unsigned int
SigmaTypes::get_positive(const unsigned int &n) {
  auto &&_sv = positive_succ(n);
  const auto &[d_x] = std::get<typename Sig<unsigned int>::Exist>(_sv.v());
  return d_x;
}

__attribute__((pure)) Sig<unsigned int>
SigmaTypes::double_positive(const unsigned int &n) {
  Sig<unsigned int> p = positive_succ(n);
  return Sig<unsigned int>::exist(
      ([=]() mutable {
        auto &[d_x] = std::get<typename Sig<unsigned int>::Exist>(p.v_mut());
        return d_x;
      }() +
       [=]() mutable {
         auto &[d_x0] = std::get<typename Sig<unsigned int>::Exist>(p.v_mut());
         return d_x0;
       }()));
}

__attribute__((pure)) unsigned int
SigmaTypes::use_nat_double(const unsigned int &n) {
  return nat_with_double(n).projT1();
}

__attribute__((pure)) List<unsigned int>
SigmaTypes::positives_up_to(const unsigned int &k) {
  if (k <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int k_ = k - 1;
    return List<unsigned int>::cons(
        [&]() {
          auto &&_sv = positive_succ(k_);
          const auto &[d_x] =
              std::get<typename Sig<unsigned int>::Exist>(_sv.v());
          return d_x;
        }(),
        positives_up_to(k_));
  }
}
