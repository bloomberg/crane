#include "local_cofix_without_parameters.h"

uint64_t
LocalCofixWithoutParameters::hd(const LocalCofixWithoutParameters::stream &s) {
  const auto &[a0, a1] =
      std::get<typename LocalCofixWithoutParameters::stream::Cons>(s.v());
  return a0;
}

List<uint64_t> LocalCofixWithoutParameters::take(
    uint64_t k, const LocalCofixWithoutParameters::stream &s) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    const auto &[a0, a1] =
        std::get<typename LocalCofixWithoutParameters::stream::Cons>(s.v());
    return List<uint64_t>::cons(a0, take(k_, a1));
  }
}

LocalCofixWithoutParameters::stream
LocalCofixWithoutParameters::zeros_or(bool b) {
  if (b) {
    auto z_impl = [](auto &_self_z,
                     std::monostate) -> LocalCofixWithoutParameters::stream {
      return stream::lazy_(
          [=]() -> typename LocalCofixWithoutParameters::stream::Cons {
            return {UINT64_C(0), _self_z(_self_z, std::monostate{})};
          });
    };
    auto z = [=, z_impl = std::move(z_impl)](
                 std::monostate u) -> LocalCofixWithoutParameters::stream {
      return z_impl(z_impl, u);
    };
    return z(std::monostate{});
  } else {
    auto o_impl = [](auto &_self_o,
                     std::monostate) -> LocalCofixWithoutParameters::stream {
      return stream::lazy_(
          [=]() -> typename LocalCofixWithoutParameters::stream::Cons {
            return {UINT64_C(1), _self_o(_self_o, std::monostate{})};
          });
    };
    auto o = [=, o_impl = std::move(o_impl)](
                 std::monostate u) -> LocalCofixWithoutParameters::stream {
      return o_impl(o_impl, u);
    };
    return o(std::monostate{});
  }
}

LocalCofixWithoutParameters::stream
LocalCofixWithoutParameters::ones_then(const List<uint64_t> &l) {
  return l.template fold_right<LocalCofixWithoutParameters::stream>(
      [](uint64_t x, const LocalCofixWithoutParameters::stream &x0) {
        return stream::cons(x, x0);
      },
      []() {
        auto o_impl =
            [](auto &_self_o,
               std::monostate) -> LocalCofixWithoutParameters::stream {
          return stream::lazy_(
              [=]() -> typename LocalCofixWithoutParameters::stream::Cons {
                return {UINT64_C(1), _self_o(_self_o, std::monostate{})};
              });
        };
        auto o = [=, o_impl = std::move(o_impl)](
                     std::monostate u) -> LocalCofixWithoutParameters::stream {
          return o_impl(o_impl, u);
        };
        return o(std::monostate{});
      }());
}
