#ifndef INCLUDED_ALIAS_MAPPED_INDUCTIVE_MATCH
#define INCLUDED_ALIAS_MAPPED_INDUCTIVE_MATCH

#include <cstdint>
#include <optional>
#include <utility>
#include <variant>

struct AliasMappedInductiveMatch {
  struct M {
    template <typename T1, typename F1>
    static T1 opt_rect(T1 f, F1 &&f0, const std::optional<uint64_t> &o) {
      if (o.has_value()) {
        const uint64_t &n = *o;
        return f0(n);
      } else {
        return f;
      }
    }

    template <typename T1, typename F1>
    static T1 opt_rec(T1 f, F1 &&f0, const std::optional<uint64_t> &o) {
      return opt_rect<T1>(std::move(f), f0, o);
    }
  };

  using N = M;
  static uint64_t get(const std::optional<uint64_t> &o);
  static inline const uint64_t result =
      (get(std::make_optional<uint64_t>(UINT64_C(4))) +
       get(std::optional<uint64_t>()));
};

#endif // INCLUDED_ALIAS_MAPPED_INDUCTIVE_MATCH
