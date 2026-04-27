#ifndef INCLUDED_JMS_BBL_ROUNDTRIP
#define INCLUDED_JMS_BBL_ROUNDTRIP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct JmsBblRoundtrip {
  struct state {
    unsigned int pc;
    unsigned int ret;
    bool has_ret;

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).pc, (*(this)).ret, (*(this)).has_ret};
    }
  };

  __attribute__((pure)) static unsigned int
  addr12_of_nat(const unsigned int &n);
  __attribute__((pure)) static state execute_jms(const state &s,
                                                 const unsigned int &addr);
  __attribute__((pure)) static state execute_bbl(state s);
  static inline const state sample = state{100u, 0u, false};
  static inline const bool t =
      execute_bbl(execute_jms(sample, 200u)).pc == 102u;
};

#endif // INCLUDED_JMS_BBL_ROUNDTRIP
