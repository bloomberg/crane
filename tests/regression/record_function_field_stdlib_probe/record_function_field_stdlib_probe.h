#ifndef INCLUDED_RECORD_FUNCTION_FIELD_STDLIB_PROBE
#define INCLUDED_RECORD_FUNCTION_FIELD_STDLIB_PROBE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Datatypes {
  __attribute__((pure)) static Bool0 negb(const Bool0 b);
};

struct RecordFunctionFieldStdlibProbe {
  struct endo {
    std::function<Bool0(Bool0)> run;

    __attribute__((pure)) endo *operator->() { return this; }

    __attribute__((pure)) const endo *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) endo clone() const { return endo{(*(this)).run}; }
  };

  static inline const endo e = endo{Datatypes::negb};
  static inline const Bool0 sample = e.run(Bool0::e_TRUE0);
};

#endif // INCLUDED_RECORD_FUNCTION_FIELD_STDLIB_PROBE
