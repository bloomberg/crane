#ifndef INCLUDED_RECORD_FUNCTION_FIELD_STDLIB_PROBE
#define INCLUDED_RECORD_FUNCTION_FIELD_STDLIB_PROBE

#include <functional>
#include <utility>

enum class Bool0 { TRUE_, FALSE_ };

struct Datatypes {
  static Bool0 negb(Bool0 b);
};

struct RecordFunctionFieldStdlibProbe {
  struct endo {
    std::function<Bool0(Bool0)> run;

    // ACCESSORS
    endo clone() const { return endo{(*this).run}; }
  };

  static inline const endo e = endo{Datatypes::negb};
  static inline const Bool0 sample = e.run(Bool0::TRUE_);
};

#endif // INCLUDED_RECORD_FUNCTION_FIELD_STDLIB_PROBE
