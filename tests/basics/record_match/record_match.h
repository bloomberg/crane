#ifndef INCLUDED_RECORD_MATCH
#define INCLUDED_RECORD_MATCH

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordMatch {
  struct MyRec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;

    // ACCESSORS
    __attribute__((pure)) MyRec clone() const {
      return MyRec{(*(this)).f1, (*(this)).f2, (*(this)).f3};
    }
  };

  __attribute__((pure)) static unsigned int sum(const MyRec &r);
};

#endif // INCLUDED_RECORD_MATCH
