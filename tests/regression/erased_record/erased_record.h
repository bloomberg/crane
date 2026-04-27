#ifndef INCLUDED_ERASED_RECORD
#define INCLUDED_ERASED_RECORD

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ErasedRecord {
  struct ManyProps {
    unsigned int field0;
    unsigned int field1;
    unsigned int field2;
    unsigned int field3;
    unsigned int field4;

    __attribute__((pure)) ManyProps *operator->() { return this; }

    __attribute__((pure)) const ManyProps *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ManyProps clone() const {
      return ManyProps{(*(this)).field0, (*(this)).field1, (*(this)).field2,
                       (*(this)).field3, (*(this)).field4};
    }
  };

  __attribute__((pure)) static unsigned int complex_match(const ManyProps &r);
  __attribute__((pure)) static unsigned int unusual_body(const ManyProps &r);

  struct MostlyProps {
    unsigned int real1;
    unsigned int real2;
    unsigned int real3;

    __attribute__((pure)) MostlyProps *operator->() { return this; }

    __attribute__((pure)) const MostlyProps *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) MostlyProps clone() const {
      return MostlyProps{(*(this)).real1, (*(this)).real2, (*(this)).real3};
    }
  };

  __attribute__((pure)) static unsigned int
  access_mostly_props(const MostlyProps &r);
  static inline const unsigned int test1 =
      complex_match(ManyProps{1u, 2u, 3u, 4u, 5u});
  static inline const unsigned int test2 =
      unusual_body(ManyProps{1u, 2u, 3u, 4u, 5u});
  static inline const unsigned int test3 =
      access_mostly_props(MostlyProps{5u, 10u, 15u});
};

#endif // INCLUDED_ERASED_RECORD
