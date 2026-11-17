#ifndef INCLUDED_EPONYMOUS_ENUM_MODULE
#define INCLUDED_EPONYMOUS_ENUM_MODULE

#include <utility>

/// An enum eponymous with the module that is extracted is not promoted into
/// the module's struct: it stays an enum class member, and the module's
/// other definitions stay members beside it.  Promoting it wrote
/// struct EponymousEnumModule { enum class EponymousEnumModule {...}; },
/// a member named like its class, and dropped every other definition.
struct EponymousEnumModule {
  enum class eponymousEnumModule { RED, GREEN, BLUE };

  template <typename T1>
  static T1 eponymousEnumModule_rect(T1 f, T1 f0, T1 f1,
                                     eponymousEnumModule e) {
    switch (e) {
    case eponymousEnumModule::RED: {
      return f;
    }
    case eponymousEnumModule::GREEN: {
      return f0;
    }
    case eponymousEnumModule::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 eponymousEnumModule_rec(T1 f, T1 f0, T1 f1, eponymousEnumModule e) {
    return eponymousEnumModule_rect<T1>(std::move(f), std::move(f0),
                                        std::move(f1), e);
  }

  static eponymousEnumModule next(eponymousEnumModule c);
  static bool is_red(eponymousEnumModule c);
};

#endif // INCLUDED_EPONYMOUS_ENUM_MODULE
