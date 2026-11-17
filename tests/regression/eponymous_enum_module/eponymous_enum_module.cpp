#include "eponymous_enum_module.h"

/// An enum eponymous with the module that is extracted is not promoted into
/// the module's struct: it stays an enum class member, and the module's
/// other definitions stay members beside it.  Promoting it wrote
/// struct EponymousEnumModule { enum class EponymousEnumModule {...}; },
/// a member named like its class, and dropped every other definition.
EponymousEnumModule::eponymousEnumModule
EponymousEnumModule::next(EponymousEnumModule::eponymousEnumModule c) {
  switch (c) {
  case eponymousEnumModule::RED: {
    return eponymousEnumModule::GREEN;
  }
  case eponymousEnumModule::GREEN: {
    return eponymousEnumModule::BLUE;
  }
  case eponymousEnumModule::BLUE: {
    return eponymousEnumModule::RED;
  }
  default:
    std::unreachable();
  }
}

bool EponymousEnumModule::is_red(EponymousEnumModule::eponymousEnumModule c) {
  switch (c) {
  case eponymousEnumModule::RED: {
    return true;
  }
  default: {
    return false;
  }
  }
}
