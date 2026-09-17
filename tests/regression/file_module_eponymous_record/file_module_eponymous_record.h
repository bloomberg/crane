#ifndef INCLUDED_FILE_MODULE_EPONYMOUS_RECORD
#define INCLUDED_FILE_MODULE_EPONYMOUS_RECORD

struct catalog;

struct catalog {
  uint64_t size;
};

struct Catalog0 {
  static catalog grow(const catalog &c);
};

const uint64_t answer = Catalog0::grow(catalog{UINT64_C(1)}).size;

#endif // INCLUDED_FILE_MODULE_EPONYMOUS_RECORD
