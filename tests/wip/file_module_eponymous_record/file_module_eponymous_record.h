#ifndef INCLUDED_FILE_MODULE_EPONYMOUS_RECORD
#define INCLUDED_FILE_MODULE_EPONYMOUS_RECORD

struct;

struct {
  uint64_t size;
};

struct Catalog {
  static grow(const &c);
};

const uint64_t answer = Catalog<>::grow({UINT64_C(1)}).size;

#endif // INCLUDED_FILE_MODULE_EPONYMOUS_RECORD
