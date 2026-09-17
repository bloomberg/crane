#include "file_module_eponymous_record.h"

catalog Catalog0::grow(const catalog &c) { return catalog{(c.size + 1)}; }
