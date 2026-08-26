#include "record_mediated_drain.h"

RecordMediatedDrain::t RecordMediatedDrain::wrap(uint64_t k,
                                                 RecordMediatedDrain::t acc) {
  return t::more(cell<RecordMediatedDrain::t>{k, acc});
}
