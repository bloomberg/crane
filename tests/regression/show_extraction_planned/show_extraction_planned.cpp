#include "show_extraction_planned.h"

/// Crane Show Extraction renders the term of the proof in progress as the
/// one declaration of a unit of its own.  It planned an empty unit instead,
/// so the declaration it rendered had no callable plan, and neither did a
/// global the term calls: every use was an anomaly.  The command runs while
/// this file is compiled, so an anomaly fails the test.
Nat ShowExtractionPlanned::twice(Nat n) { return n.add(n); }
