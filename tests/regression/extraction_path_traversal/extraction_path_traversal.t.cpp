// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// The security assertions run while ExtractionPathTraversal.vo is built: the
// Fail commands reject path-traversal extraction targets before any file is
// written. This executable makes the fixture visible to Crane's standard test
// runner.
int main() { return 0; }
