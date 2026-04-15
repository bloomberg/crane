// This file intentionally left minimal: NameClashIifeThis.v generates a
// C++ compilation error (return this inside an IIFE lambda returning
// shared_ptr<shape>). The test fails at the compile step, not at runtime.
int main() { return 0; }
