// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: demonstrate stack overflow when destroying a deeply nested rose tree
// with list mapped to std::deque. The iterative destructor does not drain
// the deque field, so destruction recurses to tree depth.
//
// Expected: SEGFAULT (stack overflow) during destruction.
// When fixed: should print "Tree destroyed OK" and exit 0.

#include "deque_deep_tree_stackoverflow.h"
#include <cstdio>

int main() {
    using R = DequeDeepTreeStackoverflow::rose;

    // Build a deeply nested tree iteratively (avoids stack overflow
    // during construction). Each node has exactly one child in its deque.
    R tree = R::rleaf(42);
    for (int i = 0; i < 200000; ++i) {
        std::deque<R> children;
        children.push_back(std::move(tree));
        tree = R::rnode(std::move(children));
    }

    printf("Tree built, depth=200000\n");
    fflush(stdout);

    // Destroy the tree by overwriting. The old tree's destructor runs here.
    // With the current empty drain, this causes depth-200000 recursion → SEGFAULT.
    tree = R::rleaf(0);

    printf("Tree destroyed OK\n");
    return 0;
}
