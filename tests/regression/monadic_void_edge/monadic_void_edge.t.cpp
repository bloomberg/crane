#include <monadic_void_edge.h>

int main() {
    // Just verify compilation succeeds and basic calls work.
    // The monadic functions run IO effects, so we test structural
    // correctness by calling them (they print to stdout).
    MonadicVoidEdge::bind_void_then_value();
    MonadicVoidEdge::bind_void_void();
    MonadicVoidEdge::let_bind_monadic_void();
    MonadicVoidEdge::unit_chain();
    MonadicVoidEdge::match_after_bind();
    MonadicVoidEdge::void_nontail();
    MonadicVoidEdge::deeply_nested_void();
    MonadicVoidEdge::test_apply_effect();
    MonadicVoidEdge::bind_into_pair();
    MonadicVoidEdge::mixed_binds();
    MonadicVoidEdge::test_sequence();
    return 0;
}
