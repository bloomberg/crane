#include <block_template_nonlocal.h>

int main() {
    // These would read from stdin at static init, but the test just checks compilation.
    // BUG: Currently fails with "non-local lambda expression cannot have a capture-default"
    return 0;
}
