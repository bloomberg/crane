#include <block_template_stress.h>
#include <cassert>

int main() {
    // Compilation test — block templates require stdin/file interaction,
    // so we verify compilation and type correctness.
    (void)&BlockTemplateStress::read_n_lines;
    (void)&BlockTemplateStress::conditional_read;
    (void)&BlockTemplateStress::read_and_add;
    (void)&BlockTemplateStress::branch_read;
    (void)&BlockTemplateStress::read_two_nats;
    (void)&BlockTemplateStress::block_result_as_arg;
    (void)&BlockTemplateStress::read_files;
    (void)&BlockTemplateStress::interleaved_void;
    return 0;
}
