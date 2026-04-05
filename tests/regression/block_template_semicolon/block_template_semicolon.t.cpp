#include <block_template_semicolon.h>

int main() {
    // Compilation test — verifies that string arguments with semicolons
    // don't break the block template rendering.
    (void)&BlockTemplateSemicolon::read_semicolon_expr;
    (void)&BlockTemplateSemicolon::read_semicolon_stmt;
    (void)&BlockTemplateSemicolon::read_normal;
    return 0;
}
