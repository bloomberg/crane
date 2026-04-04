#include <void_callback.h>
#include <cassert>

int main() {
    (void)VoidCallback::test_for_each;
    (void)VoidCallback::use_side_effect;
    assert(VoidCallback::use_side_effect == 42u);
    assert(VoidCallback::test_ignore == 3u);
    (void)VoidCallback::test_apply_twice;
    (void)VoidCallback::test_apply_to_void;
    VoidCallback::void_in_match(true);
    VoidCallback::void_in_match(false);
    assert(VoidCallback::void_option(true).has_value());
    assert(!VoidCallback::void_option(false).has_value());
    return 0;
}
