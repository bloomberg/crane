#include <effect_deep_compose.h>
#include <cassert>
#include <cstdlib>

int main() {
    // 1. timed_env_op
    auto elapsed = EffectDeepCompose::timed_env_op("CRANE_TEST_VAR", "hello");
    assert(elapsed >= 0);  // elapsed time should be non-negative

    // 2. just_greet (just runs without error)
    EffectDeepCompose::just_greet();

    // 3. env_with_log
    EffectDeepCompose::env_with_log("CRANE_LOG_TEST", "value");

    // 4. show_env
    EffectDeepCompose::show_env("CRANE_LOG_TEST");

    // 5. maybe_time
    auto t = EffectDeepCompose::maybe_time(true);
    assert(t > 0);
    auto t2 = EffectDeepCompose::maybe_time(false);
    assert(t2 == 0);

    // 6. repeat_n
    EffectDeepCompose::repeat_n(3u);

    // cleanup
    unsetenv("CRANE_TEST_VAR");
    unsetenv("CRANE_LOG_TEST");

    return 0;
}
