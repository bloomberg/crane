#include <cstdio>
#include <chrono>
#include "lambda_capture_perf.h"

int main() {
    auto start = std::chrono::high_resolution_clock::now();
    int result = LambdaCapturePerf::test;
    auto end = std::chrono::high_resolution_clock::now();
    auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    if (result != 500) {
        fprintf(stderr, "FAIL: expected 500, got %d\n", result);
        return 1;
    }
    if (ms > 5000) {
        fprintf(stderr, "FAIL: took %lldms (>5s), likely due to deep-copy in lambda capture\n", (long long)ms);
        return 1;
    }
    printf("OK: result=%d, time=%lldms\n", result, (long long)ms);
    return 0;
}
