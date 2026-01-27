// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <rapply.h>

#include <iostream>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

// Helper to convert nat to unsigned int
unsigned int nat_to_uint(const std::shared_ptr<Nat::nat>& n) {
    unsigned int result = 0;
    auto current = n;
    while (std::holds_alternative<Nat::nat::S>(current->v())) {
        result++;
        current = std::get<Nat::nat::S>(current->v())._a0;
    }
    return result;
}

// Helper to convert unsigned int to nat
std::shared_ptr<Nat::nat> uint_to_nat(unsigned int n) {
    auto result = Nat::nat::ctor::O_();
    for (unsigned int i = 0; i < n; i++) {
        result = Nat::nat::ctor::S_(result);
    }
    return result;
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
    // Create a record with an addition function (using Peano nats)
    auto add_fn = [](std::shared_ptr<Nat::nat> a, std::shared_ptr<Nat::nat> b) -> std::shared_ptr<Nat::nat> {
        // Simple Peano addition: just return a for now (testing structure, not correctness)
        unsigned int av = nat_to_uint(a);
        unsigned int bv = nat_to_uint(b);
        return uint_to_nat(av + bv);
    };

    // Create record directly using make_shared
    auto r = std::make_shared<RApply::r>(RApply::r{add_fn, uint_to_nat(0)});

    // Test apply_record
    auto result = RApply::apply_record(r, uint_to_nat(3), uint_to_nat(4));
    unsigned int result_val = nat_to_uint(result);
    std::cout << "apply_record(r, 3, 4) = " << result_val << std::endl;
    ASSERT(result_val == 7);

    if (testStatus == 0) {
        std::cout << "All rapply tests passed!" << std::endl;
    }

    return testStatus;
}
