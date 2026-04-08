// Port of the examples from the Rust README.
//
// Demonstrates:
//   1. Basic atomically call
//   2. Read/write within a transaction
//   3. Composing transactions

#include "stm.h"
#include <iostream>

int main() {
    using namespace stm;

    // Example 1: Basic atomically call (from README)
    //
    // Rust:
    //   atomically(|trans| {
    //       Ok(42)
    //   });
    int result = atomically([](Transaction&) {
        return 42;
    });
    std::cout << "Example 1: " << result << std::endl;

    // Example 2: Read and write a TVar (from README)
    //
    // Rust:
    //   let var = TVar::new(0);
    //   let x = atomically(|trans| {
    //       var.write(trans, 42)?;
    //       var.read(trans)
    //   });
    TVar<int> var(0);
    int x = atomically([&](Transaction& tx) {
        var.write(tx, 42);
        return var.read(tx);
    });
    std::cout << "Example 2: var = " << x << std::endl;

    // Example 3: Composing two operations (from README)
    //
    // Rust:
    //   let read = TVar::new(42);
    //   let write = TVar::new(0);
    //   Transaction::with(|trans| {
    //       let r = read.read(trans)?;
    //       write.write(trans, r)
    //   });
    TVar<int> src(42);
    TVar<int> dst(0);
    atomically([&](Transaction& tx) {
        int r = src.read(tx);
        dst.write(tx, r);
        return 0;
    });
    std::cout << "Example 3: dst = " << dst.read_atomic() << std::endl;

    // Example 4: modify
    //
    // Rust:
    //   let var = TVar::new(21);
    //   atomically(|trans| var.modify(trans, |x| x*2));
    //   assert_eq!(var.read_atomic(), 42);
    TVar<int> mod_var(21);
    atomically([&](Transaction& tx) {
        mod_var.modify(tx, [](int v) { return v * 2; });
        return 0;
    });
    std::cout << "Example 4: modify 21*2 = " << mod_var.read_atomic() << std::endl;

    // Example 5: replace
    //
    // Rust:
    //   let var = TVar::new(0);
    //   let x = atomically(|trans| var.replace(trans, 42));
    //   assert_eq!(x, 0);
    //   assert_eq!(var.read_atomic(), 42);
    TVar<int> rep_var(0);
    int old = atomically([&](Transaction& tx) {
        return rep_var.replace(tx, 42);
    });
    std::cout << "Example 5: replace old=" << old
              << " new=" << rep_var.read_atomic() << std::endl;

    return 0;
}
