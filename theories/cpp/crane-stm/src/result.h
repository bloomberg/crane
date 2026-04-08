#pragma once

// Port of stm-core/src/result.rs

namespace stm {

/// StmError represents the two failure modes of an STM step.
/// Mirrors Rust's `StmError` enum exactly.
enum class StmError {
    /// A variable the computation depends on has changed.
    Failure,

    /// `retry` was called — may block until a read variable changes.
    Retry,
};

} // namespace stm
