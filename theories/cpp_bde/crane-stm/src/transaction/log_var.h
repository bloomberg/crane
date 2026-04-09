#pragma once

// Port of stm-core/src/transaction/log_var.rs

#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>

namespace stm {

/// Type-erased shared pointer, analogous to Rust's `Arc<dyn Any + Send + Sync>`.
using ArcAny = bsl::shared_ptr<void>;

namespace detail {

/// LogVar tracks whether a variable was read, written, or both within a transaction.
/// Mirrors the Rust `LogVar` enum with 5 variants exactly.
///
/// Each variant struct holds the relevant ArcAny values:
///   Read(original)
///   Write(new_value)
///   ReadWrite(original, new_value)
///   ReadObsolete(original)           — read on a failed `or` branch
///   ReadObsoleteWrite(original, new_value) — read+write on a failed `or` branch

struct Read {
    ArcAny value;
};

struct Write {
    ArcAny value;
};

struct ReadWrite {
    ArcAny original;
    ArcAny value;
};

struct ReadObsolete {
    ArcAny value;
};

struct ReadObsoleteWrite {
    ArcAny original;
    ArcAny value;
};

class LogVar {
public:
    using Variant = bsl::variant<Read, Write, ReadWrite, ReadObsolete, ReadObsoleteWrite>;

    explicit LogVar(Variant v) : var_(bsl::move(v)) {}

    // Convenience factories matching Rust's enum constructors.
    static LogVar make_read(ArcAny v) { return LogVar(Read{bsl::move(v)}); }
    static LogVar make_write(ArcAny v) { return LogVar(Write{bsl::move(v)}); }

    /// Read a value and potentially upgrade the state.
    /// Mirrors Rust's `LogVar::read(&mut self) -> ArcAny`.
    ArcAny read() {
        // Visitor that returns the value and optionally upgrades the variant.
        ArcAny result;
        bsl::visit([&](auto& v) {
            using V = bsl::decay_t<decltype(v)>;
            if constexpr (bsl::is_same_v<V, stm::detail::Read> ||
                          bsl::is_same_v<V, stm::detail::Write> ||
                          bsl::is_same_v<V, ReadWrite>) {
                result = v.value;
            } else if constexpr (bsl::is_same_v<V, ReadObsoleteWrite>) {
                result = v.value;
                // Upgrade to ReadWrite
                var_ = ReadWrite{v.original, v.value};
            } else if constexpr (bsl::is_same_v<V, ReadObsolete>) {
                result = v.value;
                // Upgrade to Read
                var_ = stm::detail::Read{v.value};
            }
        }, var_);
        return result;
    }

    /// Write a value and potentially upgrade the state.
    /// Mirrors Rust's `LogVar::write(&mut self, w: ArcAny)`.
    void write(ArcAny w) {
        bsl::visit([&](auto& v) {
            using V = bsl::decay_t<decltype(v)>;
            if constexpr (bsl::is_same_v<V, stm::detail::Write>) {
                var_ = stm::detail::Write{bsl::move(w)};
            } else if constexpr (bsl::is_same_v<V, ReadObsolete>) {
                var_ = ReadObsoleteWrite{v.value, bsl::move(w)};
            } else if constexpr (bsl::is_same_v<V, ReadObsoleteWrite>) {
                var_ = ReadObsoleteWrite{v.original, bsl::move(w)};
            } else if constexpr (bsl::is_same_v<V, stm::detail::Read> ||
                                 bsl::is_same_v<V, ReadWrite>) {
                ArcAny orig;
                if constexpr (bsl::is_same_v<V, stm::detail::Read>) {
                    orig = v.value;
                } else {
                    orig = v.original;
                }
                var_ = ReadWrite{bsl::move(orig), bsl::move(w)};
            }
        }, var_);
    }

    /// Turn into an obsolete version for `or` branch merging.
    /// Write-only entries return nullopt (no read dependency to preserve).
    /// Mirrors Rust's `LogVar::obsolete(self) -> Option<LogVar>`.
    bsl::optional<LogVar> obsolete() && {
        auto read_val = bsl::move(*this).into_read_value();
        if (read_val) {
            return LogVar(ReadObsolete{bsl::move(*read_val)});
        }
        return bsl::nullopt;
    }

    /// Extract the original read value, ignoring writes.
    /// Write-only entries return nullopt.
    /// Mirrors Rust's `LogVar::into_read_value(self) -> Option<ArcAny>`.
    bsl::optional<ArcAny> into_read_value() && {
        return bsl::visit([](auto&& v) -> bsl::optional<ArcAny> {
            using V = bsl::decay_t<decltype(v)>;
            if constexpr (bsl::is_same_v<V, stm::detail::Read>) {
                return bsl::move(v.value);
            } else if constexpr (bsl::is_same_v<V, ReadWrite>) {
                return bsl::move(v.original);
            } else if constexpr (bsl::is_same_v<V, ReadObsolete>) {
                return bsl::move(v.value);
            } else if constexpr (bsl::is_same_v<V, ReadObsoleteWrite>) {
                return bsl::move(v.original);
            } else {
                // Write — no read dependency
                return bsl::nullopt;
            }
        }, bsl::move(var_));
    }

    /// Access the underlying variant (for commit logic).
    const Variant& variant() const { return var_; }

private:
    Variant var_;
};

} // namespace detail
} // namespace stm
