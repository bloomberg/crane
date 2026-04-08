#pragma once

// Port of stm-core/src/transaction/log_var.rs

#include <any>
#include <memory>
#include <optional>
#include <variant>

namespace stm {

/// Type-erased shared pointer, analogous to Rust's `Arc<dyn Any + Send + Sync>`.
using ArcAny = std::shared_ptr<void>;

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
    using Variant = std::variant<Read, Write, ReadWrite, ReadObsolete, ReadObsoleteWrite>;

    explicit LogVar(Variant v) : var_(std::move(v)) {}

    // Convenience factories matching Rust's enum constructors.
    static LogVar make_read(ArcAny v) { return LogVar(Read{std::move(v)}); }
    static LogVar make_write(ArcAny v) { return LogVar(Write{std::move(v)}); }

    /// Read a value and potentially upgrade the state.
    /// Mirrors Rust's `LogVar::read(&mut self) -> ArcAny`.
    ArcAny read() {
        // Visitor that returns the value and optionally upgrades the variant.
        ArcAny result;
        std::visit([&](auto& v) {
            using V = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<V, stm::detail::Read> ||
                          std::is_same_v<V, stm::detail::Write> ||
                          std::is_same_v<V, ReadWrite>) {
                result = v.value;
            } else if constexpr (std::is_same_v<V, ReadObsoleteWrite>) {
                result = v.value;
                // Upgrade to ReadWrite
                var_ = ReadWrite{v.original, v.value};
            } else if constexpr (std::is_same_v<V, ReadObsolete>) {
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
        std::visit([&](auto& v) {
            using V = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<V, stm::detail::Write>) {
                var_ = stm::detail::Write{std::move(w)};
            } else if constexpr (std::is_same_v<V, ReadObsolete>) {
                var_ = ReadObsoleteWrite{v.value, std::move(w)};
            } else if constexpr (std::is_same_v<V, ReadObsoleteWrite>) {
                var_ = ReadObsoleteWrite{v.original, std::move(w)};
            } else if constexpr (std::is_same_v<V, stm::detail::Read> ||
                                 std::is_same_v<V, ReadWrite>) {
                ArcAny orig;
                if constexpr (std::is_same_v<V, stm::detail::Read>) {
                    orig = v.value;
                } else {
                    orig = v.original;
                }
                var_ = ReadWrite{std::move(orig), std::move(w)};
            }
        }, var_);
    }

    /// Turn into an obsolete version for `or` branch merging.
    /// Write-only entries return nullopt (no read dependency to preserve).
    /// Mirrors Rust's `LogVar::obsolete(self) -> Option<LogVar>`.
    std::optional<LogVar> obsolete() && {
        auto read_val = std::move(*this).into_read_value();
        if (read_val) {
            return LogVar(ReadObsolete{std::move(*read_val)});
        }
        return std::nullopt;
    }

    /// Extract the original read value, ignoring writes.
    /// Write-only entries return nullopt.
    /// Mirrors Rust's `LogVar::into_read_value(self) -> Option<ArcAny>`.
    std::optional<ArcAny> into_read_value() && {
        return std::visit([](auto&& v) -> std::optional<ArcAny> {
            using V = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<V, stm::detail::Read>) {
                return std::move(v.value);
            } else if constexpr (std::is_same_v<V, ReadWrite>) {
                return std::move(v.original);
            } else if constexpr (std::is_same_v<V, ReadObsolete>) {
                return std::move(v.value);
            } else if constexpr (std::is_same_v<V, ReadObsoleteWrite>) {
                return std::move(v.original);
            } else {
                // Write — no read dependency
                return std::nullopt;
            }
        }, std::move(var_));
    }

    /// Access the underlying variant (for commit logic).
    const Variant& variant() const { return var_; }

private:
    Variant var_;
};

} // namespace detail
} // namespace stm
