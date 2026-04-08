# crane-stm Design Note

A faithful C++20 port of [rust-stm](https://github.com/Marthog/rust-stm).

## Architecture Summary (Rust source)

The Rust library provides composable Software Transactional Memory via optimistic
concurrency control. Key components:

| Rust module | Role |
|---|---|
| `result.rs` | `StmError` enum (`Failure`, `Retry`) and `StmResult<T>` alias |
| `transaction/log_var.rs` | `LogVar` enum tracking per-variable read/write state within a transaction log |
| `transaction/control_block.rs` | `ControlBlock` — per-thread park/unpark coordination for blocking on `retry()` |
| `tvar.rs` | `VarControlBlock` (value + waiters + dead-thread cleanup) and `TVar<T>` (type-safe wrapper) |
| `transaction/mod.rs` | `Transaction` (BTreeMap log, read/write/or/commit/wait_for_change), `TransactionGuard`, `TransactionControl` |
| `lib.rs` | Free functions: `atomically`, `retry`, `guard`, `unwrap_or_retry`, `optionally` |

Execution model:
1. Transaction runs user closure, logging reads/writes in a `BTreeMap<Arc<VarControlBlock>, LogVar>`.
2. On success, two-phase commit: acquire locks in address order, verify read consistency (Arc pointer equality), write back, wake waiters.
3. On `Failure` (conflict detected), clear log and retry.
4. On `Retry` (explicit), register with read-set variables, park thread, wake when any variable changes.

## Rust → C++ Type Mapping

| Rust | C++ | Fidelity |
|---|---|---|
| `Arc<T>` | `std::shared_ptr<T>` | Exact — both are thread-safe reference-counted pointers |
| `Weak<T>` | `std::weak_ptr<T>` | Exact |
| `Arc<dyn Any + Send + Sync>` | `std::shared_ptr<void>` with type-erased deleter | Approximate — C++ `shared_ptr<void>` preserves the deleter; downcast via `static_pointer_cast` since we control the stored type |
| `parking_lot::RwLock` | `std::shared_mutex` | Close — both provide reader-writer locking; `parking_lot` is non-poisoning, C++ mutexes don't poison either |
| `parking_lot::Mutex` | `std::mutex` | Close — same non-poisoning semantics |
| `BTreeMap<Arc<VarControlBlock>, LogVar>` | `std::map<std::shared_ptr<VarControlBlock>, LogVar, VarControlBlockPtrCmp>` | Exact — both are ordered maps; custom comparator orders by raw pointer address (matching Rust's `Ord` impl on `VarControlBlock`) |
| `StmError` enum | `enum class StmError` | Exact |
| `StmResult<T>` = `Result<T, StmError>` | `StmResult<T>` — custom result type or internal exceptions | See below |
| `LogVar` enum (5 variants with data) | `std::variant<Read, Write, ReadWrite, ReadObsolete, ReadObsoleteWrite>` | Exact — `std::variant` maps directly to Rust tagged enums |
| `thread::park` / `unpark` | `std::mutex` + `std::condition_variable` | Approximate — C++ lacks direct park/unpark; condvar achieves the same semantics |
| `thread_local!(Cell<bool>)` | `thread_local bool` | Exact |
| `PhantomData<T>` | Not needed — C++ templates carry type info without phantom markers | N/A |
| `AtomicUsize` / `AtomicBool` | `std::atomic<size_t>` / `std::atomic<bool>` | Exact |

### StmResult control flow

Rust uses `Result<T, StmError>` with `?` for early return. C++ has no direct equivalent of `?`.
Options considered:

1. **Internal exceptions** — `StmError` values thrown as C++ exceptions inside transaction closures, caught by the transaction loop. This preserves the ergonomics of early return without requiring the user to manually propagate errors.
2. **Manual result type** — would require every lambda to return a result and every call site to check it.

Choice: **internal exceptions**. The transaction boundary (`atomically` / `Transaction::with`) catches `StmError` exceptions and handles them identically to how Rust handles `Err(Failure)` and `Err(Retry)`. The public API shape is preserved: user functions return `T` (not `StmResult<T>`), and `retry()` / `guard()` throw instead of returning `Err`. This is the one significant departure from the Rust source shape, forced by C++ lacking `?`.

The user-facing API becomes:
- `atomically([](Transaction& tx) -> T { ... })` — return `T` directly, call `retry()` to abort/block
- `retry<T>()` — throws `StmError::Retry`
- `guard(bool)` — throws `StmError::Retry` if false

This keeps the public semantics identical while adapting to C++ idioms.

## File Structure

```
crane-stm/
├── CMakeLists.txt
├── DESIGN.md
├── include/stm/
│   ├── stm.hpp                      # Top-level header (≈ src/lib.rs re-exports)
│   ├── result.hpp                   # StmError enum
│   ├── tvar.hpp                     # VarControlBlock + TVar<T>
│   └── transaction/
│       ├── transaction.hpp          # Transaction class
│       ├── control_block.hpp        # ControlBlock
│       └── log_var.hpp              # LogVar
├── tests/
│   ├── test_main.cpp                # Test runner
│   ├── test_transaction.cpp         # Transaction tests
│   ├── test_control_block.cpp       # ControlBlock tests
│   ├── test_tvar.cpp                # TVar tests
│   └── test_stm.cpp                 # Top-level API tests (lib.rs tests)
└── examples/
    └── basic.cpp                    # README examples
```

## Synchronization Primitives

| Purpose | Primitive | Why |
|---|---|---|
| Protecting `VarControlBlock::waiting_threads` | `std::mutex` | Matches `parking_lot::Mutex` — short critical sections, no readers-vs-writers distinction needed |
| Protecting `VarControlBlock::value` | `std::shared_mutex` | Matches `parking_lot::RwLock` — commit takes write lock, reads take shared lock |
| Thread parking in `ControlBlock` | `std::mutex` + `std::condition_variable` | C++ lacks `thread::park`/`unpark`; condvar is the standard equivalent |
| Dead-thread count | `std::atomic<size_t>` | Matches `AtomicUsize` |
| Blocked flag in `ControlBlock` | `std::atomic<bool>` | Matches `AtomicBool` |
| Nested transaction guard | `thread_local bool` | Matches `thread_local!(Cell<bool>)` |

## Unavoidable Mismatches

1. **No `?` operator** — Rust's `?` for `StmResult` propagation has no C++ equivalent. Using exceptions internally to replicate early-return semantics. User closures return `T` directly instead of `StmResult<T>`.

2. **No `Arc::ptr_eq` for `shared_ptr<void>`** — Rust checks read consistency via `Arc::ptr_eq`. C++ equivalent is comparing `.get()` raw pointers on `shared_ptr<void>`. Semantically identical.

3. **Type erasure** — Rust uses `Arc<dyn Any>` with runtime `downcast_ref`. C++ uses `shared_ptr<void>` with `static_pointer_cast<T>` (safe because we control what goes in). No runtime type check, but the type safety is enforced by `TVar<T>` at the API boundary, same as Rust.

4. **Destructor vs Drop** — Rust's `Drop` for `TransactionGuard` maps to C++ destructor. Semantically identical for RAII.

5. **Clone semantics** — `LogVar::Clone` in Rust is handled by explicit copy in C++ (variant copies naturally).

6. **`thread::park`/`unpark`** — Replaced with condvar. The semantics are preserved: `wait()` blocks until `set_changed()` signals, with the atomic bool preventing missed wakeups.

7. **Nested transaction detection** — Rust uses `assert!` which panics (catchable via `#[should_panic]` in tests). C++ uses `throw std::logic_error` since `assert()` aborts the process and cannot be caught. Behavior is identical: nested `atomically` calls are rejected at runtime.

8. **`or` method naming** — Rust's `Transaction::or` is renamed to `Transaction::or_` in C++ because `or` is a reserved keyword (alternative token for `||`).

9. **Header-only library** — The Rust crate is compiled as a library. The C++ port is header-only since all types are templates or small enough to inline. This is a packaging difference, not a semantic one.

## Test Coverage

All 29 Rust tests have been ported and pass:

| Category | Tests |
|---|---|
| TVar | `test_read_atomic` |
| LogVar | `test_write_obsolete_ignore` |
| ControlBlock | `blocked`, `wait_after_change`, `wait_after_multiple_changes`, `wait_threaded_wakeup` |
| Transaction | `simple`, `read`, `write`, `copy`, `log_read`, `log_write_read`, `with_control_abort_on_single_run`, `with_control_abort_on_retry`, `nested_fail` |
| STM API | `infinite_retry`, `stm_nested`, `threaded`, `read_write_interfere`, `or_simple`, `or_nocommit`, `or_nested_first`, `or_nested_second`, `guard_true`, `guard_false`, `optionally_succeed`, `optionally_fail`, `unwrap_some`, `unwrap_none` |
