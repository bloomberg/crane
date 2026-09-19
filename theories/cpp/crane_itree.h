// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Reified interaction tree: a deferred computation that can be run or
// inspected.  R is the result type (use void for effectful computations
// that produce no value).  Tau is intentionally omitted -- it is a
// coinductive guardedness marker with no runtime meaning.
//
// Invariants (enforced here so host/generated code cannot forge invalid
// nodes):
//   * Nodes are only constructible through the ret/tau/vis factories, which
//     return a std::shared_ptr.  The constructor takes a private passkey, so
//     external code cannot build a node from a hand-crafted variant or stack
//     allocate one (a stack ITree would make shared_from_this throw)
//     (CWE-665 / CWE-476, finding 132).
//   * A Tau's next pointer and a Vis continuation's result are never null:
//     the factories reject a null argument up front and run() rechecks the
//     continuation result before dereferencing it (finding 132).
//   * run() keeps the current node alive for the whole loop via
//     shared_from_this -- including the void specialization, which must not
//     fabricate a non-owning alias of [this] that an effect could outlive
//     (CWE-416, finding 86).
//
// run() intentionally has no step budget: an itree is coinductive and may be
// legitimately infinite, so bounding it here would be wrong.  A caller that
// needs to stop a divergent computation controls that at its own effect
// boundary.

#ifndef INCLUDED_CRANE_ITREE
#define INCLUDED_CRANE_ITREE

#include <any>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <variant>

template <typename R>
struct ITree : public std::enable_shared_from_this<ITree<R>> {
    struct Ret { R value; };
    struct Tau { std::shared_ptr<ITree<R>> next; };
    struct Vis {
        std::function<std::any()> effect;
        std::function<std::shared_ptr<ITree<R>>(std::any)> cont;
    };
    using variant_t = std::variant<Ret, Tau, Vis>;
    variant_t node;

  private:
    // Passkey: only ITree's own factories can name it, so the public
    // constructor cannot be called from outside despite make_shared needing it.
    struct Private { explicit Private() = default; };

  public:
    ITree(Private, variant_t n) : node(std::move(n)) {}

    static std::shared_ptr<ITree<R>> ret(R value) {
        return std::make_shared<ITree<R>>(Private{}, Ret{std::move(value)});
    }
    static std::shared_ptr<ITree<R>> tau(std::shared_ptr<ITree<R>> next) {
        if (!next)
            throw std::invalid_argument("crane: ITree::tau given a null next");
        return std::make_shared<ITree<R>>(Private{}, Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<R>> vis(
        std::function<std::any()> effect,
        std::function<std::shared_ptr<ITree<R>>(std::any)> cont) {
        if (!effect || !cont)
            throw std::invalid_argument("crane: ITree::vis given a null effect or continuation");
        return std::make_shared<ITree<R>>(Private{}, Vis{std::move(effect), std::move(cont)});
    }

    R run() {
        // Hold an owning reference to the current node for the whole loop:
        // effects and continuations may drop every other owner, so a
        // non-owning alias would dangle (finding 86).
        auto cur = this->shared_from_this();
        while (true) {
            // Copy (not move) the payload: cur is reached via shared_ptr and
            // observe() lets callers hold onto and re-run the same tree, so
            // moving out of a shared node would corrupt it for later runs
            // (finding 37, CWE-664).
            if (auto *r = std::get_if<Ret>(&cur->node))
                return r->value;
            if (auto *t = std::get_if<Tau>(&cur->node)) {
                if (!t->next)
                    throw std::runtime_error("crane: ITree Tau has a null next");
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(cur->node);
            std::any response = v.effect();
            auto next = v.cont(std::move(response));
            if (!next)
                throw std::runtime_error("crane: ITree Vis continuation returned null");
            cur = std::move(next);
        }
    }
    const variant_t &observe() const { return node; }
};

// Void specialization (Ret holds nothing).
template <>
struct ITree<void> : public std::enable_shared_from_this<ITree<void>> {
    struct Ret { std::monostate value = {}; };
    struct Tau { std::shared_ptr<ITree<void>> next; };
    struct Vis {
        std::function<std::any()> effect;
        std::function<std::shared_ptr<ITree<void>>(std::any)> cont;
    };
    using variant_t = std::variant<Ret, Tau, Vis>;
    variant_t node;

  private:
    struct Private { explicit Private() = default; };

  public:
    ITree(Private, variant_t n) : node(std::move(n)) {}

    static std::shared_ptr<ITree<void>> ret() {
        return std::make_shared<ITree<void>>(Private{}, Ret{});
    }
    static std::shared_ptr<ITree<void>> ret(std::monostate) {
        return std::make_shared<ITree<void>>(Private{}, Ret{});
    }
    static std::shared_ptr<ITree<void>> tau(std::shared_ptr<ITree<void>> next) {
        if (!next)
            throw std::invalid_argument("crane: ITree::tau given a null next");
        return std::make_shared<ITree<void>>(Private{}, Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<void>> vis(
        std::function<std::any()> effect,
        std::function<std::shared_ptr<ITree<void>>(std::any)> cont) {
        if (!effect || !cont)
            throw std::invalid_argument("crane: ITree::vis given a null effect or continuation");
        return std::make_shared<ITree<void>>(Private{}, Vis{std::move(effect), std::move(cont)});
    }

    void run() {
        // Owning reference (not a non-owning alias of [this]): an effect or
        // continuation may release the last other owner mid-run (finding 86).
        auto cur = this->shared_from_this();
        while (true) {
            if (std::holds_alternative<Ret>(cur->node))
                return;
            if (auto *t = std::get_if<Tau>(&cur->node)) {
                if (!t->next)
                    throw std::runtime_error("crane: ITree Tau has a null next");
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(cur->node);
            std::any response = v.effect();
            auto next = v.cont(std::move(response));
            if (!next)
                throw std::runtime_error("crane: ITree Vis continuation returned null");
            cur = std::move(next);
        }
    }
    const variant_t &observe() const { return node; }
};

// Type alias for itreeF — makes template argument deduction work
// (typename ITree<R>::variant_t is a non-deduced context).
template<typename R>
using itreeF_t = typename ITree<R>::variant_t;

// Bind: graft the continuation onto every leaf of the first tree.
//
// A tree is data, so binding it performs no effect: a Ret hands its value to
// the continuation, a Vis keeps its event and binds whatever its own
// continuation yields, and a Tau keeps the step.  Only run() performs
// anything, which is what lets a tree be built over an event nothing here
// knows how to interpret.
//
// The continuation is taken by value, not by forwarding reference: a Vis
// stores it in the node it returns, which outlives this call.  K stays a
// generic callable (not a std::function) so lambdas deduce against it.
template<typename A, typename K>
auto itree_bind(std::shared_ptr<ITree<A>> m, K k)
    -> decltype(k(std::declval<A>())) {
    using tree_b = decltype(k(std::declval<A>()));
    using node_b = typename tree_b::element_type;
    if (!m)
        throw std::invalid_argument("crane: itree_bind given a null tree");
    if (auto *r = std::get_if<typename ITree<A>::Ret>(&m->node))
        return k(r->value);
    if (auto *t = std::get_if<typename ITree<A>::Tau>(&m->node))
        return node_b::tau(itree_bind(t->next, k));
    auto &v = std::get<typename ITree<A>::Vis>(m->node);
    auto cont = v.cont;
    return node_b::vis(
        v.effect,
        std::function<tree_b(std::any)>(
            [cont, k](std::any x) { return itree_bind(cont(std::move(x)), k); }));
}

// Bind specialization for void first argument.
template<typename K>
auto itree_bind(std::shared_ptr<ITree<void>> m, K k)
    -> decltype(k()) {
    using tree_b = decltype(k());
    using node_b = typename tree_b::element_type;
    if (!m)
        throw std::invalid_argument("crane: itree_bind given a null tree");
    if (std::get_if<typename ITree<void>::Ret>(&m->node))
        return k();
    if (auto *t = std::get_if<typename ITree<void>::Tau>(&m->node))
        return node_b::tau(itree_bind(t->next, k));
    auto &v = std::get<typename ITree<void>::Vis>(m->node);
    auto cont = v.cont;
    return node_b::vis(
        v.effect,
        std::function<tree_b(std::any)>(
            [cont, k](std::any x) { return itree_bind(cont(std::move(x)), k); }));
}

// Ret constructor with template argument deduction.  The result type is
// decayed: the argument commonly arrives as an xvalue (`std::move(n)`), and
// naming its `decltype` directly would ask for an `ITree<R&&>`.
template<typename A>
auto itree_ret(A &&value) {
    return ITree<std::decay_t<A>>::ret(std::forward<A>(value));
}

// Tau constructor with template argument deduction.
template<typename R>
auto itree_tau(std::shared_ptr<ITree<R>> next) {
    return ITree<R>::tau(std::move(next));
}

// The result of a trigger: one Vis node whose continuation returns the
// event's own response.
//
// The response type is an index of the event type, so it has no C++ spelling
// of its own and the tree cannot be named where the trigger is written.  The
// conversion operator lets the use site name it instead, which the enclosing
// signature always does.
struct itree_trigger_t {
    std::function<std::any()> effect;

    template <typename R>
    operator std::shared_ptr<ITree<R>>() const {
        return ITree<R>::vis(effect,
            std::function<std::shared_ptr<ITree<R>>(std::any)>(
                [](std::any x) {
                    return ITree<R>::ret(std::any_cast<R>(std::move(x)));
                }));
    }
};

// Trigger with template argument deduction.  An event given an effect
// spelling is already the thunk [ITree::vis] wants; one that is plain data is
// reified as the thunk that yields it, for a handler to interpret later.
template<typename E>
itree_trigger_t itree_trigger(E e) {
    if constexpr (std::is_invocable_r_v<std::any, E &>)
        return {std::function<std::any()>(std::move(e))};
    else
        return {[e = std::move(e)]() -> std::any { return std::any(e); }};
}

// Vis constructor with template argument deduction.  Deduces R from the
// continuation's return type (shared_ptr<ITree<R>>).
template<typename Effect, typename Cont>
auto itree_vis(Effect effect, Cont cont) {
    using TreePtr = std::invoke_result_t<Cont, std::any>;
    using TreeT = typename TreePtr::element_type;
    std::function<std::any()> eff;
    if constexpr (std::is_same_v<std::decay_t<Effect>, std::any>) {
        eff = std::any_cast<std::function<std::any()>>(effect);
    } else {
        eff = std::function<std::any()>(std::move(effect));
    }
    return TreeT::vis(std::move(eff),
        std::function<TreePtr(std::any)>(std::move(cont)));
}

#endif // INCLUDED_CRANE_ITREE
