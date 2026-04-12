// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Reified interaction tree: a deferred computation that can be run or
// inspected.  R is the result type (use void for effectful computations
// that produce no value).  Tau is intentionally omitted -- it is a
// coinductive guardedness marker with no runtime meaning.

#ifndef INCLUDED_CRANE_ITREE
#define INCLUDED_CRANE_ITREE

#include <any>
#include <functional>
#include <memory>
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

    explicit ITree(variant_t n) : node(std::move(n)) {}

    static std::shared_ptr<ITree<R>> ret(R value) {
        return std::make_shared<ITree<R>>(Ret{std::move(value)});
    }
    static std::shared_ptr<ITree<R>> tau(std::shared_ptr<ITree<R>> next) {
        return std::make_shared<ITree<R>>(Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<R>> vis(
        std::function<std::any()> effect,
        std::function<std::shared_ptr<ITree<R>>(std::any)> cont) {
        return std::make_shared<ITree<R>>(Vis{std::move(effect), std::move(cont)});
    }

    R run() {
        auto cur = this->shared_from_this();
        while (true) {
            if (auto *r = std::get_if<Ret>(&cur->node))
                return std::move(r->value);
            if (auto *t = std::get_if<Tau>(&cur->node)) {
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(cur->node);
            std::any response = v.effect();
            cur = v.cont(std::move(response));
        }
    }
    const variant_t &observe() const { return node; }
};

// Void specialization (Ret holds nothing).
template <>
struct ITree<void> {
    struct Ret { std::monostate value = {}; };
    struct Tau { std::shared_ptr<ITree<void>> next; };
    struct Vis {
        std::function<std::any()> effect;
        std::function<std::shared_ptr<ITree<void>>(std::any)> cont;
    };
    using variant_t = std::variant<Ret, Tau, Vis>;
    variant_t node;

    explicit ITree(variant_t n) : node(std::move(n)) {}

    static std::shared_ptr<ITree<void>> ret() {
        return std::make_shared<ITree<void>>(Ret{});
    }
    static std::shared_ptr<ITree<void>> ret(std::monostate) {
        return std::make_shared<ITree<void>>(Ret{});
    }
    static std::shared_ptr<ITree<void>> tau(std::shared_ptr<ITree<void>> next) {
        return std::make_shared<ITree<void>>(Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<void>> vis(
        std::function<std::any()> effect,
        std::function<std::shared_ptr<ITree<void>>(std::any)> cont) {
        return std::make_shared<ITree<void>>(Vis{std::move(effect), std::move(cont)});
    }

    void run() {
        // Non-owning shared_ptr: safe because we stay in scope for the
        // duration of the loop.
        auto cur = std::shared_ptr<ITree<void>>(this, [](auto *) {});
        while (true) {
            if (std::holds_alternative<Ret>(cur->node))
                return;
            if (auto *t = std::get_if<Tau>(&cur->node)) {
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(cur->node);
            std::any response = v.effect();
            cur = v.cont(std::move(response));
        }
    }
    const variant_t &observe() const { return node; }
};

// Type alias for itreeF — makes template argument deduction work
// (typename ITree<R>::variant_t is a non-deduced context).
template<typename R>
using itreeF_t = typename ITree<R>::variant_t;

// Bind: run the first tree, feed its result to the continuation.
// Uses generic callable K (not std::function) so lambdas participate
// in template argument deduction.
template<typename A, typename K>
auto itree_bind(std::shared_ptr<ITree<A>> m, K &&k)
    -> decltype(k(std::declval<A>())) {
    A result = m->run();
    return std::forward<K>(k)(std::move(result));
}

// Bind specialization for void first argument.
template<typename K>
auto itree_bind(std::shared_ptr<ITree<void>> m, K &&k)
    -> decltype(k()) {
    m->run();
    return std::forward<K>(k)();
}

// Vis constructor with template argument deduction.  Deduces R from the
// continuation's return type (shared_ptr<ITree<R>>).
template<typename Effect, typename Cont>
auto itree_vis(Effect effect, Cont cont) {
    using TreePtr = std::invoke_result_t<Cont, std::any>;
    using TreeT = typename TreePtr::element_type;
    return TreeT::vis(
        std::function<std::any()>(std::move(effect)),
        std::function<TreePtr(std::any)>(std::move(cont)));
}

#endif // INCLUDED_CRANE_ITREE
