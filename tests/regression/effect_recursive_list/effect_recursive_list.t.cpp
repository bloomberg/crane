#include <effect_recursive_list.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

// Helper to convert List to vector for easier testing
template<typename T>
std::vector<T> to_vec(const std::shared_ptr<List<T>>& lst) {
    std::vector<T> result;
    auto cur = lst;
    while (cur && std::holds_alternative<typename List<T>::Cons>(cur->v())) {
        auto& cons = std::get<typename List<T>::Cons>(cur->v());
        result.push_back(cons.d_a0);
        cur = cons.d_a1;
    }
    return result;
}

int main() {
    // 1. read_n_lines
    {
        std::istringstream input("alpha\nbeta\ngamma\n");
        std::cin.rdbuf(input.rdbuf());
        auto lst = EffectRecursiveList::read_n_lines(3u);
        auto v = to_vec(lst);
        assert(v.size() == 3);
        assert(v[0] == "alpha");
        assert(v[1] == "beta");
        assert(v[2] == "gamma");
    }

    // 4. store_lines
    {
        std::istringstream input("val1\nval2\n");
        std::cin.rdbuf(input.rdbuf());
        auto count = EffectRecursiveList::store_lines("K", 2u);
        assert(count == 2u);
    }

    // 5. collect_envs
    {
        setenv("A", "alpha", 1);
        setenv("B", "beta", 1);
        unsetenv("C");
        auto names = List<std::string>::cons("A",
                     List<std::string>::cons("B",
                     List<std::string>::cons("C",
                     List<std::string>::nil())));
        auto vals = EffectRecursiveList::collect_envs(names);
        auto v = to_vec(vals);
        assert(v.size() == 3);
        assert(v[0].has_value());
        assert(*v[0] == "alpha");
        assert(v[1].has_value());
        assert(*v[1] == "beta");
        assert(!v[2].has_value());

        unsetenv("A");
        unsetenv("B");
    }

    // 6. read_and_prepend
    {
        std::istringstream input("prepended\n");
        std::cin.rdbuf(input.rdbuf());
        auto existing = List<std::string>::cons("existing",
                        List<std::string>::nil());
        auto lst = EffectRecursiveList::read_and_prepend(existing);
        auto v = to_vec(lst);
        assert(v.size() == 2);
        assert(v[0] == "prepended");
        assert(v[1] == "existing");
    }

    return 0;
}
