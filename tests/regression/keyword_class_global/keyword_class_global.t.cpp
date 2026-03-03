// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <keyword_class_global.h>

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

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main()
{
    ASSERT(KeywordClassGlobal::t == 8u);
    return testStatus;
}
