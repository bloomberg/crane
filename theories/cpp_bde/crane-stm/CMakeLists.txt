cmake_minimum_required(VERSION 3.20)
project(crane-stm-bde VERSION 0.4.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Find BDE bsl package
find_package(bsl REQUIRED)

# Header-only library
add_library(crane-stm-bde INTERFACE)
target_include_directories(crane-stm-bde INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>
    $<INSTALL_INTERFACE:src>
)

# Find pthreads (needed for threading)
find_package(Threads REQUIRED)
target_link_libraries(crane-stm-bde INTERFACE bsl Threads::Threads)

# Tests
option(CRANE_STM_BDE_BUILD_TESTS "Build tests" ON)
if(CRANE_STM_BDE_BUILD_TESTS)
    enable_testing()

    add_executable(crane-stm-bde-tests
        tests/test_main.cpp
    )
    target_link_libraries(crane-stm-bde-tests PRIVATE crane-stm-bde)
    target_compile_options(crane-stm-bde-tests PRIVATE
        $<$<CXX_COMPILER_ID:GNU,Clang,AppleClang>:-Wall -Wextra -Wpedantic>
    )

    add_test(NAME crane-stm-bde-tests COMMAND crane-stm-bde-tests)
endif()

# Examples
option(CRANE_STM_BDE_BUILD_EXAMPLES "Build examples" ON)
if(CRANE_STM_BDE_BUILD_EXAMPLES)
    add_executable(crane-stm-bde-basic-example examples/basic.cpp)
    target_link_libraries(crane-stm-bde-basic-example PRIVATE crane-stm-bde)
endif()
