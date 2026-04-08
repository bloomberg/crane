cmake_minimum_required(VERSION 3.20)
project(crane-stm VERSION 0.4.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Header-only library
add_library(crane-stm INTERFACE)
target_include_directories(crane-stm INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>
    $<INSTALL_INTERFACE:src>
)

# Find pthreads (needed for std::thread, std::mutex, etc.)
find_package(Threads REQUIRED)
target_link_libraries(crane-stm INTERFACE Threads::Threads)

# Tests
option(CRANE_STM_BUILD_TESTS "Build tests" ON)
if(CRANE_STM_BUILD_TESTS)
    enable_testing()

    add_executable(crane-stm-tests
        tests/test_main.cpp
    )
    target_link_libraries(crane-stm-tests PRIVATE crane-stm)
    target_compile_options(crane-stm-tests PRIVATE
        $<$<CXX_COMPILER_ID:GNU,Clang,AppleClang>:-Wall -Wextra -Wpedantic>
    )

    add_test(NAME crane-stm-tests COMMAND crane-stm-tests)
endif()

# Examples
option(CRANE_STM_BUILD_EXAMPLES "Build examples" ON)
if(CRANE_STM_BUILD_EXAMPLES)
    add_executable(crane-stm-basic-example examples/basic.cpp)
    target_link_libraries(crane-stm-basic-example PRIVATE crane-stm)
endif()
