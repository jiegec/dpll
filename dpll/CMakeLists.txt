cmake_minimum_required(VERSION 3.15)
project(dpll)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_CXX_FLAGS_DEBUG "$ENV{CXXFLAGS} -O0 -Wall -g -ggdb -fsanitize=address")
set(CMAKE_CXX_FLAGS_RELEASE "$ENV{CXXFLAGS} -O2 -Wall")

add_executable(dpll main.cpp DimacsParser.h common.h DPLL.cpp DPLL.h)
