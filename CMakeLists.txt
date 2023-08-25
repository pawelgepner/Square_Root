cmake_minimum_required(VERSION 3.21)
project(SQRTCPP)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_OSX_ARCHITECTURES x86_64)

add_executable(SQRTCPP main.cpp half.hpp)
