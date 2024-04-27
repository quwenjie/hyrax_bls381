cmake_minimum_required(VERSION 3.10)
project(hyrax_bls12_381)
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC -mcmodel=medium -O2")
#set (CMAKE_CXX_FLAGS "-mcmodel=large -O2")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--no-relax,-z,notext")

include_directories(src)
include_directories(3rd/mcl/include)
include_directories(..)

add_subdirectory(src)
add_subdirectory(3rd/mcl)
