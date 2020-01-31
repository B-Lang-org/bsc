cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

IF(DEFINED CMAKE_BUILD_TYPE)
    SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ELSE()
  SET(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ENDIF()

#set(CMAKE_C_COMPILER "gcc-4.4")
#set(CMAKE_CXX_COMPILER "/usr/bin/g++-4.4")

PROJECT(cryptoms)
SET(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O3 -Wall -Werror -g -mtune=native")
SET(CMAKE_CXX_FLAGS_DEBUG "-Wall -Werror -O0 -ggdb")
SET(CMAKE_CXX_FLAGS_RELEASE "-Wall -fprofile-use -Werror -O3 -g0 -fno-exceptions -DNDEBUG -mtune=native -fomit-frame-pointer")
SET(CMAKE_EXE_LINKER_FLAGS "-static")

find_package( ZLIB )
link_directories( ${ZLIB_LIBRARY} )
include_directories( ${ZLIB_INCLUDE_DIR} )

find_package(Boost REQUIRED)

add_definitions(-DVERSION="STP version")

include_directories(mtl)
include_directories(MTRand)

add_executable(cryptominisat
    Logger.cpp
    Solver.cpp
    Gaussian.cpp
    PackedRow.cpp
    XorFinder.cpp
    MatrixFinder.cpp
    VarReplacer.cpp
    FindUndef.cpp
    ClauseCleaner.cpp
    RestartTypeChooser.cpp
    FailedVarSearcher.cpp
    PartFinder.cpp
    Subsumer.cpp
    PartHandler.cpp
    XorSubsumer.cpp
    StateSaver.cpp
    ClauseAllocator.cpp
    UselessBinRemover.cpp
    OnlyNonLearntBins.cpp
    Main.cpp
)

target_link_libraries(cryptominisat
    ${ZLIB_LIBRARY}
    ${Boost_LIBRARIES}
)


