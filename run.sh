set -e
set -o xtrace
clang $(leanc --print-cflags) AllocatorAdversary.cpp  -c -o AllocatorAdversary.o 
lean MemoryAllocatorAdversary.lean -c adversary.c
leanc adversary.c AllocatorAdversary.o -o adversary
./adversary