# Temp benchmark results (to be included in docs later)

FIXME(benchmarks): These are very incomplete benchmarks for now. I want a nice table with different L1 values.

CPU: AMD Ryzen 7 5700U with Radeon Graphics (my laptop)
Thread(s) per core:  2
Core(s) per socket:  8

L1 = 26, fast ecdlp (1 thread) for a range of 48bit:
- runtime: 1.6s
- size of the table file: 333Mo

General rules:
1. Increasing L1 by one bit will result in ~doubling the size of the table file (as long as L1 is large enough for the T1 table to dominate the footprint).
2. Decreasing the input range by one bit will halve the runtime. 
3. Adding another thread will ~halve the runtime (as long as we can use more cpu cores, and with logical vs physical core caveats)

Some more benchmarks 
- fast ecdlp 1 threads: 1.6155 s
- par fast ecdlp 2 threads: 887.46 ms
- par fast ecdlp 4 threads: 533.73 ms
- fast ecdlp find 0: 299.65 µs
- fast ecdlp for number < 2^47: 386.68 ms
- fast ecdlp for number < 2^44: 48.593 ms
- fast ecdlp for number < 2^43: 22.916 ms
- fast ecdlp for number < 2^26: 276.64 µs
