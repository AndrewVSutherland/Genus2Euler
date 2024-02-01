# Genus2Euler

Code and data associated to the paper *Computing Euler factors of genus 2 curves over Q at primes of almost good reduction*, by [Céline Maistret](https://sites.google.com/view/cmaistret/home) and [Andrew V. Sutherland](https://math.mit.edu/~drew).

- The package file `genus2euler.m` implements Algorithm 7 of the paper as a Magma intrinsic `Genus2AlmostGoodEulerFactor`.
- The text file `EulerFactorHardCases.txt` lists tuples `case:p:[f0,...,f6],[a1,a2]:t1:t2:t3`, where `case`= 1,2,3,4 indicates the type **1**, **2a**, **2b**, **4** defined in the paper, `p` is an odd prime of almost good reduction for the genus 2 hyperelliptic curve y^2=f(x) defined by the coefficients f0,...,f6, a1 and a2 are the linear and quadratic coefficients of the L-polynomial Lp(C,T), and t1,t2,t3 are running times (in seconds) for the existing Magma intrinsic `EulerFactor`, the new Magma intrinsic `AlmostGoodEulerFactor`, and our low level C implementation, respectively.
- The text file `EulerFactorFailureCases.txt` lists 489 tuples in the format above where the existing Magma intrinsic `EulerFactor` failed to terminated (here t1 is capped at 8 hours).
