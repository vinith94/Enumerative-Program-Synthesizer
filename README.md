# Enumerative-Program-Synthesizer

Uses Enumerative techniques for program synthesis

Input specifications are given according to SyGuS format

Expressions are generated using bottom up enumeration

Uses Z3 SMT solver to check against specification

Currently works only in LIA track

Pruning of Search space using Equivalence - InProgress

Counter Examples generation - Done

Using Counter Examples for verifying the expressions against specification before invoking SMT - InProgress

------------
Dependencies
------------
Flex, Bison

-----------
Compilation
-----------
make

----------------
Sample Execution
----------------

./bin/debug/Solver  inputs/max2.sl

------
Output
------

Distinct Counter Example Points generated are: <br />
x = 1 y = 1 <br />
x = -1 y = 0 <br />
x = 0 y = 0 <br />
x = -1 y = -1 <br />
x = -2 y = -2 <br />
x = 2 y = 0 <br />

Hurray! Synthesized Expression is: (ite (<= y x) x y)




