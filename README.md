# fieldSAT

This is my entry for a SAT solver competition at my university (which won the competition!).

## Building

Simply compile `fieldSAT.cpp` with any C++ compiler, e.g.:

```g++ fieldSAT.cpp -o fieldSAT```

## Usage

This program takes input in the DIMACS CNF format from stdin. Example usage:

```./fieldSAT < problem.cnf```

(where `problem.cnf` is a file in DIMACS CNF format.)

The `-v` flag will make the solver output more information about which variable it is assigning/propagating/deciding, where it is backjumping to, etc.

## Licensing

This project is distributed under the GPL 3.0 license. See `COPYING` for more info.
