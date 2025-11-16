# SAT Competition

This is my entry for a SAT solver competition at my university.

## Building

Simply compile `dpll.cpp` with any C++ compiler, e.g.:

```g++ dpll.cpp -o sat```

## Usage

This program takes input in the DIMACS CNF format from stdin. Example usage:

```./sat < problem.cnf```

(where `problem.cnf` is a file in DIMACS CNF format.)

Currently, only the unit propagation function is implemented.

## Licensing

This project is distributed under the GPL 3.0 license. See `COPYING` for more info.
