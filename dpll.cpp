/* dpll.cpp - SAT solver for competition
Copyright (C) 2025 fieldbox

This program is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program. If not, see <https://www.gnu.org/licenses/>.*/

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

struct Clause {
  std::vector<int> literals;
  int watch1;
  int watch2;
};

enum Value { TRUE, FALSE, UNASSIGNED };

int num_vars, num_clauses;
std::vector<Clause> clauses;
std::vector<int> trail;
int trail_head = 0;
std::vector<Value> assignments;
std::vector<std::vector<Clause *>> watchers;

int get_watcher_index(int literal) {
  return (literal > 0)
             ? 2 * literal - 1
             : 2 * -literal - 2; // maps the integers (without 0) to the natural
                                 // numbers (including 0), since we need to keep
                                 // track of both positive and negative literals
}

Value value_of(int literal) {
  Value assignment = assignments[std::abs(literal)];
  if (assignment == UNASSIGNED) {
    return UNASSIGNED;
  }

  int signbit = assignment == TRUE
                    ? 0
                    : 1; // if true, then positive, i.e. sign bit will be 1
  if (std::signbit(literal) ==
      signbit) { // if the sign bits are equal, then the literals are equal. so
                 // if that literal is in the assignment list, then it is true
    return TRUE;
  } else {
    return FALSE;
  }
}

bool propagate() {
  while (trail_head < trail.size()) {
    int literal = trail[trail_head];
    int index = get_watcher_index(-literal);

    for (int i = 0; i < watchers[index].size();) {
      Clause &clause = *watchers[index][i];
      int watch_num, other_watch;
      if (clause.literals[clause.watch1] == -literal) {
        watch_num = 1;
        other_watch = clause.literals[clause.watch2];
      } else {
        watch_num = 2;
        other_watch = clause.literals[clause.watch1];
      }
      if (value_of(other_watch) == TRUE) {
        continue; // clause is already satisfied; do nothing
      }

      bool changed = false;
      int watch1 = clause.literals[clause.watch1];
      int watch2 = clause.literals[clause.watch2];
      for (int j = 0; j < clause.literals.size(); j++) {
        int lit = clause.literals[j];
        if (lit == watch1 || lit == watch2) {
          continue;
        }
        if (value_of(lit) != FALSE) {
          changed = true;
          if (watch_num == 1)
            clause.watch1 = j;
          else
            clause.watch2 = j;
          watchers[get_watcher_index(lit)].push_back(&clause);
          watchers[index][i] = watchers[index].back();
          watchers[index].pop_back();
          break;
        }
      }

      if (changed == true) {
        continue;
      } // found another non-false literal to watch; do nothing

      if (value_of(other_watch) == FALSE) {
        return false; // all literals are false, conflict found; return false
      } else {
        trail.push_back(other_watch); // all literals but one are false;
                                      // propagate the new unit clause
        assignments[std::abs(literal)] =
            literal > 0 ? TRUE : FALSE; // a new unit is being propagated, so we
                                        // need to assign it
        i++;
      }
    }
    trail_head++;
  }
  return true;
}

void parse() {
  std::string literal;

  while (std::cin >> literal) {
    if (literal == "c") {
      std::getline(
          std::cin,
          literal); // lines starting with c are comments, so ignore line
    } else if (literal == "p") {
      std::string string_num_vars, string_num_clauses;

      std::cin >> literal >> string_num_vars >>
          string_num_clauses; // after the p is "cnf", which can be ignored,
                              // then the number of variables and clauses

      num_vars = std::stoi(string_num_vars);
      num_clauses = std::stoi(string_num_clauses);
    } else {
      std::vector<int> clause;
      while (literal != "0") { // clauses are terminated with 0
        clause.push_back(std::stoi(literal));
        std::cin >> literal;
      }
      clauses.push_back(
          {clause, 0, 0}); // the 0s are temporary values; on initialisation,
                           // they will be given indices for watched literals
    }
  }
  assignments.resize(num_vars + 1); // the assignment vector is 1-indexed
  std::fill(assignments.begin(), assignments.end(),
            UNASSIGNED); // all variables start unassigned

  watchers.resize(
      2 * num_vars); // the watchers array is indexed over each literal (i.e.
                     // positive and negative propositional variables)
}

void initialise() {
  for (int i = 0; i < clauses.size(); i++) {
    if (clauses[i].literals.size() == 1) {
      int literal = clauses[i].literals[0];
      trail.push_back(literal); // unit clause, so add its literal to the
                                // trail to be propagated
      assignments[std::abs(literal)] = literal > 0 ? TRUE : FALSE;
    } else {
      watchers[get_watcher_index(clauses[i].literals[0])].push_back(
          &clauses[i]); // add the first two literals as watched literals to the
                        // watchers array and struct attributes
      watchers[get_watcher_index(clauses[i].literals[1])].push_back(
          &clauses[i]);
      clauses[i].watch1 = 0;
      clauses[i].watch2 = 1;
    }
  }
}

int main(void) {
  parse();
  initialise();
  std::cout << (propagate() == true ? "SATISFIABLE" : "UNSATISFIABLE")
            << std::endl;
  return 0;
}
