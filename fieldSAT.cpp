/* fieldSAT.cpp - SAT solver for competition
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
#include <cstring>
#include <iostream>
#include <ostream>
#include <string>
#include <vector>

struct Clause {
  std::vector<int> literals;
  int watch1;
  int watch2;
  double activity = 0;   // only relevant for learned clauses
  bool toRemove = false; // only relevant for learned clauses
};

enum Value { TRUE, FALSE, UNASSIGNED };

bool verbose = false;

int num_vars, num_clauses;
std::vector<Clause *> clauses;

std::vector<int> trail; // all assignments in chronological order
int trail_head = 0;     // index of the most recently propagated assignment

std::vector<Value> assignments; // all assignments, indexed by variable
int assigned_vars = 0;          // number of variables that are assigned

std::vector<Value> last_assignments; // last assignment to each variable,
                                     // ignoring backtracking. used when
                                     // deciding a variable's value, and
                                     // defaults to false

std::vector<std::vector<Clause *>>
    watchers; // contains lists of all clauses watching a literal, indexed by
              // literal using get_literal_index()

std::vector<int> trail_decisions; // index of the beginning of each decision
                                  // level in the trail
std::vector<int>
    decision_levels; // decision level each variable was assigned at

std::vector<Clause *> reasons; // clause that implies each variable's value

Clause *conflict_clause; // most recent conflict clause

std::vector<double> activity; // activity of a variable, indexed by variable
const double activity_inc =
    1; // amount to increment activity by when a conflict is found
const double activity_decay =
    0.95; // amount to decay activity by when a conflict is found

std::vector<Clause *> learned_clauses; // pointers to all learned clauses
int num_conflicts;                     // number of conflicts that have occurred
const int reduction_threshold =
    3000; // threshold of number of conflicts before the clause list is reduced
const double clause_activity_inc =
    1; // amount to increase clause activity by when a conflict is found
const double clause_activity_decay =
    0.95; // amount to decay clause activity by when a conflict is found

int max_conflicts =
    100; // threshold of number of conflicts before solver is restarted

int get_literal_index(
    int literal) { // some lists are indexed by literal, which can be positive
                   // or negative (but not 0). this function maps the positive
                   // and negative integers to the natural numbers to work as
                   // indices for these lists.
  return (literal > 0) ? 2 * literal - 1 : 2 * -literal - 2;
}

Value value_of(int literal) { // get the value of a literal
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

bool propagate() { // propagate any literals queued in the trail, then the
                   // literals from any unit clauses onto the trail
  while (trail_head < trail.size()) {
    int literal = trail[trail_head];
    int index = get_literal_index(-literal);

    if (verbose)
      std::cout << "propagating " << literal << "..." << std::endl;

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
        i++;
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
          watchers[get_literal_index(lit)].push_back(&clause);
          watchers[index][i] = watchers[index].back();
          watchers[index].pop_back();
          break;
        }
      }

      if (changed == true) {
        continue;
      } // found another non-false literal to watch; do nothing

      if (value_of(other_watch) == FALSE) {
        conflict_clause = &clause;
        if (verbose) {
          std::cout << "conflict! conflict clause: [";
          for (int literal : conflict_clause->literals) {
            std::cout << literal << ", ";
          }
          std::cout << "]" << std::endl;
        }
        return false; // all literals are false, conflict found; return false
      } else {
        trail.push_back(other_watch); // all literals but one are false;
                                      // propagate the new unit clause
        assignments[std::abs(other_watch)] =
            other_watch > 0 ? TRUE : FALSE; // a new unit is being propagated,
                                            // so we need to assign it
        if (verbose)
          std::cout << "assigning " << std::abs(other_watch) << " to "
                    << (other_watch > 0 ? "TRUE" : "FALSE") << std::endl;
        last_assignments[std::abs(other_watch)] =
            other_watch > 0 ? TRUE : FALSE;
        decision_levels[std::abs(other_watch)] = trail_decisions.size() - 1;
        reasons[std::abs(other_watch)] = &clause;
        assigned_vars++;
        i++;
      }
    }
    trail_head++;
  }
  return true;
}

void decide() { // decide the value of one variable, adding it to the trail
  int highest_activity = 0;
  int var;
  for (int i = 1; i < activity.size(); i++) {
    if (assignments[i] !=
        UNASSIGNED) { // if a variable has already been assigned,
      continue;       // we cannot "decide" its value
    }

    if (activity[i] > highest_activity) {
      highest_activity = activity[i];
      var = i;
    }
  }

  trail_decisions.push_back(trail.size());
  int literal =
      last_assignments[var] == TRUE
          ? var
          : -var; // default to false if the variable hasnt been assigned yet
  trail.push_back(literal);
  assignments[var] = last_assignments[var];
  decision_levels[var] = trail_decisions.size() - 1;
  assigned_vars++;

  if (verbose)
    std::cout << "deciding " << literal << "..." << std::endl;
}

std::vector<int> analyse() { // analyse the conflict and add a learned clause
                             // that "explains" the conflict
  int decision_level = trail_decisions.size() - 1;
  int current_level_count =
      0; // number of variables in the learned clause that are in the current
         // decision level. once this hits 1, we have found the first UIP, so we
         // stop

  conflict_clause->activity += clause_activity_inc;

  std::vector<int> learned_clause = conflict_clause->literals;
  std::vector<bool> seen;
  seen.resize(2 * num_vars);
  std::fill(seen.begin(), seen.end(), false);

  std::vector<int> new_clause;
  new_clause.reserve(learned_clause.size());

  for (int i = 0; i < learned_clause.size(); i++) {
    if (seen[get_literal_index(learned_clause[i])] == false) {
      seen[get_literal_index(learned_clause[i])] = true;
      new_clause.push_back(learned_clause[i]);
      if (decision_levels[std::abs(learned_clause[i])] == decision_level)
        current_level_count++;
    }
  }

  learned_clause.swap(new_clause);

  for (int i = trail.size() - 1; i >= 0;
       i--) { // loop backwards through the trail, performing resolution on the
              // learned clause on each iteration. essentially, we're replacing
              // each instance of the literal we find in the trail with the
              // (unseen) literals in its reason clause
    if (current_level_count == 1) {
      break;
    }
    int index =
        std::find(learned_clause.begin(), learned_clause.end(), -trail[i]) -
        learned_clause.begin();
    if (index !=
        learned_clause
            .size()) { // std::find returns vector.size() if item not found

      Clause *reason_clause_ptr = reasons[std::abs(trail[i])];
      reason_clause_ptr->activity += clause_activity_inc;
      std::vector<int> reason_clause = reason_clause_ptr->literals;
      if (reason_clause.empty()) // decision literals have no reason clause, so
                                 // we can skip them
        continue;
      for (int literal : reason_clause) {
        if (seen[get_literal_index(literal)] == false && literal != trail[i]) {
          seen[get_literal_index(literal)] = true;
          learned_clause.push_back(literal);
          if (decision_levels[std::abs(literal)] == decision_level) {
            current_level_count++;
          }
        }
      }

      if (decision_levels[std::abs(learned_clause[index])] == decision_level) {
        current_level_count--;
      }
      learned_clause.erase(learned_clause.begin() + index);
    }
  }

  for (int literal : learned_clause) {
    activity[std::abs(literal)] += activity_inc;
  }

  for (int i = 0; i < activity.size(); i++) {
    activity[i] *= activity_decay;
  }

  for (Clause *ptr : learned_clauses) {
    ptr->activity *= clause_activity_decay;
  }

  return learned_clause;
}

void reduce() { // remove low activity learned clauses
  std::sort(learned_clauses.begin(), learned_clauses.end(),
            [](Clause *ptr1, Clause *ptr2) {
              return (ptr1->activity < ptr2->activity);
            }); // sort clauses by activity

  std::vector<Clause *> clauses_to_remove; // vector containing clause pointers
                                           // so the memory can be freed later

  for (int i = 0; i < learned_clauses.size() / 2;
       i++) { // remove half of the learned clauses with the lowest activity
              // values
    if (reasons[std::abs(learned_clauses[i]->literals[0])] !=
        learned_clauses[i]) { // only remove a clause if it is not currently
                              // implying the value of a literal
      learned_clauses[i]->toRemove = true;
      clauses_to_remove.push_back(learned_clauses[i]);
    }
  }

  int old_size = learned_clauses.size();

  for (Clause *c :
       learned_clauses) { // remove learned clauses marked with toRemove in the
                          // previous loop from the watcher list
    if (c->toRemove) {
      for (int index : {c->watch1, c->watch2}) {
        int lit = get_literal_index(c->literals[index]);
        watchers[lit].erase(
            std::remove(watchers[lit].begin(), watchers[lit].end(), c),
            watchers[lit].end());
      }
    }
  }

  // remove clauses marked with toRemove from the learned_clauses and clauses
  // lists

  learned_clauses.erase(std::remove_if(learned_clauses.begin(),
                                       learned_clauses.end(),
                                       [](Clause *c) { return c->toRemove; }),
                        learned_clauses.end());

  clauses.erase(std::remove_if(clauses.begin(), clauses.end(),
                               [](Clause *c) {
                                 bool remove = c->toRemove;
                                 return remove;
                               }),
                clauses.end());

  int new_size = learned_clauses.size();

  for (Clause *ptr : clauses_to_remove) { // free memory of removed clauses
    delete ptr;
  }

  if (verbose)
    std::cout << "removed " << old_size - new_size << " clauses" << std::endl;
}

void restart() {
  if (verbose)
    std::cout << "reached " << num_conflicts << " conflicts! restarting..."
              << std::endl;

  for (int i = trail.size() - 1; i >= 0; i--) { // unassign every variable
    int literal = trail[i];
    int variable = std::abs(literal);
    assignments[variable] = UNASSIGNED;
    assigned_vars--;
    decision_levels[variable] = -1;
    reasons[variable] = nullptr;
    trail.pop_back();
  }

  max_conflicts *= 1.5; // geometric restart strategy - increase number of
                        // conflicts required for a restart with each restart
  if (verbose)
    std::cout << "increasing restart threshold to " << max_conflicts
              << std::endl;
}

void backjump(
    std::vector<int> learned_clause) { // after a conflict, jump back to the
                                       // decision that caused it

  int uip = 0; // after backjumping, the UIP (which is the
               // last element) will be propagated
  int uip_index = -1;
  int highest_decision_level = 0;
  for (int i = 0; i < learned_clause.size(); i++) {
    int literal = learned_clause[i];
    int level = decision_levels[std::abs(literal)];
    if (level != trail_decisions.size() - 1) {
      if (level > highest_decision_level) {
        highest_decision_level = level;
      }
    } else {
      uip = literal;
      uip_index = i;
    }
  }

  int index = highest_decision_level + 1;

  if (learned_clause.size() == 1)
    index = 1;

  if (verbose)
    std::cout << "backjumping to decision level " << index - 1 << "..."
              << std::endl;

  for (int i = trail.size() - 1; i >= trail_decisions[index]; i--) {
    int literal = trail[i];
    int variable = std::abs(literal);
    assignments[variable] = UNASSIGNED;
    assigned_vars--;
    decision_levels[variable] = -1;
    reasons[variable] = nullptr;
    trail.pop_back();
  }

  if (learned_clause.size() != 1) {
    int temp = learned_clause[0];
    learned_clause[0] = learned_clause[uip_index];
    learned_clause[uip_index] =
        temp; // swap UIP (asserting literal) into position 0 so later, we can
              // easily check if learned clause is "locked" (i.e. it is a reason
              // clause for a current assignment, and cannot be deleted)
    Clause *c = new Clause({learned_clause, 0, 1});
    clauses.push_back(c);
    watchers[get_literal_index(learned_clause[0])].push_back(c);
    watchers[get_literal_index(learned_clause[1])].push_back(c);
    learned_clauses.push_back(c);
    trail_decisions.resize(highest_decision_level + 1);
  } else {
    Clause *c = new Clause({learned_clause, 0, 0});
    clauses.push_back(c);
    watchers[get_literal_index(learned_clause[0])].push_back(c);
    learned_clauses.push_back(c);
    trail_decisions.resize(1);
  }
  trail.push_back(uip);
  trail_head = trail.size() - 1;
  reasons[std::abs(uip)] = clauses.back();
  decision_levels[std::abs(uip)] = highest_decision_level;
  Value uip_value = uip > 0 ? TRUE : FALSE;
  assignments[std::abs(uip)] = uip_value;
  last_assignments[std::abs(uip)] = uip_value;
  assigned_vars++;

  if (num_conflicts % reduction_threshold == 0) {
    reduce();
  }

  if (num_conflicts >= max_conflicts) {
    restart();
  }
}

void parse() { // parse the DIMACS CNF input
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
      std::vector<bool> seen;
      seen.resize(2 * num_vars);
      std::fill(seen.begin(), seen.end(), false);
      while (literal != "0") { // clauses are terminated with 0
        if (seen[get_literal_index(std::stoi(literal))] == false) {
          clause.push_back(std::stoi(literal));
          seen[get_literal_index(std::stoi(literal))] = true;
        }
        std::cin >> literal;
      }
      Clause *c = new Clause({clause, 0, 0});
      clauses.push_back(c);
    }
  }
}

bool initialise() {                 // initialise any important variables
  assignments.resize(num_vars + 1); // the assignment vector is 1-indexed
  std::fill(assignments.begin(), assignments.end(),
            UNASSIGNED); // all variables start unassigned

  last_assignments.resize(num_vars + 1);
  std::fill(last_assignments.begin(), last_assignments.end(),
            FALSE); // last assignment defaults to false (since if a variable
                    // hasn't been assigned before, we try assigning false to it
                    // first when deciding its value)

  decision_levels.resize(num_vars + 1);
  std::fill(decision_levels.begin(), decision_levels.end(), -1);

  reasons.resize(num_vars + 1);

  activity.resize(num_vars + 1);
  std::fill(activity.begin(), activity.end(), 1);

  watchers.resize(
      2 * num_vars); // the watchers array is indexed over each literal (i.e.
                     // positive and negative propositional variables)

  trail_decisions.push_back(
      0); // the root decision level begins at trail index 0

  for (int i = 0; i < clauses.size(); i++) {
    if (clauses[i]->literals.size() == 1) {
      int literal = clauses[i]->literals[0];
      Value lit_value = literal > 0 ? TRUE : FALSE;
      if (assignments[std::abs(literal)] == UNASSIGNED) {
        trail.push_back(literal); // unit clause, so add its literal to the
                                  // trail to be propagated
        assignments[std::abs(literal)] = literal > 0 ? TRUE : FALSE;
        assigned_vars++;
      } else if (lit_value != assignments[std::abs(literal)]) {
        return false;
      }
    } else {
      watchers[get_literal_index(clauses[i]->literals[0])].push_back(
          clauses[i]); // add the first two literals as watched literals to the
                       // watchers array and struct attributes
      watchers[get_literal_index(clauses[i]->literals[1])].push_back(
          clauses[i]);
      clauses[i]->watch1 = 0;
      clauses[i]->watch2 = 1;
    }
  }

  return true;
}

bool sat_loop() { // loop that continually propagates variables, analysing
                  // conflicts or deciding variables when appropriate
  while (true) {
    if (propagate()) { // propagate unit clauses. if propagate returns true, no
                       // conflict was found
      if (assigned_vars ==
          num_vars) { // if all variables have been assigned, satisfiable
        return true;
      } else {
        decide();
      }
    } else {
      num_conflicts++;
      if (trail_decisions.size() - 1 == 0) {
        return false; // conflict at root decision level means unsat
      }
      std::vector<int> learned_clause = analyse();
      backjump(learned_clause);
    }
  }
}

int main(int argc, char *argv[]) {
  for (int i = 0; i < argc; i++) {
    if (strcmp(argv[i], "-v") == 0) {
      verbose = true;
    }
  }
  parse();
  if (!initialise()) { // initialise can return false if it finds two unit
                       // clauses that contradict each other
    std::cout << "UNSATISFIABLE" << std::endl;
    return 0;
  }
  std::cout << (sat_loop() ? "SATISFIABLE" : "UNSATISFIABLE") << std::endl;
  return 0;
}
