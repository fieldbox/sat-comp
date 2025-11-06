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

#include <iostream>
#include <string>
#include <vector>

int main(void) {
  int num_vars, num_clauses;
  std::vector<std::vector<int>> clauses;

  std::string literal;

  while (std::cin >> literal) {
    if (literal == "c") {
      std::getline(std::cin, literal);
    } else if (literal == "p") {
      std::string string_num_vars, string_num_clauses;

      std::cin >> literal >> string_num_vars >> string_num_clauses;

      num_vars = std::stoi(string_num_vars);
      num_clauses = std::stoi(string_num_clauses);
    } else {
      std::vector<int> clause;
      while (literal != "0") {
        clause.push_back(std::stoi(literal));
        std::cin >> literal;
      }
      clauses.push_back(clause);
    }
  }
  return 0;
}
