import sys
from threading import Event
from utils import SATSolverResult, load_formula, lit_to_dimacs


class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.num_vars = self.formula.num_vars
        num_lits = self.formula.num_lits

        # Присваивание: values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен).
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.values = {}
        for i in range(self.num_vars * 2 + 2):
            self.values[i] = 0

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail = []
        self.propagated = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control = []

        self.model = None

        self.preprocess()

    def preprocess(self):
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        
        self.propagated = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control = []

        self.model = None

        self.preprocess_2()

    def preprocess_2(self):
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        self.clauses = set()
        self.units = set()
        self.has_empty_clause = False
        for clause in self.formula.clauses:
            lits = set(clause)
            if not lits:
                self.has_empty_clause = True
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif len(lits) == 1:
                self.units.add(lits.pop())
            else:
                self.clauses.add(tuple(lits))

    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int):
        """Сделать ℓ истинным на текущем уровне."""
        self.values[lit] = 1
        self.values[lit ^ 1] = -1
        self.trail.append(lit)
        for c in self.occurrences[lit]:
            self.true_literals[c] += 1
            self.free_literals[c] -= 1
        for c in self.occurrences[lit ^ 1]:
            self.free_literals[c] -= 1

    def decide(self, lit: int):
        """Открыть новый уровень решения и сделать ℓ истинным."""
        self.control.append(len(self.trail))
        self.assign(lit)

    def decision(self, level: int) -> int:
        """Литерал-решение уровня level (1 ≤ level ≤ self.level())."""
        return self.trail[self.control[level - 1]]

    def backtrack(self, level: int):
        """Отменить все присваивания уровней > level."""
        if level >= len(self.control):
            return
        values, trail = self.values, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0
            for c in self.occurrences[lit]:
                self.true_literals[c] -= 1
                self.free_literals[c] += 1
            for c in self.occurrences[lit ^ 1]:
                self.free_literals[c] += 1
        lit = trail[start]
        del trail[start:]
        del self.control[level:]
        self.propagated = start
        return lit

    def save_model(self):
        values = self.values
        self.model = [lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
                      for v in range(1, self.num_vars + 1)]

    def build_watches(self):
        self.occurrences = [[] for _ in range(self.formula.num_lits)]
        self.true_literals = {}
        self.free_literals = {}
        num_lits = self.formula.num_lits
        self.binary = [[] for _ in range(num_lits)]
        self.watches = [[] for _ in range(num_lits)]
        for c in self.clauses:
            if len(c) == 2:
                self.binary[c[0]].append(c[1])
                self.binary[c[1]].append(c[0])
            else:
                self.watches[c[0]].append([c[1], c])
                self.watches[c[1]].append([c[0], c])
            for lit in c:
                self.occurrences[lit].append(c)
                self.free_literals[c] = len(c)
                self.true_literals[c] = 0
        self.sorted_occ = sorted([(i, len(self.occurrences[i])) for i in range(len(self.occurrences))], reverse=True, key=lambda x: x[1])

    def propagate(self) -> bool:
        val = False
        while self.propagated < len(self.trail) and not val:
            lit = self.trail[self.propagated]
            self.propagated += 1
            for c in self.occurrences[lit ^ 1]:
                if self.free_literals[c] == 0 and self.true_literals[c] == 0:
                    val = True
                elif self.free_literals[c] == 1 and self.true_literals[c] == 0:
                    for lit in c:
                        if self.values[lit] == 0:
                            self.assign(lit)
        return val


    def choose_literal(self):
        for lit,occ in self.sorted_occ:
            if self.values[lit] == 0:
                return lit
        return None


    def solve(self) -> SATSolverResult:
        if self.sigkill.is_set(): 
            return SATSolverResult.UNKNOWN
        if self.has_empty_clause:
            return SATSolverResult.UNSAT
        if len(self.clauses) == 0 and len(self.units) == 0:
            return SATSolverResult.SAT
        self.build_watches()
        if len(self.units) > 0:
            for u in self.units:
                if self.values[u] == 0:
                    self.assign(u)
                elif self.values[u] == -1:
                    return SATSolverResult.UNSAT
        lit = self.choose_literal()
        while True:
            if self.sigkill.is_set():
                return SATSolverResult.UNKNOWN
            if self.propagate():
                if self.level() > 0:
                    lit = self.backtrack(self.level() - 1)
                    self.assign(lit ^ 1)
                    continue
                else:
                    return SATSolverResult.UNSAT
            lit = self.choose_literal()
            if lit is not None:
                self.decide(lit)
            else:
                break
        
        return SATSolverResult.SAT


if __name__ == "__main__":
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
