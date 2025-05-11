import random
import time
from typing import List, Tuple, Union, Callable
from multiprocessing import Process, Queue

Clause = List[int]
Formula = List[Clause]

def wrapper(func: Callable, args: tuple, q: Queue):
    try:
        start = time.time()
        result = func(*args)
        elapsed = time.time() - start
        q.put((result, round(elapsed, 4)))
    except Exception as e:
        q.put((f"Eroare: {e}", 0))

def run_with_timeout(func: Callable, args: tuple = (), timeout: int = 5) -> Tuple[str, float]:
    q = Queue()
    p = Process(target=wrapper, args=(func, args, q))
    p.start()
    p.join(timeout)
    if p.is_alive():
        p.terminate()
        return "Timeout", timeout
    else:
        return q.get()

# ------------------ CITIRE CNF ------------------
def load_dimacs_file(path: str) -> Formula:
    with open(path, 'r') as f:
        lines = f.readlines()
    formula = []
    for line in lines:
        if line.startswith(('c', 'p', '%', '0')) or line.strip() == "":
            continue
        try:
            clause = [int(x) for x in line.strip().split() if int(x) != 0]
            formula.append(clause)
        except ValueError:
            continue
    return formula

# ------------------ REZOLUTIE ------------------
def resolve(c1: Clause, c2: Clause) -> Union[Clause, None]:
    for lit in c1:
        if -lit in c2:
            new_clause = set(c1 + c2)
            new_clause.discard(lit)
            new_clause.discard(-lit)
            return list(new_clause)
    return None

def resolution_algorithm(formula: Formula) -> bool:
    clauses = list(formula)
    new = set()
    while True:
        n = len(clauses)
        for i in range(n):
            for j in range(i + 1, n):
                resolvent = resolve(clauses[i], clauses[j])
                if resolvent is not None:
                    if len(resolvent) == 0:
                        return False
                    new.add(tuple(sorted(resolvent)))
        new_clauses = [list(c) for c in new if list(c) not in clauses]
        if not new_clauses:
            return True
        clauses.extend(new_clauses)

# ------------------ DAVIS-PUTNAM ------------------
def dp_resolution(formula: Formula, variables: List[int]) -> bool:
    clauses = list(formula)
    for var in variables:
        pos = [c for c in clauses if var in c]
        neg = [c for c in clauses if -var in c]
        resolvents = []
        for p in pos:
            for n in neg:
                r = list(set(p + n))
                r = [l for l in r if l != var and l != -var]
                if not r:
                    return False
                resolvents.append(r)
        clauses = [c for c in clauses if var not in c and -var not in c]
        clauses.extend(resolvents)
    return True

# ------------------ DPLL ------------------
def unit_propagate(clauses: Formula, assignment: dict) -> Union[Tuple[Formula, dict], None]:
    changed = True
    while changed:
        changed = False
        unit_clauses = [c for c in clauses if len(c) == 1]
        for clause in unit_clauses:
            unit = clause[0]
            var = abs(unit)
            val = unit > 0
            if var in assignment:
                if assignment[var] != val:
                    return None
                continue
            assignment[var] = val
            new_clauses = []
            for c in clauses:
                if unit in c:
                    continue
                if -unit in c:
                    new_c = [l for l in c if l != -unit]
                    if not new_c:
                        return None
                    new_clauses.append(new_c)
                else:
                    new_clauses.append(c)
            clauses = new_clauses
            changed = True
            break
    return clauses, assignment

def dpll(clauses: Formula, assignment: dict = {}) -> Union[dict, None]:
    result = unit_propagate(clauses[:], assignment.copy())
    if result is None:
        return None
    clauses, assignment = result
    if not clauses:
        return assignment
    for clause in clauses:
        for literal in clause:
            var = abs(literal)
            if var not in assignment:
                for val in [True, False]:
                    new_assignment = assignment.copy()
                    new_assignment[var] = val
                    new_clauses = []
                    for c in clauses:
                        if (var if val else -var) in c:
                            continue
                        new_c = [l for l in c if l != (-var if val else var)]
                        if not new_c:
                            break
                        new_clauses.append(new_c)
                    else:
                        result = dpll(new_clauses, new_assignment)
                        if result is not None:
                            return result
                return None
    return assignment

# ------------------ WALKSAT ------------------
def evaluate_clause(clause: Clause, assignment: dict) -> bool:
    return any(
        (lit > 0 and assignment.get(abs(lit), False)) or
        (lit < 0 and not assignment.get(abs(lit), True))
        for lit in clause
    )

def num_satisfied(clauses: Formula, assignment: dict) -> int:
    return sum(evaluate_clause(c, assignment) for c in clauses)

def walksat(clauses: Formula, max_flips: int = 10000, prob_random: float = 0.5) -> Union[dict, None]:
    variables = list({abs(lit) for clause in clauses for lit in clause})
    assignment = {v: random.choice([True, False]) for v in variables}
    for _ in range(max_flips):
        unsat = [c for c in clauses if not evaluate_clause(c, assignment)]
        if not unsat:
            return assignment
        clause = random.choice(unsat)
        if random.random() < prob_random:
            var = abs(random.choice(clause))
        else:
            scores = {}
            for lit in clause:
                var = abs(lit)
                assignment[var] = not assignment[var]
                scores[var] = num_satisfied(clauses, assignment)
                assignment[var] = not assignment[var]
            var = max(scores, key=scores.get)
        assignment[var] = not assignment[var]
    return None

# ------------------ BENCHMARK ------------------
def benchmark_all_algorithms_with_timeout(formula: Formula, variables: List[int] = None, timeout: int = 5) -> None:
    print("=== Benchmark cu timeout ===")

    if variables is None:
        variables = list({abs(l) for clause in formula for l in clause})

    res, t1 = run_with_timeout(resolution_algorithm, (formula,), timeout)
    print(f"Rezoluție: {res} – {t1:.4f} secunde")

    dp, t2 = run_with_timeout(dp_resolution, (formula, variables), timeout)
    print(f"Davis–Putnam: {dp} – {t2:.4f} secunde")

    dpll_result, t3 = run_with_timeout(dpll, (formula,), timeout)
    print(f"DPLL: {'SAT' if isinstance(dpll_result, dict) else 'UNSAT' if dpll_result is None else dpll_result} – {t3:.4f} secunde")

    ws_result, t4 = run_with_timeout(walksat, (formula,), timeout)
    print(f"WalkSAT: {'SAT' if isinstance(ws_result, dict) else 'UNSAT' if ws_result is None else ws_result} – {t4:.4f} secunde")

# ------------------ MAIN ------------------
if __name__ == '__main__':
    formula = load_dimacs_file("benchmark-uri/uf20-01.cnf")
    benchmark_all_algorithms_with_timeout(formula, timeout=5)