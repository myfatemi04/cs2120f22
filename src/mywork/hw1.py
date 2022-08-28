# Name: Michael Fatemi
# Email: gsk6me@virginia.edu
# Date: August 28, 2022

from z3 import *

def solve_with_integers():
    # Position of queen on each row
    nums = Ints(' '.join(f'q[{i}]' for i in range(1, 6)))

    solver = Solver()
    # Make sure queens are on different columns
    solver.add(Distinct(nums))
    # Make sure diagonals are all clear
    solver.add(Distinct([nums[i] - i for i in range(5)]))
    solver.add(Distinct([i - nums[i] for i in range(5)]))
    # Make sure everything is in bounds
    solver.add(*[And(0 < nums[i], nums[i] <= 5) for i in range(5)])

    solver.check()

    model = solver.model()

    print("Raw numeric model:")
    print(model)
    print()

    print("Chessboard model:")
    for i in range(5):
        print(' '.join('Q' if model[nums[i]] == j else '*' for j in range(1, 6)))

def solve_with_booleans():
    board = Bools(' '.join(
        f"row_{i}_col_{j}" for i in range(1, 6) for j in range(1, 6)
    ))
    
    def at_most_one(literals):
        from itertools import combinations
        
        return And(*[
            Or(Not(a), Not(b))
            for (a, b) in combinations(literals, 2)
        ])
        
    row_constraints = [
        at_most_one(board[i:i + 5])
        for i in range(0, 25, 5)
    ] + [
        # At least one queen per row
        Or(*board[i:i + 5])
        for i in range(0, 25, 5)
    ]
    
    col_constraints = [
        at_most_one(board[i::5])
        for i in range(5)
    ]
    
    diagonal_constraints_a = [
        at_most_one(board[::6])
        for i in range(5)
    ]
    
    diagonal_constraints_b = [
        at_most_one(board[4::4])
        for i in range(5)
    ]
    
    solver = Solver()
    solver.add(*col_constraints)
    solver.add(*row_constraints)
    solver.add(*diagonal_constraints_a)
    solver.add(*diagonal_constraints_b)
    solver.check()
    model = solver.model()
    
    i = 0
    for row in range(5):
        row_str = ''
        for col in range(5):
            row_str += 'Q' if model[board[i]] else '*'
            i += 1
            
        print(row_str)
    
solve_with_booleans()
