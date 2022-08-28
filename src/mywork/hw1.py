# Name: Michael Fatemi
# Email: gsk6me@virginia.edu
# Date: August 28, 2022

from z3 import *

def solve_with_integers(board_size=5):
    # Position of queen on each row
    nums = Ints(' '.join(f'q[{i}]' for i in range(1, board_size + 1)))

    solver = Solver()
    # Make sure queens are on different columns
    solver.add(Distinct(nums))
    # Make sure diagonals are all clear
    solver.add(Distinct([nums[i] - i for i in range(board_size)]))
    solver.add(Distinct([i - nums[i] for i in range(board_size)]))
    # Make sure everything is in bounds
    solver.add(*[And(0 < nums[i], nums[i] <= board_size) for i in range(board_size)])

    solver.check()

    model = solver.model()

    print("Raw numeric model:")
    print(model)
    print()

    print("Chessboard model:")
    for i in range(board_size):
        print(' '.join('Q' if model[nums[i]] == j else '*' for j in range(1, board_size + 1)))

def solve_with_booleans(board_size=5):
    board = [
        [Bool(f'board_{row}_{col}')
         for col in range(board_size)]
        for row in range(board_size)
    ]
    
    def at_most_one(literals):
        from itertools import combinations
        
        return And(*[
            Or(Not(a), Not(b))
            for (a, b) in combinations(literals, 2)
        ])
        
    row_constraints = [
        at_most_one(board[row])
        for row in range(board_size)
    ] + [
        # At least one queen per row
        Or(*board[row])
        for row in range(board_size)
    ]
    
    col_constraints = [
        at_most_one([board[row][col] for row in range(board_size)])
        for col in range(board_size)
    ]
    
    diagonal_constraints = []
    # down and to the right
    for i in range(board_size - 1):
        a = []
        b = []
        c = []
        d = []
        for j in range(board_size - i):
            # down and to the right: i is starting distance from left, j is distance from top
            a.append(board[j][i + j])
            # down and to the right: i is starting distance from top, j is distance from left
            b.append(board[i + j][j])
            # up and to the right: i is starting distance from left, j is distance from bottom
            c.append(board[board_size - 1 - j][i + j])
            # up and to the right: i is starting distance from bottom, j is distance from left
            d.append(board[board_size - 1 - (i + j)][j])
        
        diagonal_constraints.append(at_most_one(a))
        diagonal_constraints.append(at_most_one(b))
        diagonal_constraints.append(at_most_one(c))
        diagonal_constraints.append(at_most_one(d))
    
    solver = Solver()
    solver.add(*col_constraints)
    solver.add(*row_constraints)
    solver.add(*diagonal_constraints)
    print(solver.check())
    model = solver.model()
    
    for row in range(board_size):
        row_str = ''
        for col in range(board_size):
            row_str += 'Q' if model[board[row][col]] else '*'
            
        print(' '.join(row_str))

board_size = 5
print("#### Solving with Boolean method ####")
solve_with_booleans(board_size)
print()

print("#### Solving with Ints method ####")
solve_with_integers(board_size)
