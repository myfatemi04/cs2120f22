# Name: Michael Fatemi
# Email: gsk6me@virginia.edu
# Date: August 28, 2022

from z3 import *

board = [
    [Int(f'board_{i}_{j}')
     for i in range(1, 10)]
    for j in range(1, 10)
]

solver = Solver()

# Enforce range of numbers
solver.add(*[
    And(board[j][i] >= 1, board[j][i] <= 9)
    for i in range(len(board))
    for j in range(len(board))
])

# Enforce rows
solver.add(*[
    Distinct(row) for row in board
])

# Enforce columns
solver.add(*[
    Distinct([board[row_i][col_i] for row_i in range(9)])
    for col_i in range(9)
])

# Enforce blocks
for start_row in [0, 3, 6]:
    for start_col in [0, 3, 6]:
        solver.add(Distinct([
            board[start_row + row][start_col + col]
            for row in range(3)
            for col in range(3)
        ]))

unsolved_board = ((0, 0, 0, 0, 9, 4, 0, 3, 0),
            (0, 0, 0, 5, 1, 0, 0, 0, 7),
            (0, 8, 9, 0, 0, 0, 0, 4, 0),
            (0, 0, 0, 0, 0, 0, 2, 0, 8),
            (0, 6, 0, 2, 0, 1, 0, 5, 0),
            (1, 0, 2, 0, 0, 0, 0, 0, 0),
            (0, 7, 0, 0, 0, 0, 5, 2, 0),
            (9, 0, 0, 0, 6, 5, 0, 0, 0),
            (0, 4, 0, 9, 7, 0, 0, 0, 0))

for row in range(len(unsolved_board)):
    for col in range(len(unsolved_board[row])):
        if unsolved_board[row][col] != 0:
            solver.add(board[row][col] == unsolved_board[row][col])

result = solver.check()
print(result)
model = solver.model()

solved_board = [[model[board[row][col]].as_long() for col in range(9)] for row in range(9)]

def print_board(board):
    i = 0
    for row in range(9):
        row_str = ''
        for col in range(9):
            row_str += (str(board[row][col]) if board[row][col] != 0 else ".") + (" " if ((col + 1) % 3) == 0 else "")
            i += 1

        print(' '.join(row_str))
        print()
        if (row + 1) % 3 == 0:
            print()
            

print_board(unsolved_board)
print_board(solved_board)
