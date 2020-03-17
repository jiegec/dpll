import sys
n = int(sys.argv[1])

clauses = []

# every row only one
for i in range(n):
    clause = []
    for j in range(n):
        clause.append(i * n + j+1)
    clauses.append(clause)
    for j in range(n):
        for k in range(j+1, n):
            clauses.append([-(i * n + j + 1), -(i * n + k + 1)])

# every column only one
for i in range(n):
    clause = []
    for j in range(n):
        clause.append(i + j * n + 1)
    clauses.append(clause)
    for j in range(n):
        for k in range(j+1, n):
            clauses.append([-(i + j * n + 1), -(i + k * n + 1)])

# diagonal
diags = []
for i in range(2*n-1):
    diags.append([])

for i in range(n):
    for j in range(n):
        diags[i+j].append(i*n+j+1)

for i in range(2 * n - 1):
    for j in range(len(diags[i])):
        for k in range(j+1, len(diags[i])):
            clauses.append([-diags[i][j], -diags[i][k]])

# the other way of digonal
diags = []
for i in range(2*n-1):
    diags.append([])

for i in range(n):
    for j in range(n):
        diags[(i-j+2*n-1) % (2*n-1)].append(i*n+j+1)

for i in range(2 * n - 1):
    for j in range(len(diags[i])):
        for k in range(j+1, len(diags[i])):
            clauses.append([-diags[i][j], -diags[i][k]])

print('c {} queens problem'.format(n))
print('p cnf {} {}'.format(n**2, len(clauses)))
for clause in clauses:
    print(' '.join([str(lit) for lit in clause]) + ' 0')