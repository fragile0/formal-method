# LAB6 线性算法

- linear arithmetic 线性算法
- linear programming 线性规划

作业共分为三个部分

- 第一部分介绍了LA/LP理论的基本背景知识
- 第二部分介绍了LA/LP理论的应用，解决了一些NPC问题
- 第三部分包括解决一些复杂的问题

## PartA 基础线性算法理论

#### exercise1 

```python
x, y = Reals('x y')
solver = Solver()
solver.add(x + y == 0.8, x - y == 0.2)
res = solver.check()
print("result for problem 1:")
if res == sat:
    model = solver.model()
    print(model)
else:
    print(res)
```

运行上面这段代码，得到的结果如下：

```python
result for problem 1:
[y = 3/10, x = 1/2]
```

#### exercise2

```python
x, y = Reals('x y')
solver = Solver()
solver.add(x + y == 0.8, x + y == 0.2)
res = solver.check()
print("result for problem 2:")
if res == sat:
    model = solver.model()
    print(model)
else:
    print(res)
```

 运行上面这段代码，得到的结果如下：

```python
result for problem 2:
unsat
```

#### exercise3

```python
x, y = Ints('x y')
solver = Solver()
solver.add(x + y == 8, x - y == 2)
res = solver.check()
print("result for problem 3:")
if res == sat:
    model = solver.model()
    print(model)
else:
    print(res)
```

运行上面这段代码，得到的结果如下：

```python
result for problem 3:
[x = 5, y = 3]
```

#### exercise4

```python
x, y = Reals('x, y')
cons = [x + y == 8, x - y == 1]
res, model = check_cons(cons)
print_model(res, model)

x, y = Ints('x, y')
cons = [x + y == 8, x - y == 1]
res, model = check_cons(cons)
print_model(res, model)
```

运行上面这段代码，得到的结果如下：

```python
[y = 7/2, x, = 9/2]
unsat
```

#### exercise5（0-1 Integer Linear Arithmetic)

​	这类问题主要是判断每个list中是否至少存在一个0

```
x1...xn中所有数字都属于0,1,并且和为1,因此至少有一个xi的值为1
由于所有xi*ei和为0,此时用反证法。如果所有ei都为1，此时所有xi和ei和必然不为0.
因此list中至少存在一个0
```

#### exercise6

​	添加一个限制，循环即可。

```python
cons_exp = []
tmp_sum = 0
for i in range(len(vars)):
    tmp_sum = tmp_sum + vars[i] * l[i]
cons_exp.append(tmp_sum == 0)
```

#### challenge  

​	判断一个数组中有几个0，这里的思路很简单，循环限制条件sum(vars)==t，如果能够满足，证明至少存在数组中t个0，否则证明数组中不存在t个0，因此返回t - 1即可。

```python
l1 = [1, 2, 4, 5]  # 0
l2 = [3, 0, 8, 2]  # 1
l3 = [4, 0, 3, 0]  # 2

def check_zero_la(l):
    vars = [Int('x_%d' % i) for i in range(len(l))]
    cons_0_or_1 = []

    for i in range(len(vars)):
        cons_0_or_1.append(Or(vars[i] == 0, vars[i] == 1))

    cons_exp = []
    tmp_sum = 0
    for i in range(len(vars)):
        tmp_sum = tmp_sum + vars[i] * l[i]
    cons_exp.append(tmp_sum == 0)
    ans = 0
    while 1:
        cons_sum = [sum(vars) == ans]
        res, model = check_cons(cons_0_or_1 + cons_sum + cons_exp)
        if res != sat:
            return ans - 1
        ans = ans + 1
    return -1

print(check_zero_la(l1))
print(check_zero_la(l2))
print(check_zero_la(l3))
```

#### exercise7

```python
x, y = Reals('x, y')
res, model = check_cons([x * x + y * y < 0])
if res == sat:
    print(model)
else:
    print(res)
```

最后输出unsat结果就是正确的。

#### exercise8

```python
x, p, q = Ints('x p q')
cons_1 = [x * q == p]
cons_2 = [q != 0]
cons_3 = [x * x == 2]
res, model = check_cons(cons_1 + cons_2 + cons_3)
print_model(res, model)
```

最后输出unsat结果就是正确的。

## PartB LA/LP理论应用

#### exercise9

```python
s = 0
for i in range(len(target_set)):
	s = s + target_set[i] * flags[i]
solver.add(s == 0)
```

加上一个新的限制即可，程序结果如下：

```python
time used in LA: 0.047994s
(True, [-3, -2, 5])
```

#### exercise10

把规模调到20，运行结果如下：

```python
time used in DP: 0.339669s
time used in LA: 0.089237s
(True, [1, -1])
time used in LA optimized: 0.017830s
(True, [1, -1])
```

DP速度明显比不上LA和LA优化，如果把规模继续加大，甚至可能出现递归栈溢出的情况。让人疑惑的一点是，这个所谓的dp没有用到任何记忆化的东西，仅仅是简单的搜索罢了，实际上是指数级别的时间复杂度。

#### challenge

```python
def subset_sum_dp1(target_set):
   def subset_sum_dp1_do(the_set):
        print(the_set)
        s = set()
        for i in range(len(the_set)):
            if len(s) == 0:
                s.add(the_set[i])
            else:
                tmp = set()
                for item in s:
                    tmp.add(item + the_set[i])
                s = s.union(tmp)
      #      print(s)
            if 0 in s:
                return True
        return False
   start = time.time()
   result = subset_sum_dp1_do(target_set)
   print(f"time used in DP1: {(time.time() - start):.6f}s")
   return result
```

实现一个非递归dp，解决这个问题，速度明显比其他几种方法要快，最终实现的是用set存储当前得到的数据，这个方法的时间复杂度取决于所有数据的和的最大值和最小值，而不取决于数据规模。

#### exercise12

```python
def n_queen_la(board_size: int, verbose: bool = False) -> int:
    solver = Solver()
    n = board_size

    board = [[Int(f"x_{row}_{col}") for col in range(n)] for row in range(n)]

    # only be 0 or 1 in board
    for row in board:
        for pos in row:
            solver.add(Or(pos == 0, pos == 1))
    #   each row has just 1 queen,
    for i in range(n):
        s = []
        for j in range(n):
            s.append(board[i][j])
        solver.add(sum(s) == 1)
    #   each column has just 1 queen,
    for i in range(n):
        s = []
        for j in range(n):
            s.append(board[j][i])
        solver.add(sum(s) == 1)
	# 	each diag has no more than 1 queen
    for d in range(1 - n, n):
        s = []
        for i in range(0, n):
            j = i - d
            if j >= 0 and j < n:
                s.append(board[i][j])
        solver.add(sum(s) <= 1)
	# each udiag has no more than 1 queen
    for d in range(0, 2 * n):
        s = []
        for i in range(0, n):
            j = d - i
            if j >= 0 and j < n:
                s.append(board[i][j])
        solver.add(sum(s) <= 1)
    # count the number of solutions
    solution_count = 0

    start = time.time()
    while solver.check() == sat:
        solution_count += 1
        model = solver.model()

        if verbose:
            # print the solution
            print([(row_index, col_index) for row_index, row in enumerate(board)
                   for col_index, flag in enumerate(row) if model[flag] == 1])

        # generate constraints from solution
        solution_cons = [(flag == 1) for row in board for flag in row if model[flag] == 1]

        # add solution to the solver to get new solution
        solver.add(Not(And(solution_cons)))
    print(f"n_queen_la solve {board_size}-queens by {(time.time() - start):.6f}s")
    # print(solution_count)
    return solution_count
```

​	依次添加四个限制，最后结果得到solution_count=92即可，用时8s

#### exercise12,13

运行结果

```

n_queen_la solve 8-queens by 8.908559s
92
n_queen_bt solve 8-queens by 0.051301s
92
n_queen_la_opt solve 8-queens by 1.289348s
92

速度 bt > la_opt > la
```

 #### exercise14

```python
def lp_exercise():
    opt = Optimize()
    x, y, z = Reals("x y z")

    opt_min = Optimize()
    cons = [x - y >= 2.1, x + z <= 5.5, y - z <= 1.1]
    opt_min.add(cons)

    # minimize() will get minimal value of the target function
    opt_min.maximize(x + y + z)

    if opt_min.check() == sat:
        print(opt_min.model())
```

#### exercise15,16,17

```python
def zero_one_knapsack_lp(weights, values, cap, verbose=False):
    # create a new solver, but
    solver = Optimize()

    # the decision variables
    flags = [Int(f"x_{i}") for i in range(len(weights))]
    # print(flags)

    # flags are 0-1
    for flag in flags:
        solver.add(Or(flag == 0, flag == 1))

    con = []
    for i in range(len(flags)):
        con.append(weights[i] * flags[i])
    solver.add(sum(con) <= cap)

    res = []
    for i in range(len(flags)):
        res.append(values[i] * flags[i])
    solver.maximize(sum(res))

    start = time.time()
    result = solver.check()
    print(f"zero_one_knapsack_lp solve {len(weights)} items by time {(time.time() - start):.6f}s")

    if result == sat:
        model = solver.model()

        # print the chosen items
        if verbose:
            print("\n".join([f"Index: {index}, Weight: {weights[index]}, Value: {values[index]}"
                             for index, flag in enumerate(flags) if model[flag] == 1]))

        return True, sum([values[index] for index, flag in enumerate(flags) if model[flag] == 1])

    return False, result

```



```python
def complete_knapsack_lp(weights, values, cap, verbose=False):
    solver = Optimize()
    flags = [Int(f"x_{i}") for i in range(len(weights))]
    for flag in flags:
        solver.add(flag >= 0)
    con = []
    for i in range(len(flags)):
        con.append(weights[i] * flags[i])
    solver.add(sum(con) <= cap)

    res = []
    for i in range(len(flags)):
        res.append(values[i] * flags[i])
    solver.maximize(sum(res))

    start = time.time()
    result = solver.check()
    print(f"complete_lp solve {len(weights)} items by time {(time.time() - start):.6f}s")

    if result == sat:
        model = solver.model()
        max_vals = 0
        for index, flag in enumerate(flags):
            flag = model[flag].as_long()
            if flag > 0:
                print("Index: " + str(index) + ", Weight: " + str(weights[index]) + ", Value: " + str(
                    values[index]) + ", Amount: " + str(flag))
                max_vals += values[index] * flag

        return max_vals

    return False, result
```

分别用lp方法解决01背包和完全背包问题，exercise17用lp和dp方法对比。从原理上即可知道，如果背包容量足够大的话，使用dp一方面可能出现栈空间溢出，可能程序无法正确执行。但如果背包容量较小，dp速度远远快于lp方法。

#### exercise18, 19

```python
exps = [0]
for i in range(len(xs)):
    exps.append((ys[i] - k * xs[i] - b) * (ys[i] - k * xs[i] - b))
```

最终得到的答案如下：

```python
the linear function is:
 y = 20*x - 4
the linear function is:
 y = 2.0*x - 1.0
```

机器学习方法和线性回归得到的结果有显著的不同，但从结果来看，线性回归比机器学习的结果要准确很多。





















