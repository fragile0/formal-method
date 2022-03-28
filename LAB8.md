## LAB8 符号执行

​	这里主要讨论三个部分，操作语义、符号执行、并行执行。

### Part A Concrete execution

```python
    B ::= + | - | * | / | == | != | > | < | >= | <=
    E ::= n | x | E B E
    S ::= pass
        | x = E
        | seq(S, S)
        | f(E1, ..., En)
        | if(E, S, S)
        | while(E, S)
    F ::= f((x1, ..., xn), S, E)
```

需要写一个解释器直接执行MiniPy的源代码，为了实现这一目标，你首先需要建立数据结构来表示MiniPy的语法，它也被叫做AST。

#### exercise 1

阅读mini_py.py的代码，给定的代码修改了一部分MiniPy的语法，最大的改变是移除了函数调用声明F。这里需要我们做的就是实现

```python
class Function:
    def __init__(self, name: str, args: List[str], stmts: List[Stmt], ret: Expr):
        self.name = name
        self.args = args
        self.stmts = stmts
        self.ret = ret

    def __str__(self):
        arg_str = ",".join(self.args)
        for stmt in self.stmts:
            stmt.level += 1

        stmts_str = "".join([str(stmt) for stmt in self.stmts])
        
        # 函数结构: def + (参数) + “\n” + 函数体 + “\n” + return + 返回值
        return (f"def {self.name}({arg_str}):\n"
                f"{stmts_str}\n"
                f"\treturn {self.ret}")
```

这里不难，所有的函数组成部分都已经写好，只需要拼接即可，输出结果如下：

```python
def printer_test(n):
	s = 0
	i = 0
	while i <= (n - 3):
		s = s + i
		i = i + 1
		if s > i :
			b = s - 1
	if s > i :
		s = i - 1
	else:
		s = i + 1

	return s
```

#### exercise 2,3

阅读concrete.py文件，确保能够了解这个数据结构。并依据big-step规则完成interpret_stm()函数，通过测试样例。

```python
  ρ⊢E⟹n
    -------------------------- (E-Assign)
          ρ⊢x=E⟹ρ[x⊢n]

        ρ⊢E⟹1    ρ⊢S1⟹ρ1                  ρ⊢E⟹0   ρ⊢S2⟹ρ2
    -------------------------- (E-If1) ------------------------- (E-If2)
         ρ⊢if(E;S1;S2)⟹ρ1                  ρ⊢if(E;S1;S2)⟹ρ2

            ρ⊢E⟹0                         ρ⊢E⟹1  ρ⊢S⟹ρ′ ρ′⊢while(E;S)
    -------------------------- (E-While1) ------------------------------------ (E-While2)
          ρ⊢while(E;S)⟹ρ                         ρ⊢while(E;S)⟹ρ′′
```

需要分别实现赋值、判断、循环这三个条件, 实现结果如下：

```python
 if isinstance(stmt, StmtAssign):
        memory.concrete_memory[stmt.var] = interpret_expr(memory, stmt.expr)
    if isinstance(stmt, StmtIf):
        if interpret_expr(memory, stmt.expr):
            next_stmts = stmt.then_stmts
        else:
            next_stmts = stmt.else_stmts
        interpret_stmts(memory, next_stmts)
    if isinstance(stmt, StmtWhile):
        while interpret_expr(memory, stmt.expr):
            for s in stmt.stmts:
                interpret_stm(memory, s)

    return memory
```



### Part B Symbolic execution

#### exercise 4

这里实现了一个多线程的并行执行，执行得到的结果如下：

```python
Timer(pid=55700, time='2022-01-08 16:27:05.395985')
Timer(pid=55700, time='2022-01-08 16:27:06.402993')
Timer(pid=49092, time='2022-01-08 16:27:06.418285')
Timer(pid=55700, time='2022-01-08 16:27:07.404493')
Timer(pid=55700, time='2022-01-08 16:27:08.414717')
Timer(pid=49092, time='2022-01-08 16:27:08.429716')
Timer(pid=55700, time='2022-01-08 16:27:09.420771')
Timer(pid=49092, time='2022-01-08 16:27:10.441119')
Timer(pid=49092, time='2022-01-08 16:27:12.450411')
Timer(pid=49092, time='2022-01-08 16:27:14.455036')
```

一个线程每2s计时一次，而另一个线程每过1s计时一次。

#### exercise 5,6,7

这三个练习都是关于符号执行。

**exercise5,6实现的是符号计算的功能**，通过不断地将符号递归替换成表达式得到最终的最简表达式。

```python
def symbolic_expr(memory, expr):
    if isinstance(expr, ExprNum):
        return expr
    if isinstance(expr, ExprVar):
        expr = memory.symbolic_memory[expr.var]
        if isinstance(expr, ExprNum):
            return expr
        elif isinstance(expr, ExprVar):
            return memory.symbolic_memory[expr.var]
        elif isinstance(expr, ExprBop):
            if isinstance(expr.left, ExprVar):
                left = memory.symbolic_memory[expr.left.var]
            else:
                left = expr.left
            if isinstance(expr.right, ExprVar):
                right = memory.symbolic_memory[expr.right.var]
            else:
                right = expr.right
            return ExprBop(left, right, expr.bop)
    if isinstance(expr, ExprBop):
        right = symbolic_expr(memory, expr.right)
        left = symbolic_expr(memory, expr.left)
        return ExprBop(left, right, expr.bop)
```

**exercise7实现的是将符号计算的限制转化为z3表达式**，最终将它加入cons计算出该表达式是否可满足。

```python
def expr_2_z3(expr):
    if isinstance(expr, ExprNum):
        return expr.num
    if isinstance(expr, ExprVar):
        return Int(expr.var)
    if isinstance(expr, ExprBop):
        if expr.bop is Bop.ADD:
            return expr_2_z3(expr.left) + expr_2_z3(expr.right)
        if expr.bop is Bop.MIN:
            return expr_2_z3(expr.left) - expr_2_z3(expr.right)
        if expr.bop is Bop.MUL:
            return expr_2_z3(expr.left) * expr_2_z3(expr.right)
        if expr.bop is Bop.DIV:
            return expr_2_z3(expr.left) / expr_2_z3(expr.right)
        if expr.bop is Bop.EQ:
            return expr_2_z3(expr.left) == expr_2_z3(expr.right)
        if expr.bop is Bop.NE:
            return expr_2_z3(expr.left) != expr_2_z3(expr.right)
        if expr.bop is Bop.GT:
            return expr_2_z3(expr.left) > expr_2_z3(expr.right)
        if expr.bop is Bop.GE:
            return expr_2_z3(expr.left) >= expr_2_z3(expr.right)
        if expr.bop is Bop.LT:
            return expr_2_z3(expr.left) < expr_2_z3(expr.right)
        if expr.bop is Bop.LE:
            return expr_2_z3(expr.left) <= expr_2_z3(expr.right)
    return []
```

### Part C Concolic execution

concolic实行主要有以下几大优点：

- 渐近执行避免了路径爆炸的问题； 
- 无需限定循环
- 无需为API调用建立符号模型
- 面对困难的约束时更加灵活。 

#### exercise 8,9

execise8, 9主要实现的解析if、while和赋值语句，并修改内存内容,实现结果如下：

```python
def concolic_stmt(memory, stmt):
    if isinstance(stmt, StmtAssign):
        memory.symbolic_memory[stmt.var] = symbolic_expr(memory, stmt.expr)
        memory.concrete_memory[stmt.var] = interpret_expr(memory, stmt.expr)

    elif isinstance(stmt, StmtIf):
        if interpret_expr(memory, stmt.expr):
            memory.path_condition.append(symbolic_expr(memory, stmt.expr))
            return concolic_stmts(memory, stmt.then_stmts)
        memory.path_condition.append(symbolic_expr(memory, neg_exp(stmt.expr)))
        return concolic_stmts(memory, stmt.else_stmts)

    elif isinstance(stmt, StmtWhile):
        while interpret_expr(memory, stmt.expr):
            if isinstance(stmt.expr, ExprBop):
                memory.path_condition.append(get_the_whole_expr(memory, stmt.expr))
            for s in stmt.stmts:
                concolic_stmt(memory, s)
        if isinstance(stmt.expr, ExprBop):
            memory.path_condition.append(get_the_whole_expr(memory, stmt.expr))
    return memory
```

### Part D sql injection

