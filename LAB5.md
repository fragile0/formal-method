# LAB5: EUF理论

### 前置知识

- **EUF = equalities(等式理论) + uninterpreted functions(抽象函数)** 
- 不可解释函数的唯一性质，两个函数相同当且仅输入输出相同。
- SMT问题即是判断SMT是否可满足的问题 
- SMT- 谓词逻辑可满足性 = SAT + Theory solvers

### Part A: Basic EUF theory

**类、常量、函数的定义**

```python
S = DeclareSort('S')	# 定义抽象类s
e = Const('e', S)		# 定义常量e
f = Function('f', S, S)		# 函数具有一个输入一个输出,类型均为S
g = Function('g', S, S, S)	# 函数具有两个输入一个输出，类型均为S
```

#### exercise 1 SMT问题实例

​	这一部分主要给出了几个用程序解决SMT问题的实例，只需要看看理解即可，不需要自己实现。

#### exercise 2  证明程序等效性

```python
S = DeclareSort('S')
in_0 = Const('in_0', S)
out_a_0, out_a_1, out_a_2, out_b = Consts('out_a_0, out_a_1, out_a_2, out_b', S)
f = Function('f', S, S, S)

s1 = out_a_0 == in_0
s2 = out_a_1 == f(out_a_0, in_0)
s3 = out_a_2 == f(out_a_1, in_0)

p1 = And(s1, s2, s3)

s4 = out_b == f(f(in_0, in_0), in_0)
p2 = s4

F = Implies(And(p1, p2), out_a_2 == out_b)
solve(F)
solve(Not(F))
```

这一部分可以参考exercise1的代码写，主要注意的是在这里面'='号相当于赋值，而'=='表示两个变量相等。最后如果solve(Not(F))得到无解证明两个程序是等效的，反之则是无效的。

## Part B,C: Translation validation

partB较为复杂，主要是实现一些编译优化的功能，涉及到很多递归和字符串处理，其实逻辑不难，但是细节很繁琐，C反而简单了很多，只需要调用上面写的接口函数即可。由于时间不足，B写了几个函数后实在不想继续写了，后面从github上copy来的答案，答案在文件夹中附有。

