## LAB7 数据结构理论

### Part A bit vectors

#### exercise 1

运行如下代码，解释输出。

```python
x, y = BitVecs('x y', 2)
solve(x+y==9)
```

​	**得到的结果如下为，[y = 0, x = 1], 由于定义一个两位的位向量，而9明显超过了2bit的表示范围，所以有(x + y) % 4 == 9 % 4，即为(x + y) % 4 == 1, 因此z3得到结果x = 1, y = 0, 满足题意。**

#### exercise 2

lab2需要实现一个计数器，实现对于一个BitVecVal中变量1数量的统计。这里难点在于如何判断一个BitVecVal的值是否等于0，可以用Solver来解决这个问题，如果结果等于SAT，证明变量为0，否则不为0。具体代码如下：

```python
def count_one_in_bit_vector(x):
    tmp = x
    cnt = 0
    while 1:
        solver = Solver()
        solver.add(tmp != 0)
        res = solver.check()
        tmp = tmp & (tmp - 1)
        if res == sat:
            cnt = cnt + 1
        else:
            break
    return cnt
```

​	这里还有一个lowbit技巧，用过树状数组的同学应该都有所耳闻，x & (x - 1)每次将二进制最低位的1变为0，最后输出cnt即为1的个数。

#### exercise 3,4,5,6

这四个exercise是连在一起的，首先让我们实现一个有bug 的平均数函数，后用check_average(int_average_v1, True)和java函数实现对于定义函数的验证，最后得到的结果如下：

```python
FAILED! Found a bug with non-negative input in the function: int_average_v1
[y = 2140969103, x = 1902339953]
Exception in thread "main" java.lang.AssertionError: Generating a integer overflow bug!
	at com.assign.IntAverage.int_average(IntAverage.java:13)
	at com.assign.IntAverage.main(IntAverage.java:8)
```

显然，这几个函数都是由bug的，得到的结果也是如此。后来给出了第二个函数

```python
def int_average_v2(x, y):
	return x + (y-x)/2
```

这里虽然将+号写成了-号，但仍然存在相同的问题：如果y是一个很小的负数，而x是一个很大的正数，此时仍然会溢出。

#### exercise 7,8

考虑第二个函数int_averge_v3()，具体实现位逻辑右移

```python
def int_average_v3(x, y):
    return LShR((x+y), 1)

FAILED! Found a bug with negative input in the function: int_average_v3
[y = 2181038079, x = 2516582401]
```

从结果可以看出仍然有bug，原因是如果两个无符号数相加溢出的符号位无法得到保存，这样得到的结果显然存在bug。

#### exercise 9,10

从这个exercise开始，我们要开始实现真正的求解平均数函数了，这个实现起来难度较大，主要代码如下：

```python
t = (x & y) + ((x ^ y) >> 1)	# 保证不溢出
s = (LSHR(t, 31) & (x ^ y))		# 判断是否向0舍入
return t + s					# 向0舍入
```

从条件可知，只有得到结果最高位为1，并且x,y的最低位不同会发生舍入。

**exercise10给出了如下代码:**

```c++
int myfunction(int *array, int len){
	int *myarray, i;

	myarray = malloc(len * sizeof(int));    /* [1] */
    if(myarray == NULL){
        return -1;
    }
    for(i = 0; i < len; i++){              /* [2] */
        myarray[i] = array[i];
    }
	return myarray;
}
```

代码[1]处，len * (sizeof(int))可能存在越界溢出风险，除此之外，如果前面发生溢出，myarray分配空间成功，代码[2]处很可能发生越界写的问题。

#### exercise 11

给定两个数相乘，判断是否溢出。

```python
def detect_multi_overflow(x, y):
    v1 = x.as_signed_long()
    v2 = y.as_signed_long()
    if v1 * v2 < 0:
        return (True, 0)
    else:
        return (False, v1 * v2)
```

这是一个git上一个取巧的写法，实际上还要考虑多种情况，较为复杂。

#### exercise 12

```python
def fermat(x, y, z, n):
    cons = []
    cons.append(x & 0xffffff00 == 0)
    cons.append(y & 0xffffff00 == 0)
    cons.append(z & 0xffffff00 == 0)
    cons.append(x != 0)
    cons.append(y != 0)
    cons.append(z != 0)
    v1 = x
    v2 = y
    v3 = z
    for i in range(1, n):
        v1 = v1 * x
        v2 = v2 * y
        v3 = v3 * z
    cons.append(v1 + v2 == v3)
    return cons
```

验证费马大定理在一定范围内是成立的，从结果来看，n=3验证时间超过10s，n越大，时间呈指数数量级增长，最终得到无解，费马大定理成立。

### Part B arrays

#### exercise 13,14,15,16

这一块主要是实现对于数组的存取，并用z3验证。实现起来较为简单，结果如下：

```python
def array_proof():
    array = Array('a', IntSort(), IntSort())
    value = Int('x')
    index = Int('i')
    solver = Solver()
    t = Select(Store(array, index, value), index)
    solver.add(simplify(t) >= value)
    res = solver.check()
    if res == sat:
        print('SAT')
    else:
        print('UNSAT')
```

```python
def array_non_linear_proof():
    array = Array('a', IntSort(), IntSort())
    value = Int('x')
    index = Int('i')
    t = Select(Store(array, index * index - index * index, value), 0)
    solver = Solver()
    solver.add(simplify(t) >= value)
    res = solver.check()
    if res == sat:
        print('SAT')
    else:
        print('UNSAT')
```

```python
def array_new():
    return lambda x: 0

# array[index]
def array_select(array, index):
    return array(index)

# array[index] = element
def array_store(array, index, element):
    return lambda x: element if x == index else array(x)
```

### Part C pointers

#### exercise 17,18

这两个练习难度不大，主要是利用递归来实现对于表达式的求值和化简，所有的数据结构都已经给出，但在写的时候一定要注意不能遗漏，很容易出错，而且debug也需要较长的时间。

得到的结果如下：

```python
# T ::= x | T + E | &x | &*T | *T | NULL
# E ::= x | n | E + E | E - E | *T
# R ::= T = T | T < T | E = E | E < E
# P ::= R | ~R | P ∧ P
#
def count_stars(prop: Prop):
    # exercise 17: finish the missing code in `count_stars()` methods,
    # make it can count amount of star symbols (*) in our pointer logic .

    def term_count_stars(term: Term):
        if isinstance(term, TStar):
            return term_count_stars(term.term) + 1
        if isinstance(term, TAddrStar):
            return term_count_stars(term.term) + 1
        if isinstance(term, TAddE):
            return term_count_stars(term.term) + expr_count_stars(term.expr)
        return 0

    def expr_count_stars(expr: Expr):
        if isinstance(expr, EAdd):
            return expr_count_stars(expr.left) + expr_count_stars(expr.right)
        if isinstance(expr, EMinus):
            return expr_count_stars(expr.left) + expr_count_stars(expr.right)
        if isinstance(expr, EStar):
            return 1 + term_count_stars(expr.term)
        return 0

    def rel_count_stars(rel: Relation):
        if isinstance(rel, REEq) or isinstance(rel, RELe):
            return expr_count_stars(rel.left) + expr_count_stars(rel.right)
        else:
            return term_count_stars(rel.left) + term_count_stars(rel.right)

    if isinstance(prop, PRel) or isinstance(prop, PNot):
        return rel_count_stars(prop.rel)
    if isinstance(prop, PAnd):
        return count_stars(prop.left) + count_stars(prop.right)
```

```python
    def term_to_z3(term: Term):
        # rules to eliminate a pointer T
        #
        # ⟦x⟧      =   H(S(x))
        # ⟦T + E⟧  =   ⟦T⟧ + ⟦E⟧
        # ⟦&x⟧     =   S(x)
        # ⟦&*T⟧    =   ⟦T⟧
        # ⟦*T⟧     =   H(⟦T⟧)
        # ⟦NULL⟧   =   0
        #
        # your code here
        if isinstance(term, TVar):
            return H(S(Const(term.name, IntSort())))
        if isinstance(term, TAddE):
            return term_to_z3(term.term) + expr_to_z3(term.expr)
        if isinstance(term, TAddrStar):
            return term_to_z3(term.term)
        if isinstance(term, TAddr):
            return S(Const(term.name, IntSort()))
        if isinstance(term, TStar):
            return H(term_to_z3(term.term))
        if isinstance(term, TNull):
            return 0

    def expr_to_z3(expr: Expr):
        # rules to eliminate an expression E
        #
        # ⟦n⟧      =   n
        # ⟦x⟧      =   H(S(x))
        # ⟦E + E⟧  =   ⟦E⟧ + ⟦E⟧
        # ⟦E − E⟧  =   ⟦E⟧ − ⟦E⟧
        # ⟦*T⟧     =   H(⟦T⟧)
        #
        # your code here
        if isinstance(expr, EConst):
            return expr.value
        if isinstance(expr, EVar):
            return H(S(Const(expr.name, IntSort())))
        if isinstance(expr, EAdd):
            return expr_to_z3(expr.left) + expr_to_z3(expr.right)
        if isinstance(expr, EMinus):
            return expr_to_z3(expr.left) - expr_to_z3(expr.right)
        if isinstance(expr, EStar):
            return H(term_to_z3(expr.term))
    def relation_to_z3(rel: Relation):
        # rules to eliminate a relation R
        #
        # ⟦T = T⟧   =   ⟦T⟧ = ⟦T⟧
        # ⟦T < T⟧   =   ⟦T⟧ < ⟦T⟧
        # ⟦E = E⟧   =   ⟦E⟧ = ⟦E⟧
        # ⟦E < E⟧   =   ⟦E⟧ < ⟦E⟧
        #
        # your code here
        if isinstance(rel, RTEq):
            return term_to_z3(rel.left) == term_to_z3(rel.right)
        if isinstance(rel, RTLe):
            return term_to_z3(rel.left) < term_to_z3(rel.right)
        if isinstance(rel, REEq):
            return expr_to_z3(rel.left) == expr_to_z3(rel.right)
        if isinstance(rel, RELe):
            return expr_to_z3(rel.left) < expr_to_z3(rel.right)
    # rules to eliminate a proposition P
    #
    # ⟦R⟧      =   ⟦R⟧
    # ⟦~R⟧     =   ~⟦R⟧
    # ⟦P /\Q⟧  =   ⟦P⟧ / \ ⟦Q⟧
    #
    if isinstance(prop, PRel):
        return relation_to_z3(prop.rel)
    if isinstance(prop, PNot):
        return Not(relation_to_z3(prop.rel))
    if isinstance(prop, PAnd):
        return And(to_z3(prop.left), to_z3(prop.right))
```



