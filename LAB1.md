## LAB1

​		lab1比较简单，感觉更多的是偏介绍性质的，最后需要实现一个表达式求值的功能。但是其中最难的递归树已经帮你画好了，只需要你利用递归树求值，这个无疑大大降低了题目的难度。

​		总共有四个tests，前两个tests需要将递归树转换成相应的字符串，这个实现\__str__()函数即可。后两个tests需要用递归树求值，这相当于一个后序遍历的过程，写一个递归函数即可。

​	最后出现如下字样代表实验通过。

```python
Ran 4 tests in 0.003s
```

​	整个代码如下：

```python
import unittest


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


class Exp:

    def __repr__(self):
        return self.__str__()


class ExpVar(Exp):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


class ExpAdd(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} + {self.right}"


class ExpMinus(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} - {self.right}"


class ExpMulti(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} * {self.right}"


class ExpDiv(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} / {self.right}"


class ExpPar(Exp):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "(" + str(self.value) + ")"


def eval_value(exp: Exp):
    if isinstance(exp, ExpVar):
        return exp.value
    if isinstance(exp, ExpPar):
        return eval_value(exp.value)
    if isinstance(exp, ExpAdd):
        return eval_value(exp.left) + eval_value(exp.right)
    if isinstance(exp, ExpMinus):
        return eval_value(exp.left) - eval_value(exp.right)
    if isinstance(exp, ExpDiv):
        return eval_value(exp.left) / eval_value(exp.right)
    if isinstance(exp, ExpMulti):
        return eval_value(exp.left) * eval_value(exp.right)


test_case_1 = ExpAdd(
    ExpMulti(ExpVar(3), ExpVar(4)),
    ExpDiv(ExpVar(10), ExpVar(2))
)

test_case_2 = ExpMinus(
    ExpMulti(
        ExpPar(ExpAdd(ExpVar(12), ExpVar(217))),
        ExpVar(3)
    ),
    ExpVar(621)
)


class TestTableau(unittest.TestCase):

    def test_print_1(self):
        self.assertEqual(str(test_case_1), "3 * 4 + 10 / 2")

    def test_print_2(self):
        self.assertEqual(str(test_case_2), "(12 + 217) * 3 - 621")

    def test_eval_1(self):
        self.assertEqual(eval_value(test_case_1), 17)

    def test_eval_2(self):
        self.assertEqual(eval_value(test_case_2), 66)


if __name__ == '__main__':
    print(ExpAdd(ExpVar(12), ExpVar(217)))
    unittest.main()

```



