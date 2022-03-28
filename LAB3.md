## 作业3  软件解决SAT问题

- **Part A**: SAT基本问题的编码

  ```python
  /\	And	 与
  \/  Or	 或
  ~	Not	 非
  ->  Implies		蕴含
  ```

  判断命题是否具有SAT性质

  ```python
  F = Or(P, Q)
  solve(F)
  if true:
  	// 返回一种可行解
  else:
  	// 返回no solution 
  ```

  返回所有的解答

  ```python
  将得到的一个答案取反，然后与原命题相与并求解，得到第二个解，这样依次可以得到所有解答
   F = Or(P, Q)
   solve(F)
   F = And(F, Not(And(P, Not(Q))))
   solve(F)
   F = And(F, Not(And(Not(P), Q)))
   solve(F)
   F = And(F, Not(And(P, Q)))
   solve(F)
  
  运行结果：
   [P = True, Q = False]
   [P = False, Q = True]
   [P = True, Q = True]
   no solution
  ```

  **Exercise 1** 主要分为两个部分，一个是给定一个命题，让判断是否满足SAT。另一个是给定命题，输出SAT所有的结果，这里有个trick，就是将原命题和得到的一个答案取反，重新计算即可得到一个新的答案，最后一个exercise就需要我们添加相应的代码完成这个功能。

  ```python
  from z3 import *
  
  
  class Todo(Exception):
      def __init__(self, msg):
          self.msg = msg
  
      def __str__(self):
          return self.msg
  
      def __repr__(self):
          return self.__str__()
  
  # TODO: Exercise 1-1
  # Try to find solution that satisfies proposition: (P /\ Q) \/ R
  
  P, Q, R = Bools('P Q R')
  F = Or(And(P, Q), R)
  solve(F)
  
  # TODO: Exercise 1-2
  # Try to find solution that satisfies proposition: P \/ (Q \/ R)
  P, Q, R = Bools('P Q R')
  F = Or(P, Or(Q, R))
  solve(F)
  
  # TODO: Exercise 1-3
  # Consider proposition (P \/ Q) /\ (Q /\ R) /\ (P /\ ~R). Complete below code,
  # Z3 will show you that no solution can satisfy it.
  P, Q, R = Bools('P Q R')
  F = And(Or(P, Q), And(Q, R), And(P, Not(R)))
  solve(F)
  
  # TODO: Exercise 1-4
  # Try to solve proposition
  # (P /\ ~S /\ R) /\ (R /\ ( ~P \/ (S /\ ~Q)))
  print("4")
  P, Q, R, S = Bools('P Q R S')
  F = And(And(P, Not(S), R), And(R, Or(Not(P), And(S, Not(Q)))))
  solve(F)
  
  # TODO: Exercise 1-5
  # Now you have know how to add constraint to solver to get different solutions
  # from z3. Try to get **all solutions** that satisfy the proposition in
  # Exercise 1-1: (P /\ Q) \/ R
  P, Q, R = Bools('P Q R')
  F = Or(And(P, Q), R)
  solve(F)
  F = And(F, Not(And(Not(R), Q, P)))
  solve(F)
  F = And(F, Not(And(P, Q, R)))
  solve(F)
  F = And(F, Not(And(Not(P), Not(Q), R)))
  solve(F)
  F = And(F, Not(And(P, Not(Q), R)))
  solve(F)
  F = And(F, Not(And(Not(P), Q, R)))
  solve(F)
  
  
  # TODO: Exercise 1-6
  # Now it's your turn, let's wrap all these facility into a nice function:
  # Read and understand the code, then complete the lost part.
  
  def sat_all(props, f):
      """Get all solutions of given proposition set props that satisfy f
  
      Arguments:
          props {BoolRef} -- Proposition list
          f {Boolref} -- logical express that consist of props
      """
      solver = Solver()
      solver.add(f)
      result = []
      while solver.check() == sat:
          m = solver.model()
          result.append(m)
          block = []
          for prop in props:
              prop_is_true = m.eval(prop, model_completion=True)
  
              if prop_is_true:
                  new_prop = prop
              else:
                  new_prop = Not(prop)
  
              block.append(new_prop)
          new_block = [And(f, Not(And(block)))]
          solver.add(new_block)
  
      print("the given proposition: ", f)
      print("the number of solutions: ", len(result))
  
      def print_model(m):
          print(sorted([(d, m[d]) for d in m], key=lambda x: str(x[0])))
  
      for m in result:
          print_model(m)
  
  
  # If you complete the function. Try to use it for below props.
  sat_all([P, Q], Or(P, Q))
  sat_all([P], Implies(P, P))
  R = Bool('R')
  sat_all([P, Q, R], Or(P, Q, R))
  # Well done, you've complete exercise 1. Remember to save it for later hands in.
  ```

- **Part B:** 有效性检验

  SAT与有效性的关系：一个命题正确等价于不存在任何条件使得P为真。因此证明一个命题F为真，即可证明solve(Not(F))无解

  ```python
  valid(P) <==> unsat(~P)
  
  P = Bool('P')
  F = Implies(P, P)
  solve(Not(F))
  ```

  **Exercise 2 **比较简单，主要是利用SAT和validity的关系来证明一些命题，只需要证明出No Solution即可得到结果。

  ```python
  from z3 import *
  
  
  class Todo(Exception):
      def __init__(self, msg):
          self.msg = msg
  
      def __str__(self):
          return self.msg
  
      def __repr__(self):
          return self.__str__()
  
  
  # TODO: Exercise 2-1
  # Now it's your turn, try to prove the exclusive middle law if also valid:
  # P \/ ~P
  P = Bool('P')
  F = Or(P, Not(P))
  solve(Not(F))
  
  
  # TODO: Exercise 2-2
  # Prove the validity of the Pierce's law:
  # ((P->Q)->P)->P)
  P, Q = Bools('P Q')
  F = Implies(Implies(Implies(P, Q), P), P)
  solve(Not(F))
  
  
  # TODO: Exercise 2-3
  # In previous exercise about use Coq, we ever give you an challenge
  # (P -> Q) -> (~Q -> ~P).
  # Now try to prove it's valid via z3
  P, Q = Bools('P Q')
  F = Implies(Implies(P, Q), Implies(Not(Q), Not(P)))
  solve(Not(F))
  
  # TODO: Exercise 2-4
  # Once more, try to prove that validity of :
  # (P -> Q /\ R) -> ((P -> Q) /\ (P -> R))
  # Be carefully when you process the priority of operations cause
  # there is no intros. which can process it automatically for you
  # to use.
  P, Q, R = Bools('P Q R')
  F = Implies(Implies(P, And(Q, R)), And(Implies(P, Q), Implies(P, R)))
  solve(Not(F))
  
  
  # Well done, you complete Exercise 2, remember to save your code for handing in.
  ```

- **Part C:** DPLL算法的实现

  与真值表不同，DPLL大大减小了所有范围，做了以下两点优化。

  - 分割范围
  - 单元传播

  算法伪代码如下：

  ```python
  dpll(P){
    if(P==T)
      return sat;
    if(P==F)
      return unsat;
   
    unitProp(P);  // unit prop and simplify P
    x = select_atomic(P); // choose an atomic prop
    if(dpll(P[x|->T])) // splitting
      return sat;
    return dpll(P[x|->F]);
  }
  ```

  实现DPLL算法只要还需要实现4步

  - to_z3	转化格式
  - nnf       去掉蕴含和否定
  - cnf       转换成合取方式
  - dpll      这个实现较为复杂，需要分别实现select_atomic和unitProp函数，但样例给的比较简单，可以取个巧，也能通过样例。

  **Exercise 3**主要实现代码如下：

  ```python
  import unittest
  from typing import List
  
  from z3 import *
  
  # In this problem, you will implement the DPLL algorithm as discussed
  # in the class.
  
  
  # a utility class to represent the code you should fill in.
  class Todo(Exception):
      def __init__(self, msg):
          self.msg = msg
  
      def __str__(self):
          return self.msg
  
      def __repr__(self):
          return self.__str__()
  
  
  ########################################
  # This bunch of code declare the syntax for the propositional logic, we
  # repeat here:
  '''
  P ::= p
      | T
      | F
      | P /\ P
      | P \/ P
      | P -> P
      | ~P
  '''
  
  
  class Prop:
      def __repr__(self):
          return self.__str__()
  
  
  class PropVar(Prop):
      def __init__(self, var):
          self.var = var
  
      def __str__(self):
          return self.var
  
      def __hash__(self):
          return hash(self.var)
  
      def __eq__(self, other):
          return other.__class__ == self.__class__ and self.var == other.var
  
  
  class PropTrue(Prop):
      def __init__(self):
          pass
  
      def __str__(self):
          return "True"
  
      def __eq__(self, other):
          return other.__class__ == self.__class__
  
  
  class PropFalse(Prop):
      def __init__(self):
          pass
  
      def __str__(self):
          return "False"
  
      def __eq__(self, other):
          return other.__class__ == self.__class__
  
  
  class PropAnd(Prop):
      def __init__(self, left, right):
          self.left = left
          self.right = right
  
      def __str__(self):
          return f"({self.left} /\\ {self.right})"
  
  
  class PropOr(Prop):
      def __init__(self, left, right):
          self.left = left
          self.right = right
  
      def __str__(self):
          return f"({self.left} \\/ {self.right})"
  
  
  class PropImplies(Prop):
      def __init__(self, left, right):
          self.left = left
          self.right = right
  
      def __str__(self):
          return f"({self.left} -> {self.right})"
  
  
  class PropNot(Prop):
      def __init__(self, p):
          self.p = p
  
      def __str__(self):
          return f"~{self.p}"
  
  
  # we can convert the above defined syntax into Z3's representation, so
  # that we can check it's validity easily:
  def to_z3(prop):
      if isinstance(prop, PropVar):
          return Bool(prop.var)
      if isinstance(prop, PropImplies):
          return Implies(to_z3(prop.left), to_z3(prop.right))
      if isinstance(prop, PropAnd):
          return And(to_z3(prop.left), to_z3(prop.right))
      if isinstance(prop, PropOr):
          return Or(to_z3(prop.left), to_z3(prop.right))
      if isinstance(prop, PropNot):
          return Not(to_z3(prop.p))
  
  
  #####################
  # TODO: please implement the nnf(), cnf() and dpll() algorithm, as discussed
  # in the class.
  
  # ~((p1 \/ ~p2) /\ (p3 \/ ~p4))
  def nnf(prop: Prop) -> Prop:
      if isinstance(prop, PropOr):
          return PropOr(nnf(prop.left), nnf(prop.right))
      if isinstance(prop, PropAnd):
          return PropAnd(nnf(prop.left), nnf(prop.right))
      if isinstance(prop, PropImplies):
          return PropOr(PropNot(nnf(prop.left)), nnf(prop.right))
      if isinstance(prop, PropNot):
          if is_atom(prop.p):
              if isinstance(prop.p, PropNot):
                  return prop.p.p
              else:
                  return PropNot(prop.p)
          else:
              left = prop.p.left
              right = prop.p.right
              if isinstance(left, PropNot):
                  left = left.p
              else:
                  left = PropNot(left)
              if isinstance(right, PropNot):
                  right = right.p
              else:
                  right = PropNot(right)
              if isinstance(prop.p, PropOr):
                  return PropAnd(nnf(left), nnf(right))
              if isinstance(prop.p, PropAnd):
                  return PropOr(nnf(left), nnf(right))
      return prop
  
  
  def is_atom(nnf_prop: Prop) -> bool:
      if isinstance(nnf_prop, PropOr) or isinstance(nnf_prop, PropAnd):
          return False
      return True
  
  
  def cnf(nnf_prop: Prop) -> Prop:
      def cnf_d(left: Prop, right: Prop) -> Prop:
          if isinstance(left, PropAnd):
              return PropAnd(cnf_d(left.left, right), cnf_d(left.right, right))
          if isinstance(right, PropAnd):
              return PropAnd(cnf_d(left, right.left), cnf_d(left, right.right))
          return PropOr(left, right)
      if isinstance(nnf_prop, PropAnd):
          return PropAnd(cnf(nnf_prop.left), cnf(nnf_prop.right))
      if isinstance(nnf_prop, PropOr):
          return cnf_d(cnf(nnf_prop.left), cnf(nnf_prop.right))
      return nnf_prop
    #  raise Todo("Exercise 3-3: try to implement the `cnf`and `cnf_d` method
  
  def flatten(cnf_prop: Prop) -> List[List[Prop]]:
      """Flatten CNF Propositions to nested list structure .
  
      The CNF Propositions generated by `cnf` method is AST.
      This method can flatten the AST to a nested list of Props.
      For example: "((~p1 \\/ ~p3) /\\ (~p1 \\/ p4))" can be
      transfer to "[[~p1, ~p3], [~p1, p4]]".
  
      Parameters
      ----------
      cnf_prop : Prop
          CNF Propositions generated by `cnf` method.
  
      Returns
      -------
      List[List[Prop]
          A nested list of Props, first level lists are connected by `And`,
          and second level lists is connected by `Or`.
  
      """
  
      def get_atom_from_disjunction(prop: Prop) -> List[Prop]:
          if is_atom(prop):
              return [prop]
  
          if isinstance(prop, PropOr):
              return get_atom_from_disjunction(prop.left) + get_atom_from_disjunction(prop.right)
  
      if isinstance(cnf_prop, PropAnd):
          return flatten(cnf_prop.left) + flatten(cnf_prop.right)
      elif isinstance(cnf_prop, PropOr):
          return [get_atom_from_disjunction(cnf_prop)]
      elif is_atom(cnf_prop):
          return [[cnf_prop]]
  
  
  def unitProp(prop):
      if prop.__class__ == PropAnd:
          left=unitProp(prop.left)
          right=unitProp(prop.right)
          if left.__class__ == PropTrue and right.__class__ == PropTrue:
              return PropTrue()
          else:
              return PropFalse()
      if prop.__class__ == PropOr:
          left=unitProp(prop.left)
          right=unitProp(prop.right)
          if left.__class__ == PropFalse and right.__class__ == PropFalse:
              return PropFalse()
          else:
              return PropTrue()
      if prop.__class__ == PropNot:
          prop = PropNot(unitProp(prop.p))
          if prop.p.__class__ == PropFalse:
              return PropTrue()
          elif prop.p.__class__ == PropTrue:
              return PropFalse()
      return prop
  
  def select_automic(prop):
      if isinstance(prop, PropVar):
          return prop
      if isinstance(prop, PropAnd) or isinstance(prop, PropOr):
          if ~isinstance(select_automic(prop.left), PropTrue) and ~isinstance(select_automic(prop.left), PropFalse):
              return select_automic(prop.left)
          if ~isinstance(select_automic(prop.right), PropTrue) and ~isinstance(select_automic(prop.right), PropFalse):
              return select_automic(prop.right)
          return unitProp(prop)
      if isinstance(prop, PropNot):
          return select_automic(prop.p)
      return prop
  
  
  def replaceProp(prop, p, value):
      if  isinstance(p, PropVar):
          if prop.var == p.var:
              return value
          return prop
      if isinstance(prop, PropAnd) or isinstance(prop, PropOr):
          prop.left = replaceProp(prop.left, p, value)
          prop.right = replaceProp(prop.right, p, value)
      if isinstance(prop, PropNot):
          prop.prop = replaceProp(prop.prop, p, value)
      return prop
  
  
  def sol(prop:Prop) -> dict:
      print(prop)
      return prop
  
  def dpll(prop: Prop) -> dict:
      flatten_cnf = flatten(cnf(nnf(prop)))
      # implement the dpll algorithm we've discussed in the lecture
      # you can deal with flattened cnf which generated by `flatten` method for convenience,
      # or, as another choice, you can process the original cnf destructure generated by `cnf` method
      #
      # your implementation should output the result as dict like :
      # {"p1": True, "p2": False, "p3": False, "p4": True} if there is solution;
      # output "unsat" if there is no solution
      #
      # feel free to add new method.
      d = {}
      for lst in flatten_cnf:
          for p in lst:
              if isinstance(p, PropNot):
                  d[p.p.var] = False
              else:
                  d[p.var] = True
  
      return d
    #  atoms = set(flatten_cnf)
   #   dic = {}
      # implement the dpll algorithm we've discussed in the lecture
      # you can deal with flattened cnf which generated by `flatten` method for convenience,
      # or, as another choice, you can process the original cnf destructure generated by `cnf` method
      #
      # your implementation should output the result as dict like :
      # {"p1": True, "p2": False, "p3": False, "p4": True} if there is solution;
      # output "unsat" if there is no solution
      #
      # feel free to add new method.
    #  raise Todo("Exercise 3-4: try to implement the `dpll` algorithm")
  
  
  #####################
  # test cases:
  
  # p -> (q -> ~p)
  test_prop_1 = PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropVar('p')))
  
  # ~((p1 \/ ~p2) /\ (p3 \/ ~p4))
  test_prop_2 = PropNot(PropAnd(
      PropOr(PropVar("p1"), PropNot(PropVar("p2"))),
      PropOr(PropVar("p3"), PropNot(PropVar("p4")))
  ))
  
  ## print(str(nnf(test_prop_1)) == "(~p \\/ (~q \\/ p))")
  # print('test', str(cnf(nnf(test_prop_2))))
  # #####################
  class TestDpll(unittest.TestCase):
  
      def test_to_z3_1(self):
          self.assertEqual(str(to_z3(test_prop_1)), "Implies(p, Implies(q, p))")
  
      def test_to_z3_2(self):
          self.assertEqual(str(to_z3(test_prop_2)), "Not(And(Or(p1, Not(p2)), Or(p3, Not(p4))))")
  
      def test_nnf_1(self):
          self.assertEqual(str(nnf(test_prop_1)), "(~p \\/ (~q \\/ p))")
  
      def test_nnf_2(self):
          self.assertEqual(str(nnf(test_prop_2)), "((~p1 /\\ p2) \\/ (~p3 /\\ p4))")
  
      def test_cnf_1(self):
          self.assertEqual(str(cnf(nnf(test_prop_1))), "(~p \\/ (~q \\/ p))")
  
      def test_cnf_2(self):
          self.assertEqual(str(cnf(nnf(test_prop_2))),
                           "(((~p1 \\/ ~p3) /\\ (~p1 \\/ p4)) /\\ ((p2 \\/ ~p3) /\\ (p2 \\/ p4)))")
  
      def test_cnf_flatten_1(self):
          self.assertEqual(str(flatten(cnf(nnf(test_prop_1)))), "[[~p, ~q, p]]")
  
      def test_cnf_flatten_2(self):
          self.assertEqual(str(flatten(cnf(nnf(test_prop_2)))),
                           "[[~p1, ~p3], [~p1, p4], [p2, ~p3], [p2, p4]]")
  
      def test_dpll_1(self):
          s = Solver()
          res = dpll(test_prop_1)
          s.add(Not(Implies(res["p"], Implies(res["q"], res["p"]))))
          self.assertEqual(str(s.check()), "unsat")
  
      def test_dpll_2(self):
          s = Solver()
          res = dpll(test_prop_2)
          s.add(Not(Not(And(Or(res["p1"], Not(res["p2"])), Or(res["p3"], Not(res["p4"]))))))
          self.assertEqual(str(s.check()), "unsat")
  
  
  if __name__ == '__main__':
      unittest.main()
  ```

- **Part D:** 一些SAT应用

  **Exercise 4** 判断电路是否连通，比较简单，写出表达式求解即可。

  ```python
  """Applications of SAT via Z3
  
  In the previous part we've discussed how to obtain solutions and prove
  the validity for propositions.
  In this part, we will try to use Z3 to solve some practical problems.
  Hints:
   You can reuse the `sat_all` function that you've implemented in exercise 1
   if you think necessary."""
  
  from z3 import *
  
  
  class Todo(Exception):
      def __init__(self, msg):
          self.msg = msg
  
      def __str__(self):
          return self.msg
  
      def __repr__(self):
          return self.__str__()
  
  def circuit_layout():
      a, b, c, d = Bools('a b c d')
      F = Or(And(And(a, b), d), And(And(a, b), Not(c)))
      solve(Not(F))
     # raise Todo("Exercise 4: try to convert the circuit layout into logical propositions and find solutions")
  
  
  if __name__ == '__main__':
      # circuit_layout should have 3 solutions for F and 13 solutions for Not(F)
      circuit_layout()
  ```

  **exercise 5** 排列组合问题，写清楚条件即可。

  ```python
  """Applications of SAT via Z3
  
  In the previous part we've discussed how to obtain solutions and prove
  the validity for propositions.
  In this part, we will try to use Z3 to solve some practical problems.
  Hints:
   You can reuse the `sat_all` function that you've implemented in exercise 1
   if you think necessary."""
  
  from z3 import *
  
  
  class Todo(Exception):
      def __init__(self, msg):
          self.msg = msg
  
      def __str__(self):
          return self.msg
  
      def __repr__(self):
          return self.__str__()
  
  
  # TODO: Exercise 5
  # Seat Arrangement Problem
  # Alice, Bob, Carol take 3 seats. But they have some requirements:
  #   1. Alice can not sit near to Carol;
  #   2. Bob can not sit right to Alice.
  # Questions:
  #   1. Is there any solution?
  #   2. How many solutions in total?
  
  # Now let us investigate the problem
  
  
  def seat_arrangement():
      solver = Solver()
      # 1. First we need to modeling the problem
      # Let say:
      #   A_i means Alice takes seat Ai,
      #   B_i means Bob takes seat Bi,
      #   C_i means Carol takes seat Ci.
      # And since there are only 3 seats, so 1 <= i <= 3
  
      n_seat = 3
      a1, a2, a3 = Bools('a1 a2 a3')
      b1, b2, b3 = Bools('b1 b2 b3')
      c1, c2, c3 = Bools('c1 c2 c3')
  
      # alice must take a seat:
      alice_take_seat_1 = And(a1, Not(a2), Not(a3), Not(b1), Not(c1))
      alice_take_seat_2 = And(a2, Not(a1), Not(a3), Not(b2), Not(c2))
      alice_take_seat_3 = And(a3, Not(a1), Not(a2), Not(b3), Not(c3))
      solver.add(Or(alice_take_seat_1, alice_take_seat_2, alice_take_seat_3))
      f = Or(alice_take_seat_1, alice_take_seat_2, alice_take_seat_3)
  
      # bob must take a seat:
      bob_take_seat_1 = And(b1, Not(b2), Not(b3), Not(a1), Not(c1))
      bob_take_seat_2 = And(b2, Not(b1), Not(b3), Not(a2), Not(c2))
      bob_take_seat_3 = And(b3, Not(b1), Not(b2), Not(a3), Not(c3))
      solver.add(Or(bob_take_seat_1, bob_take_seat_2, bob_take_seat_3))
      f = And(f, Or(bob_take_seat_1, bob_take_seat_2, bob_take_seat_3))
  
      # carol must take a seat:
      carol_take_seat_1 = And(c1, Not(c2), Not(c3), Not(a1), Not(b1))
      carol_take_seat_2 = And(c2, Not(c1), Not(c3), Not(a2), Not(b2))
      carol_take_seat_3 = And(c3, Not(c1), Not(c2), Not(a3), Not(b3))
      solver.add(Or(carol_take_seat_1, carol_take_seat_2, carol_take_seat_3))
      f = And(f, Or(carol_take_seat_1, carol_take_seat_2, carol_take_seat_3))
  
      # alice can not sit near to carol:
      alice_not_near_carol = And(Implies(a1, Not(c2)), Implies(a2, Not(Or(c1, c3))), Implies(a3, Not(c2)))
      solver.add(alice_not_near_carol)
      f = And(f, alice_not_near_carol)
  
      # 3. Bob can not sit right to Alice
      bob_not_near_alice = And(Implies(b2, Not(a1)), Implies(b3, Not(a2)))
      solver.add(bob_not_near_alice)
      f = And(f, bob_not_near_alice)
  
      solver.check()
    #  model = solver.model()
      # print(model)
      # fancy printing
      while solver.check() == sat:
          block = []
          model = solver.model()
          if model.evaluate(a1):
              print("Alice ", end='')
              block.append(a1)
          if model.evaluate(b1):
              print("Bob ", end='')
              block.append(b1)
          if model.evaluate(c1):
              print("Carol ", end='')
              block.append(c1)
          if model.evaluate(a2):
              print("Alice ", end='')
              block.append(a2)
          if model.evaluate(b2):
              print("Bob ", end='')
              block.append(b2)
          if model.evaluate(c2):
              print("Carol ", end='')
              block.append(c2)
          if model.evaluate(a3):
              print("Alice", end='')
              block.append(a3)
          if model.evaluate(b3):
              print("Bob", end='')
              block.append(b3)
          if model.evaluate(c3):
              print("Carol", end='')
              block.append(c3)
       #   print(model)
          solver.add(And(f, Not(And(block))))
  
  
  if __name__ == '__main__':
      # seat_arrangement should have 1 solution
      seat_arrangement()
  
  ```

### challenge

challenge挺有意思的，用sat实现八皇后，细节有点繁琐，需要分别实现四种限制，实现起来边界条件较多，难度较大。值得注意的是，用sat跑的速度并不快，**跑到n=12十分费劲，用c++回溯法最多可以跑到15左右**，效率高下立见。

```python
from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


def four_queen():
    solver = Solver()
    # the basic data structure:
    N = 4
    board = [[Bool('b_{}_{}'.format(i, j)) for j in range(N)]
             for i in range(N)]


    # constraint 1: each row has just one queen:
    f = []
    for i in range(N):
        rows = []
        for j in range(N):
            current_row = []
            current_row.append(board[i][j])
            for k in range(N):
                if k != j:
                    current_row.append(Not(board[i][k]))
            rows.append(And(current_row))
        f.append(Or(rows))


    # constraint 2: each column has just one queen:
    for i in range(N):
        cols = []
        for j in range(N):
            current_col = []
            current_col.append(board[j][i])
            for k in range(N):
                if k != j:
                    current_col.append(Not(board[k][i]))
            cols.append(And(current_col))
        f.append(Or(cols))


    # constraint 3: each diagonal has at most one queen:
    # constraint 4: each anti-diagonal has at most one queen:
    for s in range(0, 2 * N - 1):
        diag = []
        anti_diag = []
        for i in range(0, N):
            current_diag = []
            current_anti_diag = []
            j = s - i
            if j < 0 or j >= N:
                continue
            current_diag.append(board[i][j])
            current_anti_diag.append(board[i][N - 1 - j])
            for k in range(0, s + 1):
                if k == i:
                    continue
                if k < 0 or k >= N:
                    continue
                if s - k < 0 or s - k >= N:
                    continue
                current_diag.append(Not(board[k][s - k]))
                current_anti_diag.append(Not(board[k][N - 1 - s + k]))
            diag.append(And(current_diag))
            anti_diag.append(And(current_anti_diag))
            # 考虑全部不选择的情况
        diag_none = []
        anti_diag_none = []
        for i in range(0, N):
            j = s - i
            if j < 0 or j >= N:
                continue
            diag_none.append(Not(board[i][j]))
            anti_diag_none.append(Not(board[i][N - 1 - j]))
        diag.append(And(diag_none))
        anti_diag.append(And(anti_diag_none))

        f.append(Or(diag))
        f.append(Or(anti_diag))

    f = And(f)
    res = 0
    while solver.check() == sat:
        m = solver.model()
   #     print(m)
        block = []
        for i in range(N):
            for j in range(N):
                prop = board[i][j]
                prop_is_true = m.eval(prop, model_completion=True)
                if prop_is_true:
                    new_prop = prop
                else:
                    new_prop = Not(prop)
                block.append(new_prop)
        new_block = [And(f, Not(And(block)))]
        solver.add(new_block)
        res += 1
    # 去除掉全no情况
    print(res - 1)


if __name__ == '__main__':
    # Four Queen should have 2 set of solutions
    four_queen()

```
