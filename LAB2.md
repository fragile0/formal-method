## LAB2

​	   lab2总体来说比lab1有意思很多，做完感觉像通关打游戏一样，看一个例子，写一个练习，不知不觉就写完了，感觉意犹未尽。实现过程参考了https://blog.csdn.net/m0_37714470/article/details/105375686.

**做之前需要了解一下coq程序基本的结构：**

```
Theorem (题目名字): forall P Q(所有变量) :Prop,
    需要证明的结论。
Proof.
    证明的过程。
Qed.
```

  另外其他需要注意的主要如下：

- **ctrl + ↓ 让程序执行到光标的下一行，ctrl + ↑ 让程序执行到上一行。类似于可以回退的单步调试。**
- **证明的过程中每一句后面必须加上.**

- **原则：先有前提(inversion)后有结论(spilt)	 先提出的结论必须先证.**   （详细见exercise4）
- 如果要证明 **A->(B->C)->D->(E->F)->G** 其中**A,(B->C),D,(E->F)**均为前提，而**G**为结论。
- **intros** 蕴含				 得到命题所有前提  	
- **inversion H** 反演	  将前提H左边拆成两份（合取析取均可）
- **spilt** 拆分					将结论拆成两份
- **unford not**  非           将条件中的~变成false
- **elim** 消除谬误            如果条件中有**H0：P->false**此时使用命令**elim H0**命令相当于只需要证明**P**的正确性
- **left** 和 **right** 			   分别选择结论 选择析取的左半部分和右半部分
- **apply**  应用                 如果条件H与结论相同，可直接使用apply H完成证明
- **apply A in B**               以B为前提，结合A能够推出的结果,**这里一定要注意顺序**

具体结果如下：

```
Theorem exercise1: forall P Q :Prop,
    P -> (Q -> P).
Proof.
    intros.
    apply H.

Qed.

Theorem exercise2: forall P Q H:Prop,
     (P->Q) -> (Q->H) -> (P->H).
Proof.
    intros.
    apply H0 in H2.
    apply H1 in H2.
    apply H2.
Qed.

Theorem exercise3: forall P Q :Prop,
       P /\ (P -> Q) -> Q.
Proof.
    intros.
    inversion H.
    apply H1 in H0.
    apply H0.
Qed.

Theorem exercise4: forall P Q R:Prop,
     (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
Proof.
    intros.
    inversion H.
    inversion H1.
    split.
    split.
    apply H0.
    apply H2.
    apply H3.
Qed.

Theorem exercise5: forall P Q R:Prop,
      (P \/ (Q \/ R)) -> ((P \/ Q) \/ R).
Proof.
    intros.
    inversion H.
    left.
    left.
    apply H0.
    inversion H0.
    left.
    right.
    apply H1.
    right.
    apply H1.
Qed.

Theorem exercise6: forall P Q R:Prop,
    ((P -> R) /\ (Q -> R)) -> (P /\ Q -> R).
Proof.
    intros.
    inversion H.
    inversion H0.
    apply H1 in H3.
    apply H3.
Qed.    

Theorem exercise7: forall P Q R:Prop,   
    (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof.
    intros.
    split.
    apply H.
    apply H.
Qed.

Theorem challenge1: forall P Q R S T:Prop,
    (((P /\ Q) /\ R) /\ (S /\ T)) -> (Q /\ S).
Proof.
    intros.
    inversion H.
    inversion H0.
    inversion H1.
    inversion H2.
    split.
    apply H7.
    apply H4.
Qed.

Theorem challenge2: forall P Q:Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
    unfold not.
    intros.
    apply H in H1.
    apply H0 in H1.
    apply H1.
Qed.    
```

