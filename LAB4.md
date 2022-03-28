# LAB4: 谓词逻辑系统自动证明

### 回顾**coq程序基本的结构：**

```
Theorem (题目名字): forall P Q(所有变量) :Prop,
    需要证明的结论。
Proof.
    证明的过程。
Qed.
```

### 命题逻辑

- **intros** 蕴含 得到命题所有前提
- **inversion H** 反演 将前提H左边拆成两份（合取析取均可）
- **unford not** 非 将条件中的~变成false
- **elim** 消除谬误 如果条件中有**H0：P->false**此时使用命令**elim H0**命令相当于只需要证明**P**的正确性
- **spilt** 拆分 将合取结论拆成两份
- **left** 和 **right** 选择析取结论的左半部分和右半部分
- **apply** 应用 如果条件H与结论相同，可直接使用apply H完成证明
- **apply A in B** 以B为前提，结合A能够推出的结果,**这里一定要注意顺序**
- **assert (h : H)**  假设H为一个新的目标 当你证明了这个新的目标时 h作为你新的前提
- **destruct**  同inversion 将原命题拆分成两个命题，但可分别命名

### 谓词逻辑

- **Variables A B: Set.**  定义A,B两个两个集合
- **Variables P Q:A -> Prop.** 在集合A上定义谓词变量P,Q
- **Variable R : A -> B -> Prop.** 谓词变量R定义在A集合和集合B上，Prop代表某种性质

需要运用到的指令大部分都在上面，其他的按照逻辑一步一步推演即可, 总体而言难度不如上lab3。

结果如下：

```coq
Theorem exercise_1: forall P Q: Prop,
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
    unfold not.
    intros.
    split.
    intros.
    apply H.
    left.
    apply H0.
    intros.
    apply H.
    right.
    apply H0.
Qed.


Theorem exercise_2 : forall P Q R: Prop,
    P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
    split.
    intros.
    destruct H as [H1 H2].
    inversion H2.
    left.
    split.
    apply H1.
    apply H.
    right.
    split.
    apply H1.
    apply H.
    intros.
    destruct H as [H1 | H2].
    inversion H1.
    split.
    apply H.
    left.
    apply H0.
    split.
    inversion H2.
    apply H.
    right.
    inversion H2.
    apply H0.
Qed.


Variables A B: Set.
Variables P Q R: A->Prop.
Theorem exercise_3:
    (forall x:A, ~P x /\ Q x) -> (forall x:A, P x -> Q x).
Proof.
    intros.
    apply H.
Qed.


Theorem exercise_4:
    (forall x: A, (P x -> Q x)) -> (forall x: A,~Q x) -> (forall x: A, ~P x).
Proof.
    intros.
    intros H1.
    apply H in H1.
    apply H0 in H1.
    apply H1.
Qed.


Theorem exercise_5:
    (forall x: A, (P x /\ Q x)) <-> (forall x: A,P x) /\ (forall x: A, Q x).
Proof.
    split.
    split.
    intros.
    apply H.
    apply H.
    intros.
    split.
    apply H.
    apply H.
Qed.


Theorem exercise_6:
    (exists x:A, (~P x \/ Q x)) -> (exists x:A, (~(P x /\ ~Q x))).
Proof.
    intros.
    inversion H.
    exists x.
    inversion H0.
    intros H2.
    inversion H2.
    apply H1 in H3.
    apply H3.
    intros H4.
    inversion H4.
    apply H3 in H1.
    apply H1.
Qed.


Theorem exercise_7:
    (exists x:A, (~P x /\ ~Q x)) -> (exists x:A, ~(P x /\ Q x)).
Proof.
    intros.
    inversion H.
    exists x.
    intros H1.
    inversion H0.
    inversion H1.
    apply H3 in H5.
    apply H5.
Qed.


Theorem exercise_8:
    (exists x:A, (P x \/ Q x)) <-> (exists x:A, P x) \/ (exists x:A, Q x).
Proof.
    split.
    intros.
    inversion H.
    inversion H0.
    left.
    exists x.
    apply H1.
    right.
    exists x.
    apply H1.
    intros.
    inversion H.
    inversion H0.
    exists x.
    left.
    apply H1.
    inversion H0.
    exists x.
    right.
    apply H1.
Qed.


Theorem exercise_9:
    (exists x:A, ~P x) -> ~(forall x:A, P x).
Proof.
    intros.
    inversion H.
    unfold not.
    intros.
    apply H0 in H1.
    apply H1.
Qed.


Theorem exercise_10:
    (forall x:A, P x -> ~Q x) -> ~(exists x:A, (P x /\ Q x)).
Proof.
    unfold not.
    intros.
    inversion H0.
    inversion H1.
    apply H in H2.
    apply H2.
    apply H3.
Qed.

       
Theorem exercise_11:
    (forall x:A, P x -> Q x) /\ (exists x:A, P x ) -> (exists x:A, Q x).
Proof.
    unfold not.
    intros.
    inversion H.
    inversion H1.
    apply H0 in H2.
    exists x.
    apply H2.
Qed.


Theorem exercise_12:
    (exists x:A, P x /\ Q x) /\ (forall x:A, P x -> R x) -> (exists x:A, R x /\ Q x).
Proof.
    intros.
    inversion H.
    inversion H0.
    inversion H2.
    apply H1 in H3.
    exists x.
    split.
    apply H3.
    apply H4.
Qed.
```



