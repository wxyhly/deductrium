export const mapData = `

// 游戏大厅

@欢迎来到游戏[n]Deductrium![n]按WASD或[n]拖动画面进行移动
3$[[deduct]]解锁推理层与[n]逻辑蕴含符号“→”（>）
5$[[progress]]解锁进度层
3,2#a>a#p
    3,4@#p闸门开启方法：[n]当推理层的定理列表中[n]包含闸门上的字符串时[n]才能通过闸门
    3,4,4#a>(b>c)#p
    3,4,4,2#a>(a>a)#p
    3,4,2#a>((a>a)>a)#p
    3,4,2,4#(a>(a>a))>(a>a)#p
    :%,4@你现在应该有能力[n]得到a>a了吧
    3,4,2,2@提示：对刚才闸门上的东西[n]使用推理规则a2[n]看能推出什么
    :%,2@mp的意思是：[n]定理列表中如果有A与A>B[n]则定理列表就能加入B
    1@未解锁的闸门无法通过[n]请寻找线索解开闸门
3,2,2$[[neg]]解锁否定公理a3[n]即符号“¬”（~）
    :neg,4#~$0⊢$0>$1#d
    // :%,
3,2,4$[[hyp]]解锁假设与宏[n]注意：假设出的定理[n]不可用于开启门#p
    :hyp,2$
    :hyp,4@录制宏将记录[n]定理表中最后的定理[n]和用到的假设
    :%*,4@与其它推理规则类似[n]使用宏时可[n]自由替换“$”开头的项
    :%*,4,4@#d闸门开启方法：[n]当推理层的推理规则表中[n]包含闸门上的字符串时[n]才能通过闸门
    :%,2#⊢$0>$0#d
    :%*,4#$0⊢$1>$0#d
    :%,2#$0⊢$2>($1>$0)#d
    :%*,4#$0>$1,$0>($1>$2)⊢$0>$2#d
    :%*,4,2$[[mcdt]]解锁条件演绎元定理
    :%,2#$0>$1,$1>$2⊢$0>$2#d
    :%*,4@不知你是否注意到了[n]左边分叉路要么[n]是关于右边的提示[n]要么是右边的基础
    :%,2#$1,$0>($1>$2)⊢$0>$2#d
    :%,2$[[mct]]解锁演绎元定理
:neg,2#(($0>$1)>$1)>$1#p
:neg,2,2$[[1st]]解锁全称量词






// type theory

:port-iff,5@提示：解锁等词传递性[n]（a=b,b=c ⊢ a=c）后[n]才可能解锁ZFC集合论[n]或解锁类型层
:type,4@值a的类型是A[n]记作a:A
:type,5@#t闸门开启方法：[n]定理列表中有[n]门上写的类型的值时[n]才能通过闸门
:%*,0#U[n]#t
:%*,4@开启之门即为真理[n]谬误之门无法通过[n]但有些真理却……
    :%*,4,2#~~True->True
    :%*,4,3#eq (eq nat 0 0) (refl nat 0) (refl nat 0)
    :%*,4,4#Pa:U,Sum a ~a
:%*,5#False[n]#t
:%,3#True[n]#t
:%,4$解锁函数符号“λ”（L）[n]与函数类型符号“Π”（P）[n]与函数类型简写符号“→”(->)
    :%*,1@函数表达式为λx:A.b[n]其自变量x类型为A[n]输出(因变量)值为b
    :%*,1,1@若x:A能推出b:B[n]则λx:A.b的类型为[n]Πx:A,B[n](特别注意“.”与“,”！）
    :%*,1,1,1@后面将看到函数输出类型B[n]可能依赖于输入x的值[n]对于类型Πx:A,B[n]若B不依赖于x[n]则简写为A->B
    :%*,1,1,1,1@λx:A.x的类型是Πx:A,A[n]因为x的类型是A[n]亦可简写为A->A
    :%*,1,1,1,1,1@λx:A.True的类型是Πx:A,U[n]因为True的类型是U[n]亦可简写为A->U
    :%*,1,1,1,1,1,1@函数可以嵌套，如[n]λx:A.λy:B.x其实是[n]λx:A.(λy:B.x)[n]其类型是[n]Πx:A,Πy:B,A[n]亦可简写为A->(B->A)
    :%*,3@与量词类似[n]λ后的变量x出现在“.”后的表达式中[n]都是约束变量
    :%*,3,5@类似也有变量[n]在某表达式中[n]“自由出现”的概念
:%,5#Px:True,True[n]#t
:%,5#Px:False,False[n]#t
:%,0#Pa:U,U[n]#t
    :%*,4@不同于传统编程中的函数[n]函数输出值的类型[n]可以依赖于输入的自变量
    :%*,4,5@λx:U.λy:x.y类型为[n]Πx:U,Πy:x,x[n]因为λy:x.y[n]类型为Πy:x,x
    :%*,4,5,5@λx:U.λy:x.y的类型[n]也可写作Πx:U,x->x[n]因为Πy:x,x代表[n]输出值的类型始终是x[n]与输入y的值无关
:%,5#Pa:U,Px:a,a[n]#t
:%,0#Px:True,Py:False,True[n]#t
:%,5#Pa:U,Pb:U,Px:a,Py:b,a[n]#t
:%,0$解锁简写非依赖函数[n]类型符号“→”（->）#t
    :%*,4@若类型Πx:A,B中[n]x不在表达式B中自由出现[n]则该类型可省去x[n]并记作：A→B
    :%*,4,5@默认符号“→”是右结合的[n]即A→B→C为[n]A→(B→C)
    :%*,4,5,5@例：λx:A→B.x[n]的类型为(A→B)→(A→B)
    :%*,4,5,5,0@α-等价规则：[n]若z不在y中自由出现[n]则λx:A.y等价于λz:A.y'[n]其中y'是将y中自由的x[n]替换为z的结果
:%,5#Pa:U,Pb:U,Pc:U,a->b->a[n]#t
    :%*,5@β-归约规则：[n]若a:A，f:A->B[n]则函数f可以作用于a[n]记作f a
    :%*,5,0@若a:A，则有[n](λx:A.y) a等价于[n]将y中自由的x替换成a
    :%*,5,0,5,3@注意λx:A.y a的含义是[n]λx:A.(y a)而不是[n](λx:A.y) a
    :%*,5,0,5@计算(λx:A.λy:B.z) y时[n]将z中自由的x替换为y[n]将被λy:B约束[n]系统将自动使用α-等价[n]更改自变量名称来规避
    :%*,5,0,5,0@例：λx:A→B.λy:A.x y[n]的类型为(A→B)→(A→B)[n]因为x y的类型为B
    :%*,5,0,5,0,5@若把有变量的类型是A[n]翻译成“A是定理”[n]则示例函数可翻译为[n]推理层中的规则mp
:%,0#Pa:U,Pb:U,Pc:U,(a->b->c)->(a->b)->(a->c)[n]#t
:%,5$解锁简写否定符号“¬”（~）
    :%*,3$解锁证明策略[n]intro/apply
:%,0#True->~~True
:%,5#Pa:U,Pb:U,(a->b)->(~b->~a)
:%,0$解锁每个类型的归纳函数
:%,5$解锁自然数类型
:%,0$解锁相等类型
:%,5#eq nat 0 0
:%,0#eq U nat nat
:%,5#eq nat (succ 0) (succ 0)
:%,0#解锁自然数1-10简写
:%,5#eq nat 5 5
:%,0$解锁翻倍函数
:%,5#eq nat (double 3) 6 
:%,0$解锁加法函数
:%,5#eq nat (add 1 1) 2
:%,0#Px:nat,eq nat (add 0 x) x
:%,5#Px:nat,Py:nat,(eq nat x y)->(eq nat (succ x) (succ y))
:%,0#Px:nat,eq nat (add 0 x) x
:%,5#Px:nat,Py:nat,(eq nat x y)->(eq nat y x)
:%,0$解锁证明策略[n]rewrite
:%,5#Px:nat,Py:nat,Pz:nat,(eq nat x y)->(eq nat y z)->(eq nat x z)
:%,0$解锁和类型
:%,5#Sum True False
:%,0$解锁积类型
:%,5#~(Prod True False)
:%,0$解锁依赖积类型
`;