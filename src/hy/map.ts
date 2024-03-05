export const mapData = `
:@欢迎来到游戏[n]Deductrium![n]拖动画面进行移动
:1@白色砖块是路面[n]深灰色砖块是墙体[n]红色砖块是可以解锁的闸门
:1,1#[n]未解锁的闸门无法通过[n]请寻找线索解开闸门[n]#ω
:1,1,1@ \n:1,1,1,1@ \n:1,1,1,1,3@ \n:0,0,1,3,3,3,3@ \n:0,0,1,3,3,3,2@ \n:0,0,1,3,3,3,1@
:3,1$[[unlock-progress]]解锁进度层
:3,2|游戏作者：Hqak(wxyhly)
:3@这是一个形式系统推理结合[n]双曲空间解谜小游戏[n]你将从命题逻辑开始逐步加入[n]更复杂的规则和公理
:2@前往上方绿色砖块[n]解锁推理层
:2,2$[[unlock-deduct]]解锁推理层
:2,1|点击推理规则a1[n]根据命令提示框[n]随便输入些什么试试
:2,3|点击推理规则a2[n]根据命令提示框[n]随便输入些什么试试

:2,2,2|#p闸门开启方法：[n]当推理层的定理列表中[n]包含闸门上的字符串时[n]才能通过闸门
:2,2,2,1|#d闸门开启方法：[n]当推理层的推理规则列表中[n]包含闸门上的字符串时[n]才能通过闸门
:2,2,1#[n]a>(a>a)[n]#p
:2,2,1,3@ 请向上走查看[n]推理提示
:2,2,1,3,2@ 尝试使用a2公理看看[n]a>((a>a)>a)[n]能推出什么
:2,2,3#[n](a>a)[n]#p
:2,2,3,1#[n](b>b)[n]#p
:2,2,2,3#[n]((a>b)>(a>b))[n]#p
:2,2,2,2$解锁使用$开头符号与推理宏
:2,2,2,2,1@点击计入规则按钮[n]定理列表中最后一行的定理[n]将被记录在推理规则中
:2,2,2,2,2|以$开头的符号[n]在推理规则中后[n]可以替换成任意的表达式
:2,2,2,2,3|推理宏只是将多次推理打包[n]严格说不算推理规则[n]你可以像用推理规则那样用推理宏
:2,2,2,2,1,3#[n]⊢($0>$0)[n]#d
:2,2,2,2,2,1@计入规则时[n]所有假设都将会被[n]录入推理规则内
:2,2,2,2,2,2$解锁假设推理
:3,1,3#这扇门无法从下方打开[n]只能从上面打开
:3,1,3,1$解开下方的门

:1,3#通过此门需消耗推理素5kg
:3,3$获取1µg推理素\n:2,2,1,1$获取2µg推理素\n:1,3,2$获取50kg推理素
:2,1,3@ 请向上走查看[n]推理规则的使用方法
:2,1,3,2@ “A,B ⊢ C”的含义为
:2,1,3,2,2@  若A、B都是定理[n]则C也是定理
:2,1,3,2,2,2@  推理规则中的美元符号$开头的符号[n]代表可替换成任意的合法表达式
:2,1,3,2,2,2,2@  若符号“⊢”前没有条件定理[n]则该推理规则是“公理”[n]公理都以字母“a”开头
:2,1,3,2,2,2,2,2|  其实除了mp，其它推理规则都是公理

:2,2,2,2,2,2,1#[n]$0⊢($1>$0)[n]#d
:2,2,2,2,2,2,1,1#[n]$0⊢($2>($1>$0))[n]#d
:2,2,2,2,2,2,1,1,1#[n]$0⊢($3>($2>($1>$0)))[n]#d

:2,1,3,2,1#[n](a>a)>(b>(c>(d>d)))[n]#p
:2,1,3,1,3@\n:2,1,3,1,2@\n:2,1,3,1,1@\n:2,1,3,1,1,1@
:2,2,2,2,2,2,3@
:2,2,2,2,2,2,1,3$获取1µg推理素
:2,2,2,2,2,2,1,1,3$获取1µg推理素
:2,2,2,2,2,2,1,1,1,3$获取1µg推理素

:3,3,1#前面的区域[n]以后再来探索吧？


:2,2,3,3#通过此门需消耗推理素5µg
:2,3,1,1$解锁否定公理a3[n]（即解锁全部命题逻辑公理）

`;