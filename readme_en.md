# Deductrium

A game that combines mathematical formal systems and hyperbolic space in the browser using Typescript. Currently includes propositional logic, first-order logic, Peano axioms, ZFC set theory, and some type theory.

Link: [wxyhly.github.io/deductrium](https://wxyhly.github.io/deductrium/)

## Deduct Layer Tutorial

### Command Input Box
The command input box is at the bottom. When prompted to enter a command, you can enter the content in the brackets of the buttons at the bottom of the proposition table to execute the command. The effect is the same as clicking the button. A command may be completed by entering it multiple times. If you want to exit halfway, please press the `Esc` key to execute other commands.

### Deduction
Rules in the deduction rule table \[D\] are all in this form:
`( A1, A2, ..An ⊢ C )`  
This means if conditions `A1`, `A2`, ..., `An` are all propositions in the \[P\] table, executing this rule will lead to add conclusion `C` to the proposition table. To execute a deduction rule, first ensure that there is no command being executed (if there is, press Esc to cancel it), then:  
- Enter the rule name  
- Or directly click the rule in \[D\] table with the mouse  

When executing a rule, the command prompt will ask you to specify which propositions in the \[P\] table correspond to conditions `A1`, `A2`, ..., `An`. You can directly select in the theorem table. Words starting with `$` in expressions are called replacement variables. You need to specify the value of the replacement variable before deduction. The system will automatically match replacement variables via conditional propositions; if undetermined, the player needs to enter the replacement content according to the prompt. The replacement content must be a legal expression. A legal expression can be a legal formula or a legal item.

### Well-Formed Formulas (WFF)
Well-formed formulas (WFF) are propositions whose truth can be determined. The simplest valid formulas (atomic formulas) are any words. Words must contain only lowercase letters, numbers, and `$`. Note that uppercase letters may be reserved by the system and are not recommended. 
WFFs can be combined into more complex WFFs using propositional logic connectives, such as `a > b`, `((1 @ 3) & ~a)`. Brackets are used to distinguish the priority of operators. See the symbol list below for details.

### Valid Terms
Valid terms represent concepts like sets, numbers, or set elements. words can be valid terms (atomic terms), but no word can be both a term and formula. Terms can be combined into complex terms using function symbols, such as `aU{b,c}`, `1+(2*(x+3))`; they can also form WFFs via predicate symbols, such as `1+1=2`, `x@{x,y}`.

### Common Symbol List  
|Input|Display|Usage|
|---|---|---|
|`>`|`→`|`$0 > $1`|
|`~`|`¬`|`~$0`|
|`\|`|`∨`|`$0 \| $1`|
|`&`|`∧`|`$0 & $1`|
|`<>`|`↔`|`$0 <> $1`|
|`V`|`∀`|`V$0:$1`|
|`E`|`∃`|`E$0:$1`|
|`@`|`∈`|`$0 @ $1`|
|`=`|`=`|`$0 = $1`|

### Quick Input
When the command input is waiting for a valid expression, hovering the mouse over propositions/rules in the table and clicking (or tapping on mobile) will automatically insert the highlighted content at the cursor. If text is selected in the command line, all instances of the selected text will be replaced with the highlighted content.

### Hypotheses and Macro Recording
Since propositions in the table are derived via deduction rules, it would be troublesome if many identical and complex deduction steps are involved. After unlocking the corresponding rule, you can click "Record Macro" to package all deduction steps in the proposition list into a single macro and add it to the \[D\] rule table for multiple use. It is recommended to use `$`-prefixed atomic expressions in propositions, which will upgrade specified words to replacement variables when recorded as deduction rules, allowing replacement with any expression.  

To record a macro with hypotheses, click the "Hypothesis" button to input hypotheses when the proposition list is empty, then proceed with deduction and macro recording.

### Metarules
Similar to rules deriving propositions, metarules derive deduction rules with similar operation methods. All metarules are provided by the system and unlocked gradually in-game; The specific usage of each metarule can be found in the in-game instructions. Many metarules have "[]" symbols in front of their names, and the letters in them can be used to quickly generate and use these meta-rules.

### Assertion Mechanism
In first-order logic, replacement variables often require restrictions like "free occurrence" or "substitutability". Since `$`-prefixed expressions may be arbitrarily replaced when recorded as macros, conditions like "free occurrence" or "substitutability" in the expressions are temporarily undetermined. The system uses assertion functions like `#nf` and `#rp` to mark them, with fuzzy logic processing. When `$`-prefixed expressions are later substituted with specific values, the system checks if these values satisfy the assertions. If assertions are successfully verified, the corresponding assertion functions will be removed.


## Type Layer Tutorial
The Type Layer lists known unlocked types and other expressions in the "Axiom Types" list. Unlike the Deduct Layer, these are not executable but for reference only. To derive propositions, directly input expressions in the proposition list; the system will automatically recognize and check the validity of your proof evidence. Note: in type layer, mechanism is completely different: 1. the Type Layer prohibits all undefined free variables(Also recommend to use lowercase letters for bound variables); 2. The universal matcher (`$`) mechanism is no longer available.

There is a special "defined equality" mechanism in the type layer, that is, if two expressions are defined to be equal, the system will not distinguish them anywhere. Another similar concept is propositional equality. Propositional equality (eq) is similar to the equality predicate in first-order logic, but is just a proposition.

### Common Symbol List  
|Input|Display|Usage|
|---|---|---|
|`->`|`→`|`x -> y`|
|`L`|`λ`|`Lx:a,b`|
|`P`|`Π`|`Px:a,b`|
|`S`|`Σ`|`Sx:a,b`|
|`X`|`×`|`aXb`|

## Proof Assistant
Manually constructing proof evidence (i.e., values of corresponding types) for complex propositions is challenging. The Proof Assistant can automate some tasks: First, enter the proposition to be proved in the proposition list, then click the plus button in proof strategies and select the proposition. The Proof Assistant will guide you to complete the construction of the value of the target type.