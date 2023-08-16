# 492-project

## Goal

The goal of this project is to enable Tartlet to prove classical logic theorems. In order
to achieve that, this repository extends Tartlet with continuations. The user will be 
able to manipulate continuations using three new added operations: Shift, Clear and Jump. 
The addition of these operations enables one to prove classical logic theorems using Tartlet.

## Motivation

The book “The Little Typer” introduces the concept of dependent types as a means of writing
programs that double as proofs for claims in intuitionistic logic. Dependent types are types
whose definition depends on values. The programming language Pie supports dependent types,
and is used to introduce the concept itself in “The Little Typer”. Tartlet is a stripped 
down, simplified version of Pie which is also dependently typed.

The concept of programs as proofs is known as the Curry-Howard Isomorphism, and several types 
of lambda calculi have been derived to expand the domain of proofs that one can program. 

A particularly interesting calculi is the lambda-mu calculus, first introduced by 
M. Parigot (https://doi.org/10.2307/2275652). This is an extension to the lambda calculus
which enables the programmer to bind arbitrary sub-expressions to variables. Programmatically, 
this translates to implementing continuation based control flow operators one could find in 
functional languages. Proof-wise, this would expand the logic system of Tartlet to allow proofs 
to be written in classical logic.

## Continuations

A continuation can be thought of as the context of an expression. It is easiest explained with
examples. Consider the following Racket-like expression:

(+ ((lambda x (+ x 1)) 2) 5)

For each sub-expression above, we identify the continuation by substituting the sub-expression 
with an underscore like so:

Continuation of 2: (+ ((lambda x (+ x 1)) _) 5)

Continuation of ((lambda x (+ x 1)) 2): (+ _ 5)

Continuation of (lambda x (+ x 1)): (+ ( _ 2) 5)

This yields us a context which can easily be adapted into a function, by treating the underscore
as a parameter. For instance, the continuation of ((lambda x (+ x 1)) 2) can be turned into the 
following function by turning the underscore into a free variable:

(lambda n (+ n 5))

Intuitively, the continuation of an expression is everything "outside" of the expression itself.

Typically, when manipulating continuations, a new operation called shift is added. For any expression 
(shift k body), the continuation of the shift expression is bound to k as a function, and the body 
is evaluated (without evaluating the continuation). Here are some examples:

(+ (shift k (+ 1 1)) 10) = (+ 1 1) = 2

(+ (shift k (+ 1 (k 5))) 4) = (+ 1 (k 5)) = (+ 1 ((lambda x (+ x 4)) 5))

(+ (shift k (k (+ 2 2))) 4) = ((lambda x (+ x 4)) (+ 2 2))

Additional resources on continuations: https://docs.racket-lang.org/guide/conts.html

## Lambda-Mu Calculus

The type system of the lambda-mu calculus is described by five rules:

![type.png](type.png) 

as seen in https://www.pls-lab.org/en/Lambda_mu_calculus.

The first three rules are the same as simply typed lambda calculus (variable introduction, abstraction, and application) whereas the last two rules are known as naming rules. An unnamed term is an expression in lambda calculus.

Lambda-Mu Calculus introduces the concept of mu (μ) variables, which exist in the delta (Δ) context; seperate from that of the lambda variables. Δ is a map of μ variables to named terms. A named terms can be interpreted as a second class continuation; a unary function describing the subsequent steps of computation the interpreter must follow.

The first naming rule describes function application of some α ∈ Δ of type (→ A Absurd) on an unnamed term M of type A. The second naming rule describes the mu abstraction μα.c . The computational interpretation of a mu abstraction is to capture/name the current continuation and then evaluate the expression c. If at any point during the evaluation of c, α is applied to some sub-expression M, then the result of the function application (α M) is the value of the mu abstraction.

## Scope

The objective of this project is to attempt to implement the lambda-mu calculus typing and evaluation
semantics in the interpreter of Tartlet, explore the possible use-cases of extending the language in
such a way, and how it interacts with the dependent type system.

## Added operations

Three new operations are added to Tartlett: Shift, Jump and Clear.

The shift operation works similarly to the shift described in the continuations section. The syntax of 
a shift expression is as follows:

(shift)



### Writing the Evaluator

The implementation of the lambda-mu calculus requires the evaluator to be re-written in
continuation passing style, and with the following signature:
```
eval :: Env -> Dlt -> Expr -> IR -> Value
```
Where `IR` is the type `Value -> Value`, the current continuation of the program. This will be the Intermediate Representation that the interpreter uses to represent the state of evaluation, and the structure of the program. The set of mu variables are stored within context object `Dlt` (Δ), which is passed into the evaluator as an argument similar to Env.  

We then implement built-ins **Clr** and **Shf** in Tartlet which can be used to delimit and name the current continuation into the specified mu variable. So, the expression:
```
  (Clr
      (+ 42
          (Shf k C)))
```
names the term (+ 42 _) to the mu variable k, and evaluate the expression C with k now in Δ. Built-in **Jmp** provides function application of the mu variables to some sub-expression M in expression C. Again, when evaluating C, if `(Jmp k M)` is encountered, then the result of this function application is the result of evaluating the above expression. If `(Jmp k M)` is not encountered, then the result of the evaluating the above expression is the evaluation of (+ 42 C).

### Type checking

The type of the Clr/Shf/Jmp construct and call/cc is precisely Peirce’s Law under Curry-Howard Isomorphism.

![type1.png](type1.png)

Type checking Clr/Shf/Jmp requires helper functions to extract the continuation delimited between Clr and Shf, as well as the expression thrown to the mu variable in a Jmp call.
These expressions are then type checked against the components of Peirce’s law. The type of the continuation must be (→ X Y) while the type of the expression thrown to the mu variable must be X.
Since the existing continuation within Shf is discarded upon calling Jmp, the type Y is never used, and may be taken to be the Absurd type (⊥). Regardless, the type of the shift body must be X should Jmp not be present. 

## Grammar

The grammar for our language is as follows:

```
<expr> ::= <core>
          | 'Clr' <cont>

<cont> ::= <cont>
          | <core>
          | 'Shf' <mu> <abstr>

<abstr> ::= <abstr>
          | <core>
          | 'Jmp' <mu> <core>

<mu> = ([a-z] | [A-Z]) ([1-9] | [a-z] | [A-Z])+
```
where `<core>` is any expression in core Tartlet.

## Code Organization

Source files can be found under [/src](/src). 
  
  - [Eval.hs](/src/Eval.hs) is the evaluator,
  - [Lang.hs](/src/Lang.hs) contains the language specification amongst other data types such as contexts, environments, messages, etc.
  - [Norm.hs](/src/Norm.hs) contains the alpha equivalance checker and readback functions,
  - [Parse.hs](/src/Parse.hs) contains the parser and desugarers,
  - [Top.hs](/src/Top.hs) contains the top-level function,
  - [Type.hs](/src/Type.hs) contains the type synthesizer and checker.

[/app/Main.hs](/app/Main.hs) allows the cabal project to be compiled and ran.

## References

[1] Leroy, X. (n.d.). Programming = proving? The Curry-Howard correspondence today Fourth lecture You’ve got to decide one way or the other! Classical logic, continuations, and control operators. Retrieved July 21, 2023, from https://xavierleroy.org/CdF/2018-2019/4.pdf

[2] Michel Parigot (1992). λμ-Calculus: An algorithmic interpretation of classical natural deduction. Lecture Notes in Computer Science. Vol. 624. pp. 190–201. doi:10.1007/BFb0013061. ISBN 3-540-55727-X.

[‌3] Wikibooks. (n.d.). En.wikibooks.org. https://en.wikibooks.org/wiki Write_Yourself_a_Scheme_in_48_Hours/Parsing

[4] Christiansen, D. (2019). Checking Dependent Types with Normalization by Evaluation: A Tutorial (Haskell Version). https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf

