# 472-project

## Motivation

The book “The Little Typer” introduces the concept of dependent types as a means of writing
programs that double as proofs for claims in intuitionistic logic. Dependent types are types
whose definition depends on values. This enables the programmer to define the semantics of
their program more expressively. The concept of programs as proofs is known as Curry-Howard
Isomorphism, and several types of lambda calculi have been derived to expand the domain of
proofs that one can program. A particularly interesting calculi is the lambda-mu calculus,
first introduced by M. Parigot (https://doi.org/10.2307/2275652). This is an extension to the 
lambda calculus which enables the programmer to “freeze” sub-terms to be later abstracted on. 
Programmatically, this translates to implementing continuation based control flow operators one 
could find in functional languages. Proof-theoretically, this would expand the logic system of 
Tartlet to allow proofs to be written in classical logic.

## Lambda-Mu Calculus

The type system of the lambda-mu calculus is described by five rules:

![Screenshot from 2023-08-08 19-03-46](https://github.com/Patrick-Yevych/492-project/assets/6632555/3eac4483-8c57-4fc3-b1a7-197086d3c5b4)

The first three rules are the same as simply typed lambda calculus (variable introduction, abstraction, and application) whereas the last two rules are known as naming rules. An unnamed term is a traditional expression in lambda calculus.

Lambda-Mu Calculus introduces the concept of mu (μ) variables, which exist in the delta (Δ) context; seperate from that of the lambda variables. Δ is a map of μ variables to named terms. A named terms can be interpreted as second class continuations; a unary function describing the subsequent steps of computation the interpreter must follow.

The first naming rule describes function application of some α ∈ Δ of type (→ A Absurd) on an unnamed term M of type A. The second naming rule describes the mu abstraction μα.c . The computational interpretation of a mu abstraction is to capture/name the current continuation and then evaluate the expression c. If at any point during the evaluation of c, α is applied to to some sub-expression M, then the result of the function application (α M) is the value of the mu abstraction.

## Scope

The objective of this project is to attempt to implement the lambda-mu calculus typing and evaluation
semantics in the interpreter of Tartlet, explore the possible use-cases of extending the langauge in
such a way, and how it interacts with the dependent type system.

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
names the term (+ 42 _) to the mu variable k, and evaluate the expression C with k now in Δ. Built-in **Jmp** provides function application of the mu variables to some sub-expression M in expression C. Again, when evaluating C, if `(Jmp k M)` is encountered, then the result of this function application is the result of evaluating the above expression.
