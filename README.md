# noocleus-one

"noocleus-one" is meant to be a minimal example for a functional programming language where type inference meets algebraic data types and pattern matching. 

I've developed this project to understand the mechanics of type inference in the presence of algebraic data types, pattern matching and recursive let-expressions. The "one" of "noocleus-one" stands for "rank-1 polymormphism" since I intend to apply the ideas of this project to higher-rank polymorphism. The name "noocleus" itself is a pun on my own language called "noo" (which is still under construction), since this project is somewhat of a small kernel for "noo".

## Index

1. [Terms](#1-Terms)
    1. [Extended Backus-Naur-Form](#11-Extended-Backus-Naur-Form)
    2. [Examples](#12-Examples)
        1. [Booleans](#121-Booleans)
        2. [Natural Numbers](#122-Natural-Numbers)
        3. [Options](#123-Options)
        4. [Lists](#124-Lists)
        5. [Eithers](#125-Eithers)
2. [Types](#2-Types)
    1. [Sigma and Tau Types](#21-Sigma-and-Tau-Types)
        1. [Sigma Types](#211-Sigma-Types)
        2. [Tau Types](#212-Tau-Types)
3. [References](#3-References)

### 1. Terms

#### 1.1 Extended Backus-Naur-Form
```
Term                ::= Let | Data | Abstraction ;

Let                 ::= "let", Annotation, "=", Term, "in", Term ;

Data                ::= "data", TypeConstant, { TypeVariable }, [ "=", Constructors ], "in", Term ;
Constructors        ::= Constructor, { "|", Constructor } ;
Constructor         ::= UpperCaseIdentifier, { SimpleType } ;

Abstraction         ::= Match, [ "=>", Term ] ;

Match               ::= Annotation, [ "match", "{", { Case }, "}" ] ;
Case                ::= "case", Annotation, "=>", Term ;

Annotation          ::= Application, [ ":", Tau ] ;

Application         ::= SimpleTerm, { SimpleTerm } ;

SimpleTerm          ::= Natural | Tuple | Variable ;

Natural             ::= "[0-9]+" ;

Tuple               ::= "(", [ Term, { ",", Term } ], ")" ;

Variable            ::= Identifier ;

Tau                 ::= FunctionType ;

FunctionType        ::= TypeApplication, [ "->", Tau ] ;

TypeApplication     ::= SimpleType, { SimpleType } ;

SimpleType          ::= TupleType | TypeConstant | TypeVariable ;

TupleType           ::= "(", [ Tau, { ",", Tau } ], ")" ;

TypeConstant        ::= UpperCaseIdentifier ;

TypeVariable        ::= Identifier ;

(* note: an upper case identifier may not match any terminal-symbol of this grammar *)
UpperCaseIdentifier ::= "[A-Z][a-zA-Z0-9]*'*" ;

(* note: an identifier may not match any terminal-symbol of this grammar *)
Identifier          ::= "[a-zA-Z][a-zA-Z0-9]*'*" | Symbol, { Symbol } ;

Symbol              ::= "+" | "~" | "*" | "#" | "-" | "." | ":" 
                      | "," | ";" | "<" | ">" | "|" | "@" | "^" 
                      | "!" | "$" | "%" | "&" | "/" | "?" ; 
```

#### 1.2 Examples

##### 1.2.1 Booleans
```
data Boolean = True | False in

let if = test => then => else => test match {
  case True  => then
  case False => else
} in

let negate = boolean => if boolean False True in

negate True
```

##### 1.2.2 Natural Numbers
```
data Nat = S Nat | Z in

let + = a => b => a match {
  case Z   => b
  case S n => + n (S b)
} in

let - = a => b => (a, b) match {
  case (a, Z)     => a
  case (Z, b)     => Z
  case (S a, S b) => - a b
} in

let * = a => b => a match {
  case S Z => b
  case Z   => Z
  case S n => + (* n b) b
} in

let > = a => b => (a, b) match {
  case (Z, Z)     => False
  case (a, Z)     => True
  case (S a, S b) => > a b
} in

let factorial = n =>
  if (> n Z)
    (* (factorial (- n (S Z))) n)
    (S Z)
in 

factorial 5
```

##### 1.2.3 Options
```
data Option a = Some a | None in

let map = f => option => option match {
  case Some value => Some (f value)
  case None       => None
} in

let flatMap = f => option => option match {
  case Some value => f value
  case None       => None
} in

flatMap (n => map (n => + n n) (Some n)) (Some 10)
```

##### 1.2.4 Lists
```
data List a = Cons a (List a) | Nil in

let reverse = xs => 
  let helper = xs => acc => xs match {
    case Cons head tail => helper tail (Cons head acc)
    case Nil            => acc
  } in helper xs Nil
in

let fold = z => f => xs => xs match {
  case Cons head tail => fold (f z head) f tail
  case Nil            => z
} in

fold 0 + (Cons 0 (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))))))
```

##### 1.2.5 Eithers
```
data Either a b = Left a | Right b in

let either = f => g => e => e match {
  case Left a  => f a
  case Right b => g b
} in

either (+ 1) (- 1) (Right 1)
```

### 2. Types

The type inference used in this project is that of [Hindley-Milner](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) (sometimes also called Damas-Milner). That means types can be completely (i.e. without user supplied hints) inferred. The algorithm itself is somewhat of a combination of the [algorithm J](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_J) and the one of [S. P. Jones, et al.](#3-References) for arbitrary-rank types. I have extended it by algebraic data types and pattern matching on my own, meaning that a formal proof for the correctness of those features is missing.

#### 2.1 Sigma and Tau Types

The types of the underlying type system are divided into monomorphic (also called tau types) and polymorphic (also called sigma types) types. 

##### 2.1.1 Sigma Types

A sigma (or polymorphic) type is quantified by an universal quantifier. For example, `forall x . x -> x` is the type of the polymorphic identity function. The implemented algorithm always yields a sigma type as the result of the type inference.

##### 2.1.2 Tau Types

A tau (or monomorphic) type is one without an universal quantifier. For example, `Nat` is the (monomorphic) type of a natural number. A tau type may also be interpreted as a sigma type, i.e. `Nat` may also be interpreted as `forall . Nat`. In this case we quantify over the type `Nat` without specifying type variables at all.

In case of an annotation (e.g. `let f: a -> a = x => x in f`) free type variables (in the preceding example only `a`) are assumed to be quantified by a top-level `forall`.

While type checking the algorithm switches between sigma and tau types (depending on the scope) by instantiating and generalizing them. For further explanation consider the previous example `let f: a -> a = x => x in f`. While checking the equation (`f: a -> a = x => x`) we talk about `a -> a` as a monomorphic (tau) type, because we do not know anything about `x` on the right hand side, besides that it is of type `a`. When checking the body of the `let`-expression (i.e. the part to the right of `in`) we talk about `a -> a` as a polymorphic (sigma) type (as already mentioned, we assume that the free type variables are quantified by a `forall`), since we can call `f` for any value of any type.

#### 2.2 Limitations

There are two main limitations of the implemented algorithm: On the one hand, I have introduced recursive `let`-expressions which leads to a type system whose logic is not consistent. On the other hand, the type system disallows universal quantifiers at arbitrary positions.

##### 2.2.1 Consistency

When interpreting the types of the presented type system as logical formulas (see [Curry-Howard Isomorphism](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)) we can deduce the absurdity from something that is true (exploiting recursion).

Consider the following definitions for bottom (absurdity) and top:
```
data False    in
data True = T in
...
```

Since we always want to be able to deduce `True` there is exactly one constructor (namely `T`) that takes no arguments. The other way round, we never want to deduce the absurdity. For this reason there is no constructor for `False` at all. Unfortunately we can still deduce `False` when we introduce recursion:

```
data False    in
data True = T in

let f: True -> False in n => f n in

(f T): False
```

The program above is well-typed in the sense of the implemented algorithm, i.e. the type checker will not complain about anything. The result of the program is a value of type `False`. In terms of the Curry-Howard isomorphism, we have found a proof for the absurdity.

##### 2.2.2 Rank-N Polymorphism

As mentioned before, the "one" of "noocleus-one" stands for rank-1 polymorphism. An intentional limitation of this project is that it is not possible to type programs like the following:

```
let id = x => x in 
let map = f => (f 1, f ()) in map id
```

In a more powerful type system the program above would lead to a type, where `f` is polymorphic in the body of the abstraction `f => (f 1, f ())`, i.e. `map: (forall x . x -> x) -> (Nat, ())`. In the present project, this program is ill-typed: The type checker would complain with an error message like "type mismatch between 'Nat' and '()'", since it assumes that `f` is monormphic (i.e. either accepts `Nat` or `()` but not both).

#### 3. References

1. Pratical type inference for arbitrary-rank types, S. P. Jones, et al., 31.07.2007

