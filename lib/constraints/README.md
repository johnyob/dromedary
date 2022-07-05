# Constraints

This library provides the core concept of this type checker, *constraints*. 

This document will discuss the design decisions of the library and the corresponding theory.  

## Syntax

To discuss constraints, we first must define their syntax. We also 
define some notions about structure of types and type schemes. 

```ocaml
cst, C ::= 
        (* first order constraints *)
        | ⊥ | ⊤ | τ = τ | C && C | ∃ ɑ. C | ∀ ɑ. C
        (* environmental constraints *)
        | def x : τ in C | def x : σ in C
        | x <= τ | σ <= τ
    
types, τ ::= ɑ | (τ, ..., τ) F | ...

schemes, σ ::= ∀ ɑ ... ɑ. C => τ
```
where `F` is a type former (e.g. `unit`, `option`, etc)

Constraints are split into two main forms: a subset of first-order logic with equality (first-order constraints) and constraints that define the environment (so-called environmental constraints). 

The `def` and `<=` constraints are for environment construction and access. The
`def` form is an explicit substitution as is interpreted using the following equivalence law: 
```ocaml
def x : σ in C ≃ {σ\x}C
```

`<=` is the instantiation constraint. `σ <= τ` is interpreted as "`τ` is an instance of `σ`": 
```ocaml
(∀ ɑ₁ ... ɑₙ. C => τ₁) <= τ₂ ≃ ∃ ɑ₁ ... ɑₙ. C && τ₁ = τ₂ 
```

We assume standard notions of `ɑ`-equivalence and free variables. 

*Note*: Our implementation uses a larger constraint language. Additional
constructs are "derived" from this axiomiatic system. See *Syntactic Sugar*.


## Semantics

Let `t` be a meta-variable for *ground types*, the Herbrand universe of τ: 
```ocaml
ground types, t ::= (t, ..., t) F | ...
```

A ground assignment `ɸ : ɑ ⇀ t` is a partial function from type variables to ground types. An environment `ρ : x ⇀ P(t)` is a partial function from 
term variables to sets of ground types (these can be thought of as the inhabitants of a type scheme). 

The semantics of constraints is expressed inductively `ρ; ɸ ⊢ C`, read as:
"In the environment `ρ` and assignment `ɸ`, `C` is true":
```ocaml
(* first-order constraints *)

---------- (true)
 ρ; ɸ ⊢ ⊤


  ɸ(τ₁) = ɸ(τ₂)
---------------- (equal)
 ρ; ɸ ⊢ τ₁ = τ₂


 ρ; ɸ ⊢ C₁   ρ; ɸ ⊢ C₂
----------------------- (and)
    ρ; ɸ ⊢ C₁ && C₂


 ρ; ɸ, ɑ -> t ⊢ C
------------------ (exists)
  ρ; ɸ ⊢ ∃ ɑ. C


 ∀ t   ρ; ɸ, ɑ -> t ⊢ C
------------------------ (forall)
     ρ; ɸ ⊢ ∀ ɑ. C


(* environmental constraints *)

  ρ, x -> {τ}; ɸ ⊢ C
----------------------- (def-mono)
 ρ; ɸ ⊢ def x : τ in C


  ρ, x -> ⟦σ⟧(ρ, ɸ) ; ɸ ⊢ C
---------------------------- (def-poly)
   ρ; ɸ ⊢ def x : σ in C

  
  ρ(x) ∋ ɸ(τ) 
--------------- (inst-var)
 ρ; ɸ ⊢ x <= τ


 ⟦σ⟧(ρ, ɸ) ∋ ɸ(τ) 
----------------- (inst-sch)
  ρ; ɸ ⊢ σ <= τ

```
where `⟦_⟧(_,_)` is the interpretation of the scheme `∀ ɑ ... ɑ. C => τ` under `ρ, ɸ` is the set: 
```ocaml
⟦ ∀ ɑ. C => τ ⟧( ρ , ɸ ) = { ζ(τ) : ɸ =\ɑ ζ && ρ; ζ ⊢ C }
```

**Entailment and Equivalence**: `C₁ ⊨ C₂` is defined as: 
```ocaml
∀ ρ ɸ. ρ; ɸ ⊢ C₁ => ρ; ɸ ⊢ C₂
```
`C₁ ≃ C₂` iff `C₁ ⊨ C₂` and `C₂ ⊨ C₁`.

## Theorems and Equivalence Laws

A constraint `C` *determines* `ɑ` iff 
```ocaml
∀ ρ ɸ₁ ɸ₂. ρ; ɸ₁ ⊢ C && ρ; ɸ₂ ⊢ C && ɸ₁ =\ɑ ɸ₂ => ɸ₁(ɑ) = ɸ₂(ɑ)
```
Various theorems and equivalences laws used throughout our formalization:
```ocaml
(* Congruence Law *)

ℂ ::= [] | C | ℂ && ℂ | ∃ ɑ. ℂ | ∀ ɑ. ℂ
    | def x : σ in ℂ | def x : ∀ ɑ. ℂ => τ in C

C₁ ⊨ C₂ => ℂ[C₁] ⊨ ℂ[C₂]

(* Equivalence Laws *)

(* ⊤-unit *)
⊤ && C ≃ C

(* ⊥-unit *)
⊥ && C ≃ ⊥

(* =-refl *)
⊤ ≃ τ = τ

(* =-sym *)
τ₁ = τ₂ ≃ τ₂ = τ₁

(* =-trans *)
τ₁ = τ₂ && τ₂ = τ₃ ≃ τ₁ = τ₃

(* =-sub *)
ɑ = τ && C ≃ a = τ && {τ\ɑ} C

(* and-comm *)
C₁ && C₂ ≃ C₂ && C₁ 

(* and-assoc *)
C₁ && (C₂ && C₃) ≃ (C₁ && C₂) && C₃ 

(* and-simp *)
C₁ && C₂ ≃ C₁                                           if C₁ ⊨ C₂

(* exist-exist *)
∃ ɑ. ∃ β. C ≃ ∃ ɑ β. C

(* exist-and *)
(∃ ɑ. C₁) && C₂ ≃ ∃ ɑ. C₁ && C₂                         if ɑ # C₂

(* exist-simp *)
∃ ɑ. C ≃ C                                              if ɑ # C

(* all-all *)
∀ ɑ. ∀ β. C ≃ ∀ ɑ β. C

(* all-and *)
(∀ ɑ. C₁) && C₂ ≃ ∀ ɑ. C₁ && C₂                         if ɑ # C₂

(* all-simp *)
∀ ɑ. C ≃ C                                              if ɑ # C

(* all-exists *)
∃ ɑ. ∀ β. C ≃ ∀ β. ∃ ɑ. C                               if ∃ β. C determines ɑ

(* def-sub *)
def x : σ in ℂ[x <= τ] ≃ def x : σ in ℂ[σ <= τ]         if no capture

(* def-simp *)
def x : σ in C ≃ C                                      if x # C

(* def-and-1 *)
def x : σ in C₁ && C₂ 
  ≃ (def x : σ in C₁) && (def x : σ in C₂)

(* def-and-2 *)
def x : σ in C₁ && C₂                                   if x # C₂
  ≃ (def x : σ in C₁) && C₂

(* <=-mono-refl *)
τ₁ = τ₂ ≃ τ₁ <= τ₂

(* <=-trans *)
∃ β. σ <= β <= τ ≃ σ <= τ                               if β # σ, τ

(* sch-all-exist *)
∀ ɑ. (∃ β. C) => τ ≃ ∀ ɑ β. C => τ
```


## Syntactic Sugar 

Notice that the `def` form is equivalent to `C` if `x # C` (by `def-simp`). 
Thus `x` could bind an unsolvable scheme `σ`. We use a `let` form to enforce satisfiability of `σ`: 
```ocaml
let x : ∀ ɑ... ∃ β... C₁ => τ in C₂
  = ∀ ɑ... ∃ β... .C₁ && def x :  ∀ ɑ... β... C₁ => τ in C₂ 
```

The `let` form binds "rigid" and "flexible" variables (see ??) while checking `C₁` is satisfiable. 

A recursive construct is also useful for checking fixed-points: 
```ocaml
let rec x : ∀ ɑ... ∃ β... C₁ => τ in C₂
  = let x : ∀ ɑ... ∃ β... (def x : τ in C₁) => τ in C₂
```

These "derived" forms allow us to specify less rules in our formalization
and get the rules for `let` and `let rec` (etc) for "free". 

# Implementation (Theory)

For constraint solving, we split our solver into first-order unification
and a solver that re-writes constraints into unification problems.

## Unification

We characterise unification using "unificands". For efficiency, we use a 
multi-equational approach. 

A multi-equation `E` is a set of monotypes: `E ∈ P(τ). |E| >= 2` with the interpretation: 
```ocaml
 ∀ τ ∈ E     ɸ(τ) = t
---------------------- (multi-equal)
       ρ; ɸ ⊢ E
```

A unificand `U` is defined by: 
```ocaml
 U ::= ⊥ | ⊤ | E | U && U | ∃ ɑ. U
```
Contexts are given by: 
```ocaml
 𝕌 ::= [] | 𝕌 && U | U && 𝕌 | ∃ ɑ. 𝕌
```
General approach to solving: Pull out existential quantifiers using `(* exist-and *)` (prenex normal-form), replace concrete types w/ variables
(required to get normal forms + O(1) equivalence check),
then solve multi-equations.

The solver is expressed as re-writing rules `U ~> U'` that preserve equivalence: `U ≃ U'`. 
```ocaml
(* ⊤-simp *)

U && ⊤ ~> U

(* uni-exist *)

(∃ ɑ. U₁) && U₂ ~> ∃ ɑ. U₁ && U₂                          if ɑ # U₂

(* uni-var *)

(τ₁, ..., τᵢ, ..., τₙ) F = E                              if τ
  ~> ∃ ɑ. (ɑ = τᵢ && (τ₁, ..., ɑ, ..., τₙ) F = E)

(* uni-unify-1 *)

ɑ = E₁ && ɑ = E₂ ~> ɑ = E₁ = E₂                           

(* uni-unify-2 *)

(ɑ₁, ..., ɑₙ) F = (τ₁, ..., τₙ) F = E 
  ~> ɑᵢ = τᵢ && (τ₁, ..., τₙ) F = E      

(* uni-unify-3 *)

(τ, ..., τ) F' = (τ, ..., τ) F = E ~> ⊥                   if F' <> F

(* uni-occurs-check *)

U ~> ⊥                                                    if U contains a cycle

(* uni-false *)

𝕌[⊥] ~> ⊥

```

Various other rules are admissible e.g. path compression or garbage collection on un-used variables.

## Solving

Solving is expressed as a constraint re-writing system that translates
richer constraints `C` into unificands `U`, then solves them. 

We do so using contexts (or "stacks"): 
```ocaml
(* frames *)
F ::= [] && C | ∃ ɑ. [] | ∀ ɑ. [] | def x : σ in []

(* stacks *)
S ::= [] | F[S]
```

The states of our re-writing system are given by: `(S, U, C)`, where `S` is the current stack, `U` is the current unificand, and `C` is the remaining constraint to be translated. 

```ocaml
(* unify *)

(S, U, C) --> (S, U', C)                                if U ~> U'

(* existential *)

(S, ∃ ɑ. U, C) --> (S[∃ ɑ. []], U, C)


(S[(∃ ɑ. []) && C], U, C') 
  --> (S[∃ ɑ. [] && C], U, C')


(S[∃ ɑ. ∃ β. []], U, C) --> (S[∃ ɑ β. []], U, C)


(S[def x : σ in ∃ ɑ. []], U, C)                         if ɑ # σ
  --> (S[∃ ɑ. def x : σ in []], U, C)


(* ∀ ɑ. ∃ β Ɣ is the env *)
(S[∀ ɑ. ∃ β Ɣ []], U, ⊤)                                if ∃ ɑ Ɣ. U determines β
  --> (S[∃ β. ∀ ɑ. ∃ Ɣ. []], U, ⊤)

(* constraint reduction *)

(S, U, τ₁ = τ₂) --> (S, U && τ₁ = τ₂, ⊤)


(S, U, x <= τ) --> (S, U, lookup S x <= τ)


(S, U, ∀ ɑ. C => τ₁ <= τ₂) 
  --> (S, U, ∃ ɑ. C && τ₁ = τ₂)


(S, U, C₁ && C₂) --> (S[[] && C₂], U, C₁)


(S, U, ∃ ɑ. C) --> (S[∃ ɑ. []], U, C)


(S, U, ∀ ɑ. C) --> (S[∀ ɑ. []], U, C)

(* δ reductions *)

(S[[] && C], U, ⊤) --> (S, U, C)


(S[def x : σ in []], U, ⊤) --> (S, U, ⊤)


(S[∀ ɑ. ∃ β. []], U₁ && U₂, ⊤) --> (S, U₁, ⊤)         if ɑβ # U₁ 
                                                      && ∃ β. U₂ ≃ ⊤   

(* rigid variables *)

(* Unifying a rigid variable ɑ with a free var Ɣ
   => Ɣ determines ɑ *)
(S[∀ ɑ. ∃ β. []], U, ⊤) --> fail                      if ɑ <=[U] Ɣ
                                                      && Ɣ ∈ ɑ β

(* Unifying a rigid variable w a non-variable 
   term  *)
(S[∀ ɑ. ∃ β. []], ɑ = τ = E && U, ⊤) --> fail         if not (τ = ɑ 
                                                      || τ = flexible β)
```

# Graphic Types

See goodnotes. 


# Implementation (Design)

