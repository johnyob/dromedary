# Dromedary's Type System

This library provides the fundamental aspect of this project, the type system.

In this document, we formally describe dromedary's syntax and type systems. 
We note that Dromedary has several type systems, which will all be documented,
showing the "narrative" of development for this project. 

This document will not explain any design decisions, see ??. 

#

## Syntax

Dromedary's syntax is formally defined by the following grammar:

```ocaml
constants             const ::= n ∈ ℕ | ()

primitives            prim ::= (+) | (-) | (x) | (/)

expressions           exp, e ::= 
                        | x 
                        | const | prim 
                        | fun p -> e | e₁ e₂
                        | let bs in e | let rec bs in e
                        | forall ɑ₁ .. ɑₙ -> e | exists ɑ₁ .. ɑₙ -> e | (e : τ)
                        | { l₁ = e₁ ; .. ; lₙ = eₙ } | e.l
                        | (e₁, .., eₙ) | K | K e
                        | match e with hs

bindings              b ::= p = e
                      bs ::= b₁ and .. and bₙ

patterns              pat, p ::= 
                        | _ | x 
                        | const
                        | (p₁, .., pₙ) | K | K p
                        | (p : τ) 

handlers              h ::= p -> e
                      hs ::= (h₁ | .. | hₙ)

types                 τ ::= 
                        | ɑ | τ₁ -> τ₂ 
                        | τ₁ x .. x τₙ 
                        | (τ₁, .., τₙ) F

type variables        ɑ ::= ..
expression variables  x ::= ..
type formers          F ::= int | ..
```


TODO: Define structures, type decls, etc (orthogonal to the issues we attempt to solve, but nonetheless, useful).

#

## Procaml

Procaml is the name of the type system that consists of a Core ML type system 
using constraints. 

The name procaml comes from procamelus, an extinct genus of camel. 

### Procaml Constraints

Procaml constraints are defined by: 
```ocaml
constraints     cst, C ::= 
                  (* first order constraints *)
                  | ⊥ | ⊤ | τ = τ | C && C | ∃ ɑ. C | ∀ ɑ. C
                  (* environmental constraints *)
                  | def Γ in C | x <= τ | σ <= τ
                  | let Γ in C | let rec Γ in C

types           τ ::= ɑ | (τ, .., τ) F | ..

schemes         σ ::= ∀ ɑ .. ɑ. C => τ

contexts        Γ ::= . | Γ, x : σ
```

Semantics of constraints are standard. See `constraints/README.md` for more details. 

### Procaml Environments, Constructors and Labels

Procaml programs are defined in a context of type declarations:
```ocaml
type declaration          type_decl ::= type type_desc₁ and .. and type_descₙ

type descriptions         type_desc ::= (ɑ₁, .., ɑₙ) F = type_desc_rhs
                          type_desc_rhs ::= record_desc | constructor_descs

record description        record_desc ::= { l₁ : τ₁ ; .. ; lₙ : τₙ }

constructor description   constr_descs ::= constr_desc₁ | .. | constr_descₙ
                          constr_desc ::= K | K of τ
```

The interpretation of this context Ω is *abstractly* defined by a set of judgements: 
```ocaml
Ω ⊢ F { l₁ ; .. ; lₙ } 
  = "In Ω, former F is a record type w labels l₁, .., lₙ"

Ω ⊢ F ( K₁ | .. | Kₙ ) 
  = "In Ω, former F is a variant type w constructors K₁, .., Kₙ"

Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. (ɑ₁, .., ɑₙ) F
  = "In Ω, constructor K is a constant constructor for type former F"

Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. τ -> (ɑ₁, .., ɑₙ) F
  = "In Ω, constructor K is a constructor w argument type τ for type former F"

Ω ⊢ l :: ∀ ɑ₁ .. ɑₙ. τ -> (ɑ₁, .., ɑₙ) F
  = "In Ω, label l has type τ for type former F"
```

For constructors and labels, we define the following constraints: 
```ocaml
C ⊢ ∃ ɑ₁ .. ɑₙ. τ = (ɑ₁ .. ɑₙ) F    Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. (ɑ₁, .., ɑₙ) F   
---------------------------------------------------------------------
                            C ⊢ K <= τ


C ⊢ ∃ ɑ₁ .. ɑₙ. (τ₁ = τ && τ₂ = (ɑ₁ .. ɑₙ) F)    Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. τ -> (ɑ₁, .., ɑₙ) F   
---------------------------------------------------------------------------------------
                                  C ⊢ K <= τ₁ -> τ₂


C ⊢ ∃ ɑ₁ .. ɑₙ. (τ₁ = τ && τ₂ = (ɑ₁ .. ɑₙ) F)    Ω ⊢ l :: ∀ ɑ₁ .. ɑₙ. τ -> (ɑ₁, .., ɑₙ) F   
---------------------------------------------------------------------------------------
                                  C ⊢ l <= τ₁ -> τ₂
```
where the context Ω is implicit. 

### Procaml Type System

The type system is given by:
```ocaml
(* ⊢ const : τ *)

-----------
 ⊢ n : int

-------------
 ⊢ () : unit

(* ⊢ prim : τ *)

  ⊕ ∈ { (+), (-), (x), (/) }
------------------------------
   ⊢ ⊕ : int -> int -> int

(* C ⊢ e : τ *)

 C ⊢ x <= τ
------------
 C ⊢ x : τ


   ⊢ const : τ
---------------
 C ⊢ const : τ


   ⊢ prim : τ
--------------
 C ⊢ prim : τ


   C ⊢ p -> e : τ₁ => τ₂
---------------------------
 C ⊢ fun p -> e : τ₁ -> τ₂


 C₁ ⊢ e₁ : τ₁ -> τ₂   C₂ ⊢ e₂ : τ₁
-----------------------------------
       C₁ && C₂ ⊢ e₁ e₂ : τ₂


  Γ ⊢ bs          C ⊢ e : τ
------------------------------
 let Γ in C ⊢ let bs in e : τ 


  Γ ⊢ bs          C ⊢ e : τ      mode ⊢ bs : rec 
-------------------------------------------------
       let rec Γ in C ⊢ let bs in e : τ 


  C ⊢ e : τ               ɑ₁ .. ɑₙ # τ
-----------------------------------------
 ∃ ɑ₁ .. ɑₙ. C ⊢ exists ɑ₁ .. ɑₙ -> e : τ


   C ⊢ e : τ           θ = { τ₁ \ ɑ₁, ..}
---------------------------------------------
 ∀ ɑ₁ .. ɑₙ. C ⊢ forall ɑ₁ .. ɑₙ -> e : θ(τ)


    C ⊢ e : τ
-------------------
 C ⊢ (e : τ) : τ


  ∀ 1 <= i <= n. Cᵢ ⊢ lᵢ = eᵢ : (τ₁, .., τₙ) F   
  Ω ⊢ F { l₁'; .. ; lₙ' }
  l₁, .., lₙ permutes l₁', .. , lₙ'
------------------------------------------------------------------------
  C₁ && .. && Cₙ ⊢ { l₁ = e₁ ; ..; lₙ = eₙ } : (τ₁, .., τₙ) F


 C ⊢ e : τ₁
 C ⊢ l <= τ₁ -> τ₂
-------------------
  C ⊢ l = e : τ₂


 C ⊢ e : τ₂  
 C ⊢ l <= τ₁ -> τ₂ 
-------------------
  C ⊢ e.l : τ₁


 C ⊢ K <= τ
------------
 C ⊢ K : τ


 C ⊢ e : τ₁
 C ⊢ K <= τ₁ -> τ₂
-------------------
  C ⊢ K e : τ₂


 C₁ ⊢ e : τ₁    C₂ ⊢ hs : τ₁ => τ₂
-----------------------------------
 C₁ && C₂ ⊢ match e with hs : τ₂


  ∀ 1 <= i <= n. Cᵢ ⊢ hᵢ : τ₁ => τ₂
------------------------------------------------
  C₁ && .. && Cₙ ⊢ (h₁ | .. | h₂) : τ₁ => τ₂


 C₁ ⊢ p : τ ~> Δ            C₂ ⊢ e : τ₂
-----------------------------------------
 C₁ && def Δ in C₂ ⊢ p -> e : τ₁ => τ₂ 


  C ⊢ e : τ               ɑ₁ .. ɑₙ # τ
-----------------------------------------
          ∃ ɑ₁ .. ɑₙ. C ⊢ e : τ


  C ⊢ e : τ₁               
------------------------
  C && τ₁ = τ₂ ⊢ e : τ₂

(* Γ ⊢ bs *)

-------
 . ⊢ . 

   Γ ⊢ bs   C₁ ⊢ p : τ ~> Δ    C₂ ⊢ e : τ
---------------------------------------------
 Γ, ∀ ɑ₁ .. ɑₙ. C₁ && C₂ => Δ ⊢ bs and p = e 

(* C ⊢ p : τ ~> Δ *)

fragments     Δ ::= . | Δ, x : τ

----------------
 C ⊢ _ : τ ~> .


--------------------
 C ⊢ x : τ ~> x : τ


   ⊢ const : τ
--------------------
 C ⊢ const : τ ~> .


 C ⊢ K <= τ 
----------------
 C ⊢ K : τ ~> .


 C ⊢ p : τ₁ ~> Δ
 C ⊢ K <= τ₁ -> τ₂
-------------------
 C ⊢ K p : τ ~> Δ


  ∀ 1 <= i <= n. Cᵢ ⊢ pᵢ ~> Δᵢ : τᵢ   
-------------------------------------------------------------
  C₁ && .. && Cₙ ⊢ (p₁, .., pₙ) : τ₁ x .. x τₙ ~> Δ₁ x .. x Δₙ


 C ⊢ p : τ ~> Δ
----------------------
 C ⊢ (p : τ) : τ ~> Δ


  C ⊢ p : τ ~> Δ         ɑ₁ .. ɑₙ # τ, Δ
-----------------------------------------
       ∃ ɑ₁ .. ɑₙ. C ⊢ p : τ ~> Δ


  C ⊢ p : τ₁ ~> Δ               
-----------------------------
  C && τ₁ = τ₂ ⊢ p : τ₂ ~> Δ
```

#

## Constraint Sharing

The next type system is built on the notion of explicit sharing of types within constraints,
via the usage of variables. 

While this improves efficiency and is required for Ambivalent types, it makes the type system harder to reason about. 

In the Ambivalent types [??], this is known as the "split view". 

### Constraints

```ocaml
constraints     C ::= 
                  | ⊥ | ⊤ | ɑ₁ = ɑ₂ | C && C 
                  | ∃ ɑ. C | ∃ ɑ [ɑ = ρ]. C | ∀ ɑ. C 
                  | def Γ in C | x <= ɑ | σ <= ɑ
                  | let Γ in C | let rec Γ in C


shared types    ρ ::= ɑ -> ɑ | (ɑ₁, .., ɑₙ) F

rigid view      Λ ::= . | Λ, ɑ
flexible view   Θ ::= . | Θ, ɑ | Θ, ɑ = ρ

shared schemes  σ ::= ∀ Θ. C => ɑ

contexts        Γ ::= . | x : ∀ Λ ∃ Θ. C => ɑ 
```

Change log: 

- Added `∃ ɑ [ɑ = ρ]` for explicitly building types
- Changed equality and instantiation constraints to use variables
- Updated bindings in contexts `Γ`, now has the notion of binding
  rigid variables. 

  Used in the `forall` expression for efficient (linear) constraint generation.

### Type System

Syntactic sugar: 
```ocaml
ɑ = ρ === ∃ β [β = ρ]. ɑ = β
```

```ocaml
(* C ⊢ const : ɣ *)

----------------------
 C && ɣ = int ⊢ n : ɣ

------------------------
 C && ɣ = unit ⊢ () : ɣ

(* C ⊢ prim : ɣ *)

      ⊕ ∈ { (+), (-), (x), (/) }
--------------------------------------
  C && ɣ = int -> int -> int ⊢ ⊕ : ɣ

(* C ⊢ e : ɣ *)

 C ⊢ x <= ɣ
------------
 C ⊢ x : ɣ


 C ⊢ const : ɣ
---------------
 C ⊢ const : ɣ


 C ⊢ prim : ɣ
--------------
 C ⊢ prim : ɣ


      C ⊢ p -> e : ɑ => β
----------------------------------
 C && ɣ = ɑ -> β ⊢ fun p -> e : ɣ


    C₁ ⊢ e₁ : ɑ   C₂ ⊢ e₂ : β
-------------------------------------
  ɑ = β -> ɣ && C₁ && C₂ ⊢ e₁ e₂ : ɣ


  Γ ⊢ bs          C ⊢ e : ɣ
------------------------------
 let Γ in C ⊢ let bs in e : ɣ 


  Γ ⊢ bs          C ⊢ e : ɣ      mode ⊢ bs : rec 
-------------------------------------------------
       let rec Γ in C ⊢ let bs in e : ɣ 


  C ⊢ e : ɣ               ɑ₁ .. ɑₙ <> ɣ
-----------------------------------------
 ∃ ɑ₁ .. ɑₙ. C ⊢ exists ɑ₁ .. ɑₙ -> e : ɣ


                            C ⊢ e : ɣ           
---------------------------------------------------------------------
 let x : ∀ ɑ₁ .. ɑₙ ∃ β. C => β in x <= ɣ  ⊢ forall ɑ₁ .. ɑₙ -> e : ɣ


  [τ] = Θ |> ɑ      C ⊢ e : ɣ
-------------------------------
 ∃ Θ. C && ɑ = ɣ ⊢ (e : τ) : ɣ


  ∀ 1 <= i <= n. Cᵢ ⊢ lᵢ = eᵢ : ɣ   
  Ω ⊢ F { l₁'; .. ; lₙ' }
  l₁, .., lₙ permutes l₁', .. , lₙ'
------------------------------------------------------------------------
  C₁ && .. && Cₙ && ɣ = (ɑ₁, .., ɑₙ) F ⊢ { l₁ = e₁ ; ..; lₙ = eₙ } : ɣ


 C ⊢ e : ɑ
 C ⊢ l <= ɑ -> ɣ
-------------------
  C ⊢ l = e : ɣ


 C ⊢ e : ɑ  
 C ⊢ l <= ɣ -> ɑ 
-----------------
  C ⊢ e.l : ɣ


 C ⊢ K <= ɣ
------------
 C ⊢ K : ɣ


 C ⊢ e : ɑ
 C ⊢ K <= ɑ -> ɣ
-------------------
  C ⊢ K e : ɣ


 C₁ ⊢ e : ɑ    C₂ ⊢ hs : ɑ => ɣ
-----------------------------------
 C₁ && C₂ ⊢ match e with hs : ɣ


  ∀ 1 <= i <= n. Cᵢ ⊢ hᵢ : ɑ => β
-------------------------------------------
  C₁ && .. && Cₙ ⊢ (h₁ | .. | h₂) : ɑ => β


 C₁ ⊢ p : ɑ ~> Δ            C₂ ⊢ e : β
-----------------------------------------
 C₁ && def Δ in C₂ ⊢ p -> e : ɑ => β 


  C ⊢ e : ɣ               ɑ₁ .. ɑₙ <> ɣ
-----------------------------------------
          ∃ ɑ₁ .. ɑₙ. C ⊢ e : ɣ


  C ⊢ e : ɑ               
------------------------
  C && ɑ = β ⊢ e : β

(* Γ ⊢ bs *)

-------
 . ⊢ . 

   Γ ⊢ bs   C₁ ⊢ p : ɑ ~> Δ    C₂ ⊢ e : ɑ
---------------------------------------------
 Γ, ∀ Λ ∃ Θ, ɑ. C₁ && C₂ => Δ ⊢ bs and p = e 

(* C ⊢ p : ɣ ~> Δ *)

fragments     Δ ::= . | Δ, x : ɑ

----------------
 C ⊢ _ : ɣ ~> .


--------------------
 C ⊢ x : ɣ ~> x : ɣ


 C ⊢ const : ɣ
--------------------
 C ⊢ const : ɣ ~> .


 C ⊢ K <= ɣ 
----------------
 C ⊢ K : ɣ ~> .


 C ⊢ p : ɑ ~> Δ
 C ⊢ K <= ɑ -> ɣ
-------------------
 C ⊢ K p : ɣ ~> Δ


  ∀ 1 <= i <= n. Cᵢ ⊢ pᵢ : ɑᵢ ~> Δᵢ   
-------------------------------------------------------------
  C₁ && .. && Cₙ && ɣ = ɑ₁ x .. x ɑₙ ⊢ (p₁, .., pₙ) : ɣ ~> Δ₁ x .. x Δₙ


  [τ] = Θ |> ɑ    C ⊢ p : ɑ ~> Δ
------------------------------------
 ∃ Θ. C && ɣ = ɑ ⊢ (p : τ) : ɣ ~> Δ


  C ⊢ p : ɣ ~> Δ         ɑ₁ .. ɑₙ # ɣ, Δ
-----------------------------------------
       ∃ ɑ₁ .. ɑₙ. C ⊢ p : ɣ ~> Δ


  C ⊢ p : ɑ ~> Δ               
-----------------------------
  C && ɑ = β ⊢ p : β ~> Δ
```

Change log:

- All judgement use variables, relying on explicit equivalences via `=`
- Initial judgements are surrounded by their initial view (e.g. `C ⊢ e : τ` is converted to `∃ Θ. C ⊢ e : ɑ` where `[τ] = Θ |> ɑ`). 
- Existential variables are used more often for constructing types.

#

## Implication Constraints

The next type system is an idealized implementation of implication constraints 
(the constraints added by Haskell's OutsideIn [??]). 

### Constraints and OutsideIn

OutsideIn's idealized type system adds 2 features, "rigid variables" (also known as skolem constants) and implication constraints.

Procaml already has a notion of "rigid variables" due to it's universal quantifier `∀`. Hence the only addition to constraints is the implication constraint. 

```ocaml
constraints     C ::= ... | C => C
```

### Constructors, Environments and Fragments

GADTs introduce 2 new features to constructors, the notion of binding local constraints and existential variables. 

We modify the abstract judgments of the environment Ω to account for these:
```ocaml
Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. D => (ɑ₁, .., ɑₙ) F
  = "In Ω, constant constructor K for type former F binds local constraint D"

Ω ⊢ K e :: ∀ ɑ₁ .. ɑₙ. ∃ βₙ .. βₘ. D => τ -> (ɑ₁, .., ɑₙ) F
  = "In Ω, constructor K for type former F w arugment of 
     type τ binds existentials βₙ .. βₘ and local constraint D"
```

This gives us the following instantiation constraints for GADT constructors: 
```ocaml
C ⊢ ∃ ɑ₁ .. ɑₙ. D && τ = (ɑ₁ .. ɑₙ) F    
Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. D => (ɑ₁, .., ɑₙ) F   
---------------------------------------------------
    C ⊢ K <= τ


C ⊢ ∃ ɑ₁ .. ɑₙ. τ = (ɑ₁ .. ɑₙ) F    
Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. D => (ɑ₁, .., ɑₙ) F   
---------------------------------------------------
    C ⊢ τ <= K ~> D


C ⊢ ∃ ɑ₁ .. ɑₙ β₁ .. βₘ. D && τ₁ = τ && τ₂ = (ɑ₁ .. ɑₙ) F    
Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. ∃ β₁ .. βₘ. D => τ -> (ɑ₁, .., ɑₙ) F   
---------------------------------------------------------
    C ⊢ K <= τ₁ -> τ₂


C ⊢ ∃ ɑ₁ .. ɑₙ. ∀ β₁ .. βₘ. τ₁ = τ && τ₂ = (ɑ₁ .. ɑₙ) F    
Ω ⊢ K :: ∀ ɑ₁ .. ɑₙ. ∃ β₁ .. βₘ. D => τ -> (ɑ₁, .., ɑₙ) F   
---------------------------------------------------------
    C ⊢ τ₁ -> τ₂ <= K ~> ∀ β₁ .. βₘ. D
```


Similarly, environment fragments used for pattern matching must be altered 
to account for locally bound existential variables and local constraints.

```ocaml
monomorphic env     Ξ ::= . | x : τ
fragment            Δ ::= ∀  β₁ .. βₘ. D => Ξ

Δ₁ x Δ₂ = ∀ β₁ β₂. D₁ && D₂ => Ξ₁, Ξ₂
∀ β₁. D₁ => Δ₂ = ∀ β₁ β₂. D₁ && D₂ => Ξ₂
```

### Type System

```ocaml
(* C ⊢ e : τ *)

...

 C ⊢ p : τ₁ ~> ∀ β. D => Ξ     E ⊢ e : τ₂   β # τ₂
---------------------------------------------------
 C && ∀ β. D => def Ξ in E ⊢ p -> e : τ₁ => τ₂

(* C ⊢ p : τ ~> Δ *)

------------------------
 C ⊢ _ : τ ~> ∀ .⊤ => .


----------------------------
 C ⊢ x : τ ~> ∀ .⊤ => x : τ


        ⊢ const : τ
----------------------------
 C ⊢ const : τ ~> ∀ .⊤ => .


 C ⊢ τ <= K ~> D 
--------------------------
 C ⊢ K : τ ~> ∀. D => .


 C ⊢ τ₁ -> τ₂ <= K ~> ∀ β. D
 C && D ⊢ p : τ₁ ~> Δ
-----------------------------
 C ⊢ K p : τ ~> ∀ β. D => Δ


  ∀ 1 <= i <= n. Cᵢ ⊢ pᵢ : τᵢ ~> Δᵢ   
-------------------------------------------------------------
  C₁ && .. && Cₙ ⊢ (p₁, .., pₙ) : τ₁ x .. x τₙ ~> Δ₁ x .. x Δₙ


 C ⊢ p : τ ~> Δ
----------------------
 C ⊢ (p : τ) : τ ~> Δ


  C ⊢ p : τ ~> Δ         ɑ₁ .. ɑₙ # τ, Δ
-----------------------------------------
       ∃ ɑ₁ .. ɑₙ. C ⊢ p : τ ~> Δ


  C ⊢ p : τ₁ ~> Δ               
-----------------------------
  C && τ₁ = τ₂ ⊢ p : τ₂ ~> Δ
```
