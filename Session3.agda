
{-

|---------------------------------------------------|
| Formal systems and their applications: exercises  |
| Session 3: Formalization of programming languages |
|---------------------------------------------------|

In this exercise session, the goal will be to see how Agda can be used to formalize
syntax, evaluation rules, and typing rules of programming languages. In this session,
you will do this for a very simple calculus, typed arithmetic expressions from
chapter 8 of "Types and Programming Languages". In the project for this course, you
will have to do the same for a more complicated language.
So you can see this exercise session as a kind of warm-up for the project.

-}

open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat?) hiding (pred ; _≤_ ; compare)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum hiding (map) renaming (inj₁ to left ; inj₂ to right)


-- Part 1: Untyped boolean terms
--==============================
-- First, we will define the basic syntax of a very simple untyped language of boolean
-- expressions (see TAPL p. 34):
data Term : Set where
  tmTrue   : Term
  tmFalse  : Term
  tmIf     : (t1 t2 t3 : Term) → Term
  tmZero   : Term
  tmSucc   : (t : Term) → Term
  tmPred   : (t : Term) → Term
  tmIszero : (t : Term) → Term

-- As a Warm-up exercise, define a function to calculate the size of a term
-- (see TAPL p. 29):
size : Term → Nat
size tmTrue = 1
size tmFalse = 1
size (tmIf t t₁ t₂) = 1 + (size t) + (size t₁) + (size t₂)
size (tmZero) = 1
size (tmSucc t) = 1 + size t
size (tmPred t) = 1 + size t
size (tmIszero t) = 1 + size t

-- In contrast to the TAPL book, in Agda we usually don't define a separate syntactic
-- class of values. Instead, we define a predicate "IsValue t" on terms that expresses
-- that the term t is a value.
data IsNumValue : Term → Set where
  valZero  : IsNumValue tmZero
  valSucc  : {nv : Term} (inv : IsNumValue nv) → IsNumValue (tmSucc nv)

data IsValue : Term → Set where
  valTrue  : IsValue tmTrue
  valFalse : IsValue tmFalse
  valNum   : {nv : Term} (inv : IsNumValue nv) → IsValue nv

-- To give the operational semantics of our language, we define the one-step evaluation
-- relation ↝ (unicode input: \r~) as an indexed datatype in Agda.
data _↝_ : Term → Term → Set where
  e-IfTrue     : {t2 t3 : Term} → ((tmIf tmTrue t2 t3) ↝ t2)
  e-IfFalse    : {t2 t3 : Term} → ((tmIf tmFalse t2 t3) ↝ t3)
  e-If         : {t₁ t₂ t₃ t₁′ : Term} → (t₁ ↝ t₁′) → ((tmIf t₁ t₂ t₃) ↝ (tmIf t₁′ t₂ t₃))
  e-Succ       : {t₁ t₁′ : Term} → (t₁ ↝ t₁′) → ((tmSucc t₁) ↝ (tmSucc t₁′))
  e-PredZero   : (tmPred tmZero) ↝ tmZero
  e-PredSucc   : {nv : Term} → IsNumValue nv → ((tmPred (tmSucc nv)) ↝ nv)
  e-Pred       : {t₁ t₁′ : Term} → (t₁ ↝ t₁′) → ((tmPred t₁) ↝ (tmPred t₁′))
  e-IszeroZero : (tmIszero tmZero) ↝ tmTrue
  e-IszeroSucc : {nv : Term} → IsNumValue nv → ((tmIszero (tmSucc nv)) ↝ tmFalse)
  e-Iszero     : {t₁ t₁′ : Term} → (t₁ ↝ t₁′) → ((tmIszero t₁) ↝ (tmIszero t₁′))

-- A term is normal if it doesn't evaluate any further
IsNormal : Term → Set
IsNormal t = {t' : Term} → (t ↝ t') → ⊥

-- Prove that all values are normal (Theorem 3.5.7 of TAPL):
values-normal : {t : Term} → IsValue t → IsNormal t
values-normal (valNum (valSucc inv)) (e-Succ step)
  = values-normal (valNum inv) step

-- _↝*_ is the multi-step evaluation relation:
-- x ↝* y means that x ↝ x1 ↝ x2 ↝ ... ↝ y
data _↝*_ : Term → Term → Set where
  done : {x : Term} → (x ↝* x)
  step_,_ : {x x1 y : Term} → (x ↝ x1) → (x1 ↝* y) → (x ↝* y)
infixr 0 step_,_

-- Exercise: as a test, state and prove that
--   if t then false else false ↝* false
-- where
--   s = if true then false else false
--   t = if s then true else true
-- Note: proving should be possible using C-c C-a.

test-eval1 : tmIf (tmIf (tmIf tmTrue tmFalse tmFalse) tmTrue tmTrue) tmFalse tmFalse
         ↝* tmFalse
test-eval1 = step e-If (e-If e-IfTrue) ,
             step e-If e-IfFalse ,
             step e-IfTrue ,
             done


-- Part 2: Untyped arithmetic terms
--=================================

-- As an exercise, add new syntactic forms and evaluation rules for natural numbers
-- to the definitions above (see TAPL p. 41). Also add extra cases to the other 
-- functions so that everything typechecks again. You will need to define a new
-- datatype IsNumValue : Term → Set that describes when a term is a numeric value.
--   (When making changes, it is best to comment out all that follows, to make Agda
--   stop complaining. That way, you can make your document consistent again
--   definition by definition.)

-- Exercise: as a test, state and prove that
--   if false then 0 else (pred (suc (pred 0))) ↝* 0

test-eval2 : tmIf tmFalse tmZero (tmPred (tmSucc (tmPred tmZero))) ↝* tmZero
test-eval2 = step e-IfFalse ,
             step e-Pred (e-Succ e-PredZero) ,
             step e-PredSucc valZero ,
             done


-- Part 3: Typed arithmetic terms
--===============================

-- Now we will define a type system for this simple language of booleans and
-- natural numbers. It has two types: Bool and Nat.
data Type : Set where
  tyBool : Type
  tyNat  : Type

-- As with the evaluation rules, we encode the typing rules as a data type
-- We use the unicode symbol ∈ (input \in) instead of a colon because the colon
-- is already reserved by Agda.
-- We use the prefix d- for elements of this type, which are called [d]erivations.
data _∈_ : Term → Type → Set where
  d-True  : tmTrue  ∈ tyBool
  d-False : tmFalse ∈ tyBool
  d-Zero  : tmZero  ∈ tyNat
  d-If    : {t₁ t₂ t₃ : Term} {T : Type}
        → t₁ ∈ tyBool
        → t₂ ∈ T
        → t₃ ∈ T
          --------------------
        → (tmIf t₁ t₂ t₃) ∈ T
  d-Succ : {t : Term}
       → t ∈ tyNat
         -------------------
       → (tmSucc t) ∈ tyNat
  d-Pred : {t : Term}
       → t ∈ tyNat
       -------------------
       → (tmPred t) ∈ tyNat
  d-Iszero : {t : Term}
             → t ∈ tyNat
               ---------------------
             → (tmIszero t) ∈ tyBool

-- As a test, prove that the term `if (iszero 0) then 0 else (pred 0)`
-- has type Nat.
test-typing : tmIf (tmIszero tmZero) tmZero (tmPred tmZero) ∈ tyNat
test-typing = d-If (d-Iszero d-Zero) d-Zero (d-Pred d-Zero)

-- Inversion lemmas (see TAPL p. 94):
inversion-true : {tyR : Type} → tmTrue ∈ tyR → tyR ≡ tyBool
inversion-true d-True = refl

inversion-false : {tyR : Type} → tmFalse ∈ tyR → tyR ≡ tyBool
inversion-false d-False = refl

inversion-if : {tyR : Type} {t₁ t₂ t₃ : Term} → (tmIf t₁ t₂ t₃) ∈ tyR
              → (t₁ ∈ tyBool) × (t₂ ∈ tyR) × (t₃ ∈ tyR)
inversion-if (d-If d₁ d₂ d₃) = d₁ , d₂ , d₃

inversion-zero : {tyR : Type} → (tmZero ∈ tyR) → tyR ≡ tyNat
inversion-zero d-Zero = refl

inversion-succ : {tyR : Type} {t : Term} → (tmSucc t) ∈ tyR
             → (tyR ≡ tyNat) × (t ∈ tyNat)
inversion-succ (d-Succ d) = refl , d

inversion-pred : {tyR : Type} {t : Term} → (tmPred t) ∈ tyR
             → (tyR ≡ tyNat) × (t ∈ tyNat)
inversion-pred (d-Pred d) = refl , d

inversion-iszero : {tyR : Type} {t : Term} → (tmIszero t) ∈ tyR
               → (tyR ≡ tyBool) × (t ∈ tyNat)
inversion-iszero (d-Iszero d) = refl , d

-- Uniqueness of types (see TAPL p. 94):
uniqueness-of-types : {t : Term} {tyT1 tyT2 : Type} → t ∈ tyT1 → t ∈ tyT2 → tyT1 ≡ tyT2
uniqueness-of-types d-True d-True  = refl
uniqueness-of-types d-False d-False = refl
uniqueness-of-types d-Zero d-Zero  = refl
uniqueness-of-types (d-If _ d₁ _) (d-If _ d₂ _) = uniqueness-of-types d₁ d₂
uniqueness-of-types (d-Succ d1)   (d-Succ d2)   = refl
uniqueness-of-types (d-Pred d1)   (d-Pred d2)   = refl
uniqueness-of-types (d-Iszero d1) (d-Iszero d2) = refl

-- Part 4: Safety = progress + preservation (see TAPL p. 96-97)
--=============================================================

-- First, prove the canonical forms lemma (lemma 8.3.1):
canonical-forms-bool : {t : Term} → (IsValue t) → (t ∈ tyBool)
                   → (t ≡ tmTrue) ⊎ (t ≡ tmFalse)
canonical-forms-bool valTrue  dt = left refl
canonical-forms-bool valFalse dt = right refl
canonical-forms-bool (valNum valZero)       ()
canonical-forms-bool (valNum (valSucc inv)) ()

-- Also state and prove the canonical forms lemma for the Nat type:
-- (i.e. prove that any value of type Nat is a numeric value)
canonical-forms-nat : {t : Term} → (IsValue t) → (t ∈ tyNat)
                  → IsNumValue t
canonical-forms-nat (valNum inv) pf = inv

-- Now you are ready to prove progress and preservation of this language.


preservation : {t t' : Term} {tyT : Type} → (t ↝ t') → (t ∈ tyT) → (t' ∈ tyT)
preservation e-IfTrue         (d-If d1 d2 d3)     = d2
preservation e-IfFalse        (d-If d1 d2 d3)     = d3
preservation (e-If e)         (d-If d1 d2 d3)     = d-If     (preservation e d1) d2 d3
preservation (e-Succ e)       (d-Succ d)          = d-Succ   (preservation e d)
preservation e-PredZero       (d-Pred d)          = d-Zero
preservation (e-PredSucc x)   (d-Pred (d-Succ d)) = d
preservation (e-Pred e)       (d-Pred d)          = d-Pred   (preservation e d)
preservation e-IszeroZero     (d-Iszero d)        = d-True
preservation (e-IszeroSucc x) (d-Iszero d)        = d-False
preservation (e-Iszero e)     (d-Iszero d)        = d-Iszero (preservation e d)

-- Hint: you can use the `with` syntax to pattern match on the value of a
-- function call. For an example of how to use `with`, you can look at
-- the solution of the first exercise session.

-- Hint: you can write _ as an expression; Agda will then infer its value.
-- This is only possible when only one value would type-check (e.g. the first
-- component of a dependent pair).

progress : {t : Term} {tyT : Type} → t ∈ tyT → (IsValue t) ⊎ (Σ[ t' ∈ Term ] (t ↝ t'))
progress d-True  = left valTrue
progress d-False = left valFalse
progress d-Zero  = left (valNum valZero)
progress {tmIf t₁ t₂ t₃} (d-If d₁ d₂ d₃) with (progress d₁)
...                                      | right (t₁′ , nxt) = right (tmIf t₁′ t₂ t₃ , e-If nxt)
...                                      | left (valTrue)    = right (t₂ , e-IfTrue)
...                                      | left (valFalse)   = right (t₃ , e-IfFalse)
...                                      | left (valNum valZero) with inversion-if (d-If d₁ d₂ d₃)
...                                                                 | () , _ , _
progress {tmIf t₁ t₂ t₃} (d-If d₁ d₂ d₃) | left (valNum (valSucc x)) with inversion-if (d-If d₁ d₂ d₃)
...                                                                     | () , _ , _
progress (d-Succ d) with progress d
...                    | left  (valNum inv) = left  (valNum (valSucc inv))
...                    | right (t′ , nxt)   = right (tmSucc t′ , e-Succ nxt)
progress (d-Pred d) with progress d
...                    | left (valNum valZero)            = right (tmZero    , e-PredZero)
...                    | left (valNum (valSucc {nv} inv)) = right (nv        , e-PredSucc inv)
...                    | right (t′ , nxt)                 = right (tmPred t′ , e-Pred nxt)
progress (d-Iszero d) with progress d
...                    | left (valNum valZero)       = right (tmTrue      , e-IszeroZero)
...                    | left (valNum (valSucc inv)) = right (tmFalse     , e-IszeroSucc inv)
...                    | right (t′ , nxt)            = right (tmIszero t′ , e-Iszero nxt)

-------------------------------------------------------
-- Challenge: Prove normalization of this calculus.

-- The following lemmas are straightforward
-- to prove in terms of their counterparts that operate on ↝ instead of ↝*,
-- and may come in handy.

preservation* : {t t' : Term} {tyT : Type} → (t ↝* t') → (t ∈ tyT) → (t' ∈ tyT)
preservation* done dt              = dt
preservation* (step a↝b , b↝*c) dt = preservation* b↝*c (preservation a↝b dt)

map* : {f : Term → Term}
  → (f↝ : {t t' : Term} → t ↝ t' → f t ↝ f t')
  → {t t' : Term} → t ↝* t' → f t ↝* f t'
map* f↝ done           = done
map* f↝ (step x , et*) = step f↝ x ,
                         map* f↝ et*

step*_,_ : ∀ {t t' t''}
       → t ↝* t'
       → t' ↝* t''
         ----------
       → t ↝* t''
step* done           , et*' = et*'
step* (step x , et*) , et*' = step x , (step* et* , et*')

--now prove normalization

normalization : ∀ {t tyT} → t ∈ tyT → Σ[ t' ∈ Term ] ((t ↝* t') × IsValue t')
normalization d-True  = tmTrue  , done , valTrue
normalization d-False = tmFalse , done , valFalse
normalization d-Zero  = tmZero  , done , valNum valZero
normalization (d-If dt dt₁ dt₂) = {!!}
normalization (d-Succ dt)       = {!!}
normalization (d-Pred dt)       = {!!}
normalization (d-Iszero dt)     = {!!}
