{-# OPTIONS --prop --rewriting --allow-unsolved-meta #-}

module logic where
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive

variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ' ℓ'' : Level

infixl 10 _∧_ _*_ _,_
infixl 9 _∨_ _⊎_
data _∨_ (P : Prop ℓ) (Q : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    ι₁ : P -> P ∨ Q
    ι₂ : Q -> P ∨ Q
data _⊎_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    inj₁ : P -> P ⊎ Q
    inj₂ : Q -> P ⊎ Q
record _∧_ (P : Prop ℓ) (Q : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    constructor [_,_]
    field
        π₁ : P
        π₂ : Q
record _*_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,_
    field
        proj₁ : P
        proj₂ : Q
data Exists (A : Set ℓ) (P : A -> Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    exists : (a : A) -> P a -> Exists A P
syntax Exists A (\x -> P) = ∃[ x ∈ A ] P

data ExistsUnique (A : Set ℓ) (P : A -> Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    exists-unique : (a : A) -> (∀ b -> P b -> b ≡ a) -> ExistsUnique A P
syntax ExistsUnique A (\x -> P) = ∃![ x ∈ A ] P

infixr 10 Exists ExistsUnique

data ⊥ {ℓ} : Prop ℓ where
ex-falso : {P : Prop ℓ'} -> ⊥ {ℓ} -> P
ex-falso ()
magic : {A : Set ℓ'} -> ⊥ {ℓ} -> A
magic ()
record ⊤ {ℓ} : Prop ℓ where
    constructor trivial

transport : {A B : Set ℓ} -> A ≡ B -> A -> B
transport refl a = a

cong : {T : Set ℓ} {A B : T} {C : Set ℓ'} (f : T -> C)
    -> A ≡ B -> f A ≡ f B
cong f refl = refl

symm : {A : Set ℓ} {a b : A} -> a ≡ b -> b ≡ a
symm refl = refl

trans : {A : Set ℓ} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans refl refl = refl

data Bool : Set where
    true : Bool
    false : Bool

prop : Bool -> Prop ℓ
prop true = ⊤
prop false = ⊥

prop-≡ : ∀ {b} -> prop {ℓ} b -> b ≡ true
prop-≡ {b = true} _ = refl

postulate
    truth : (P : Prop ℓ) -> (P ≡ ⊤) ⊎ (P ≡ ⊥)

abstract
    decide : Prop ℓ -> Bool
    decide P with truth P
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    prop-decide : (P : Prop ℓ) -> prop (decide P) ≡ P
    prop-decide P with truth P
    ... | inj₁ eq = symm eq
    ... | inj₂ eq = symm eq

equal-equiv : {P Q : Prop ℓ} -> P ≡ Q -> P -> Q
equal-equiv refl p = p

equiv-equal : {P Q : Prop ℓ} -> (P -> Q) ∧ (Q -> P) -> P ≡ Q
equiv-equal {P = P} {Q = Q} [ P->Q , Q->P ] with truth P | truth Q
... | inj₁ refl | inj₁ refl = refl
... | inj₁ refl | inj₂ refl = magic (P->Q _)
... | inj₂ refl | inj₁ refl = magic (Q->P _)
... | inj₂ refl | inj₂ refl = refl

abstract
    decide-prop : ∀ b -> decide {lzero} (prop b) ≡ b
    decide-prop true with truth {lzero} ⊤
    ... | inj₁ _ = refl
    ... | inj₂ eq = magic (equal-equiv eq _)
    decide-prop false with truth {lzero} ⊥
    ... | inj₁ eq = magic (equal-equiv (symm eq) _)
    ... | inj₂ _ = refl

≡-true : {P : Prop ℓ} -> P ≡ ⊤ -> P
≡-true refl = _

infixr 15 ¬_
¬_ : Prop ℓ -> Prop ℓ
¬_ {ℓ} P = P -> ⊥ {ℓ}

¬⊤≡⊥ : ¬ ⊤ ≡ ⊥ {ℓ}
¬⊤≡⊥ = equiv-equal [ (\ f -> f _) , (\ ()) ]

¬⊥≡⊤ : ¬ ⊥ ≡ ⊤ {ℓ}
¬⊥≡⊤ = equiv-equal [ (\ _ -> _) , (\ _ ()) ]

¬¬P≡P : ∀ {P : Prop ℓ} -> ¬ ¬ P ≡ P
¬¬P≡P {P = P} with truth P 
... | inj₁ refl = equiv-equal [ (\ _ -> _) , (\ _ z -> z _) ]
... | inj₂ refl = equiv-equal [ (\ f -> f \ z -> z) , (\ z f -> f z) ]

false-≡ : ∀ {P : Prop ℓ} -> ¬ P -> P ≡ ⊥
false-≡ ¬P = equiv-equal [ ¬P , (\ ()) ]

≡-false : ∀ {P : Prop ℓ} -> P ≡ ⊥ -> ¬ P
≡-false refl ()

choice : (A : Set ℓ) (P : A -> Prop ℓ')
    -> (∀ x -> ¬ P x) ∨ ∃[ x ∈ A ] P x
choice A P with truth (∃[ x ∈ A ] P x)
... | inj₁ eq rewrite eq = ι₂ _
... | inj₂ eq = ι₁ \ x Px -> ex-falso (equal-equiv eq (exists x Px))
-- We need the extra ex-falso to avoid universe level problems

syntax choice A (\ x -> P) = ε[ x ∈ A ] P

choice-safe : {A : Set ℓ} {P : A -> Prop ℓ'}
    -> ¬ (∀ x -> ¬ P x) -> ∃[ x ∈ A ] P x
choice-safe {A = A} {P = P} np with ε[ x ∈ A ] P x
... | ι₁ p = ex-falso (np p)
... | ι₂ ex = ex

postulate
    funext : {A : Set ℓ} {B : A -> Set ℓ'}
        -> {f g : ∀ a -> B a}
        -> (f ≡ g) ≡ (∀ x -> f x ≡ g x)

-- Some syntax for chaining.
_Then_ : {A : Prop ℓ} {B : Prop ℓ'} {C : Prop ℓ''}
    -> (A -> B) -> (B -> C) -> (A -> C)
(f Then g) a = g (f a)

_ThusFrom_ : {A : Prop ℓ} {B : Prop ℓ'}
    -> A -> (A -> B) -> B
a ThusFrom f = f a

infixr 2 _Then_ _ThusFrom_

-- Develop boolean reflection tools.
infixl 15 _&&_
infixl 14 _||_
infixr 13 _=>_
_&&_ : Bool -> Bool -> Bool
true && true = true
_ && _ = false

&&-reflect : ∀ x y -> prop {ℓ} (x && y) -> prop {ℓ} x ∧ prop {ℓ} y
&&-reflect true true _ = [ _ , _ ]

_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true

||-reflect : ∀ x y -> prop {ℓ} (x || y) -> prop {ℓ} x ∨ prop {ℓ} y
||-reflect true true _ = ι₁ _
||-reflect true false _ = ι₁ _
||-reflect false true _ = ι₂ _

_=>_ : Bool -> Bool -> Bool
true => false = false
_ => _ = true

=>-reflect : ∀ x y -> prop {ℓ} (x => y) -> prop {ℓ} x -> prop {ℓ} y
=>-reflect _ true _ _ = _
=>-reflect false _ _ ()

not : Bool -> Bool
not true = false
not false = true

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data PVar : Nat -> Set where
    this : {i : Nat} -> PVar (succ i)
    that : {i : Nat} -> PVar i -> PVar (succ i)

infixl 15 _F&_
infixl 14 _F|_
infixr 13 _F>_
infix 10 _⊨_ _⊢_

data Formula (n : Nat) : Set where
    tt : Formula n
    ff : Formula n
    F : PVar n -> Formula n
    _F&_ : Formula n -> Formula n -> Formula n
    _F|_ : Formula n -> Formula n -> Formula n
    _F>_ : Formula n -> Formula n -> Formula n

private
    _⊨_ : {i : Nat} -> (PVar i -> Bool) -> (Formula i -> Bool)
    Γ ⊨ tt = true
    Γ ⊨ ff = false
    Γ ⊨ F x = Γ x
    Γ ⊨ f F& g = (Γ ⊨ f) && (Γ ⊨ g)
    Γ ⊨ f F| g = (Γ ⊨ f) || (Γ ⊨ g)
    Γ ⊨ f F> g = (Γ ⊨ f) => (Γ ⊨ g)

    _⊢_ : {i : Nat} -> (PVar i -> Prop ℓ) -> (Formula i -> Prop ℓ)
    Γ ⊢ tt = ⊤
    Γ ⊢ ff = ⊥
    Γ ⊢ F x = Γ x
    Γ ⊢ f F& g = (Γ ⊢ f) ∧ (Γ ⊢ g)
    Γ ⊢ f F| g = (Γ ⊢ f) ∨ (Γ ⊢ g)
    Γ ⊢ f F> g = (Γ ⊢ f) -> (Γ ⊢ g)

    Soundness : ∀ {i} (f : Formula i)
        -> ∀ {ℓ} Γ -> (\ x -> prop {ℓ} (Γ x)) ⊢ f
        -> prop {ℓ} (Γ ⊨ f)
    Completeness : ∀ {i} (f : Formula i)
        -> ∀ {ℓ} Γ -> prop {ℓ} (Γ ⊨ f)
        -> (\ x -> prop {ℓ} (Γ x)) ⊢ f

    Soundness tt Γ prf = _
    Soundness (F x) Γ prf = prf
    Soundness (f F& g) Γ [ Pf , Pg ] with Γ ⊨ f in eqf | Γ ⊨ g in eqg
    ... | true | true = _
    ... | true | false = equal-equiv (cong prop eqg) (Soundness g Γ Pg)
    ... | false | _ = equal-equiv (cong prop eqf) (Soundness f Γ Pf)
    Soundness (f F| g) Γ prf with Γ ⊨ f in eqf | Γ ⊨ g in eqg
    ... | true | _ = _
    ... | false | true = _
    Soundness (f F| g) Γ (ι₁ Pf) | false | false = equal-equiv (cong prop eqf) (Soundness f Γ Pf)
    Soundness (f F| g) Γ (ι₂ Pg) | false | false = equal-equiv (cong prop eqg) (Soundness g Γ Pg)
    Soundness (f F> g) Γ prf with Γ ⊨ f in eqf | Γ ⊨ g in eqg
    ... | false | _ = _
    ... | true | true = _
    ... | true | false = equal-equiv (cong prop eqg)
        (Soundness g Γ
            (prf (Completeness f Γ
                (equal-equiv (cong prop (symm eqf)) _))))

    Completeness tt Γ prf = _
    Completeness (F x) Γ prf = prf
    Completeness (f F& g) Γ prf =
        [ Completeness f Γ (_∧_.π₁ prf') , Completeness g Γ (_∧_.π₂ prf') ]
        where
            prf' : prop (Γ ⊨ f) ∧ prop (Γ ⊨ g)
            prf' = &&-reflect _ _ prf
    Completeness (f F| g) Γ prf with ||-reflect _ _ prf
    ... | ι₁ prf' = ι₁ (Completeness f Γ prf')
    ... | ι₂ prf' = ι₂ (Completeness g Γ prf')
    Completeness (f F> g) Γ prf Pf =
        Completeness g Γ
            (=>-reflect _ _ prf
                (Soundness f Γ Pf))

    {-# REWRITE prop-decide #-}

    set : ∀ {i} -> (PVar i -> Bool) -> Bool -> (PVar i -> Bool)
    set v b this = b
    set v b (that x) = v (that x)

    extend : ∀ {i} -> (PVar i -> Bool) -> Bool -> (PVar (succ i) -> Bool)
    extend v b this = b
    extend v b (that x) = v x

    var-elim : ∀ {i} -> (v : PVar (succ i) -> Bool) (u : Bool)
        -> v this ≡ u
        -> (v ≡ set v u)
    var-elim v .(v this) refl = transport (symm funext)
        \ { this -> refl ; (that x) -> refl }

    extend-tail : ∀ {i} -> (v : PVar i -> Bool) (u : Bool)
        -> ∀ x -> extend v u (that x) ≡ v x
    extend-tail _ _ _ = refl

    extend-head : ∀ {i} -> (v : PVar i -> Bool) (u : Bool)
        -> extend v u this ≡ u
    extend-head _ _ = refl

    tabulate : ∀ {i}
        -> ((PVar i -> Bool) -> Bool) -> Bool
    tabulate {i = zero} f = f (λ ())
    tabulate {i = succ i} f =
        (tabulate {i} \ t -> f (extend t true)) &&
        (tabulate {i} \ t -> f (extend t false))

    var-elim-case : ∀ {i} -> (v : PVar (succ i) -> Bool)
        -> (v ≡ set v true) ⊎ (v ≡ set v false)
    var-elim-case v with v this in eq
    ... | true = inj₁ (var-elim v true eq)
    ... | false = inj₂ (var-elim v false eq)

    set-extend : ∀ {i} -> (v : PVar i -> Bool) (u1 u2 : Bool)
        -> ∀ x -> set (extend v u1) u2 x ≡ extend v u2 x
    set-extend v u1 u2 this = refl
    set-extend v u1 u2 (that x) = refl

    tabulate-constant : ∀ {i} (f : (PVar i -> Bool) -> Bool)
        -> prop {lzero} (tabulate f)
        -> ∀ v -> f v ≡ true
    tabulate-constant {i = zero} f t v = aux
        where
            v-trivial : v ≡ \ ()
            v-trivial = transport (symm funext) \ ()
            aux : f v ≡ true
            aux rewrite v-trivial = prop-≡ t
    tabulate-constant {i = succ i} f t v = {!   !}
        where
            t-reflect : prop (tabulate \ t -> f (extend t true)) ∧
                        prop (tabulate \ t -> f (extend t false))
            t-reflect = &&-reflect
                (tabulate {i} \ _ -> f _)
                (tabulate {i} \ _ -> f _) t

solve-uncurried : ∀ {i} (f : Formula i)
    -> prop {lzero} (tabulate (_⊨ f))
    -> (Γ : PVar i -> Prop ℓ) -> Γ ⊢ f
solve-uncurried f t Γ = Completeness f _ aux
    where
        aux : prop {ℓ} ((\ v -> decide (Γ v)) ⊨ f)
        aux rewrite tabulate-constant (_⊨ f) t \ v -> decide (Γ v) = _

P∨P : (P : Prop ℓ) -> P ∨ P ≡ P
P∨P P = equiv-equal
    (solve-uncurried {i = 1}
        ((F this F| F this F> F this) F& (F this F> F this F| F this)) _ \ _ -> P)
 