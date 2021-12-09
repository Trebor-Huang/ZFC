{-# OPTIONS --prop --rewriting #-}

module ZF where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import logic
open _∧_

postulate
    -- We postulate a universe of sets, and a _∈_ relation between them.
    𝕍 : Set
    _∈_ : 𝕍 -> 𝕍 -> Prop
{-# INJECTIVE _∈_ #-}
infix 20 _∈_

private variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ' ℓ'' : Level
    x y z w : 𝕍  -- These will range over sets unless noted otherwise.

-- A propositional equality for convenience.
-- We avoid the use of this as much as possible.
data _≗_ : 𝕍 -> 𝕍 -> Prop where
    refl𝕍 : x ≗ x

-- The _∈_ relation is extensional. The elements of (_∈ x) uniquely defines x.
postulate
    Extensional : (∀ z -> z ∈ x ≡ z ∈ y) -> x ≡ y
-- The converse holds by Leibniz's law.
Extensional-converse : x ≡ y -> (∀ z -> z ∈ x ≡ z ∈ y)
Extensional-converse refl z = refl

-- Extensionality flattens the propositional equality into the regular one.
≗-≡ : x ≗ y -> x ≡ y
≗-≡ eq = Extensional (\ z -> equiv-equal (ex eq z))
    where
        ex : x ≗ y -> (z : 𝕍) -> (z ∈ x -> z ∈ y) ∧ (z ∈ y -> z ∈ x)
        ex refl𝕍 z = [ idP , idP ]

≡-≗ : x ≡ y -> x ≗ y
≡-≗ refl = refl𝕍

_≟_ : {A : Set ℓ} (x y : 𝕍) -> (x ≡ y) ⊎ (x ≡ y -> A)
x ≟ y with truth (x ≗ y)
... | inj₁ eq = inj₁ (≗-≡ (≡-true eq))
... | inj₂ neq = inj₂ \ { refl -> magic (≡-false neq refl𝕍) }

-- We postulate the existence of an empty set, i.e. a set with no elements
-- This is actually redundant from the other axioms, but we keep it for
-- aesthetic considerations.
postulate
    ∅ : 𝕍
    ∅-empty : x ∈ ∅ ≡ ⊥

{-# REWRITE ∅-empty #-}

-- From extensionality, we immediately obtain that the empty set is unique.
∅-unique : (∀ x -> x ∈ y ≡ ⊥) -> y ≡ ∅
∅-unique = Extensional  -- Well, that's literally immediate.

-- Conversely, every non-empty set has an element.
-- This crucially depends on the principle of excluded middle.
non-empty : (x ≢ ∅) -> ∃[ y ∈ 𝕍 ] (y ∈ x)
non-empty {x} neq with ε[ y ∈ 𝕍 ] (y ∈ x)
... | ι₁ no =            -- Case 1 : y contains no element,
        neq                  -- y is not the empty set (assumption), but
        (∅-unique \ y ->     -- y is the empty set, since
            false-≡ (no y))  -- y is contains no element. (assumption)
    ThusFrom ex-falso        -- Contradiction!
... | ι₂ yes = yes       -- Case 2 : y contains an element, QED.

-- We define the subset relation.
_⊆_ : 𝕍 -> 𝕍 -> Prop
x ⊆ y = ∀ {z} -> z ∈ x -> z ∈ y

x⊆∅-≡ : x ⊆ ∅ -> x ≡ ∅
x⊆∅-≡ s = ∅-unique \ y -> false-≡ s

x⊆∅ : (x ⊆ ∅) ≡ (x ≗ ∅)
x⊆∅ = equiv-equal [ (\ x⊆∅ -> ≡-≗ (x⊆∅-≡ x⊆∅)) , (\{ refl𝕍 -> idP }) ]

-- We postulate the existence of power sets.
postulate
    𝒫 : 𝕍 -> 𝕍
    Power : (x : 𝕍)
        -> ∀ z -> z ∈ 𝒫 x ≡ z ⊆ x
{-# REWRITE Power #-}

-- The empty set is in every power set.
∅∈𝒫x : ∅ ∈ 𝒫 x
∅∈𝒫x ()

-- The whole set is in every power set.
x∈𝒫x : x ∈ 𝒫 x
x∈𝒫x i = i

𝟙 : 𝕍  -- the singleton set
𝟙 = 𝒫 ∅

𝟙-singleton : (x ∈ 𝟙) -> (x ≡ ∅)
𝟙-singleton s = Extensional \ z -> false-≡ s

-- 𝟙 is not ∅
∅≢𝟙 : ∅ ≢ 𝟙
∅≢𝟙 eq = equal-equiv {P = ∅ ∈ 𝟙} {Q = ∅ ∈ ∅} P≡Q (x∈𝒫x {x = ∅} {z = ∅})
    where
        P≡Q : ∅ ∈ 𝟙 ≡ ∅ ∈ ∅
        P≡Q = cong (\ z -> ∅ ∈ z) (symm eq)

𝟚 : 𝕍  -- The boolean set
𝟚 = 𝒫 𝟙

𝟚-boolean : (x ∈ 𝟚) -> (x ≡ ∅) ⊎ (x ≡ 𝟙)
𝟚-boolean {x = x} x∈𝟚
    -- We see if x is empty.
    with truth {lzero} (∀ y -> (y ∈ x) -> ⊥)
... | inj₁ is-empty = inj₁ (∅-unique  -- x has no elements, then by extensionality
                                      -- we just need to prove that x is empty.
    \ y -> false-≡                    -- If y is in x,
    \ y∈x -> ≡-true is-empty y y∈x )  -- By definition, we get contradiction.
... | inj₂ non-empty = inj₂ (Extensional  -- x is non-empty, we invoke extensionality.
    \ z -> equiv-equal
        [ x∈𝟚 , z∈x z ])
    where
        z∈x : ∀ z -> z ⊆ ∅ -> z ∈ x
        z∈x z z⊆∅ rewrite x⊆∅-≡ {z} z⊆∅
            with choice-safe (≡-false non-empty)
        ... | exists a a∈x rewrite symm (∅-unique {y = a} (\ z -> false-≡ (x∈𝟚 a∈x)))
            = a∈x

postulate
    ⋃ : 𝕍 -> 𝕍
    Union : (x : 𝕍) -> z ∈ ⋃ x ≡ ∃[ y ∈ 𝕍 ] (z ∈ y ∧ y ∈ x)
{-# REWRITE Union #-}

-- Union and powerset are "sort of" inverse to each other.
-- ⋃ (𝒫 x) = x, but 𝒫 (⋃ x) ⊇ x.
⋃-𝒫 : ⋃ (𝒫 x) ≡ x
⋃-𝒫 {x = x} = Extensional
    \ z -> equiv-equal
        [ zig , zag ]
    where
        zig : z ∈ ⋃ (𝒫 x) -> z ∈ x
        zig (exists a [ z∈a , a⊆x ]) = a⊆x z∈a
        zag : z ∈ x -> z ∈ ⋃ (𝒫 x)
        zag i = exists x [ i , idP ]

𝒫-⋃ : x ⊆ 𝒫 (⋃ x)
𝒫-⋃ z∈x y∈z = exists _ [ y∈z , z∈x ]

⋃∅≡∅ : ⋃ ∅ ≡ ∅
⋃∅≡∅ = Extensional
    \ _ -> false-≡
    \ { (exists _ ()) }

-- These two are direct application of the almost-inverse relation.
⋃𝟙≡∅ : ⋃ 𝟙 ≡ ∅
⋃𝟙≡∅ = ⋃-𝒫
⋃𝟚≡𝟙 : ⋃ 𝟚 ≡ 𝟙
⋃𝟚≡𝟙 = ⋃-𝒫

-- Since Agda wants the syntax { } and ⦃ ⦄ very much, we will avoid this.
-- Instead, we use ⟦ ⟧ as set builders.
postulate
    Comprehension : (x : 𝕍) -> (P : 𝕍 -> Prop) -> 𝕍
    Specification : (P : 𝕍 -> Prop)
        -> z ∈ Comprehension x P ≡ (z ∈ x ∧ P z)
{-# REWRITE Specification #-}
syntax Comprehension x (\ y -> P) = ⟦ y ∈ x ∥ P ⟧
infix 6 Comprehension

module Intersection where
    abstract
        -- Now intersections can be defined.
        ⋂ : 𝕍 -> 𝕍
        ⋂ x = ⟦ y ∈ ⋃ x ∥ (∀ w -> w ∈ x -> y ∈ w) ⟧
        -- We can't prove much interesting stuff about intersections yet.

        Intersection-definition : ⋂ x ≡ ⟦ y ∈ ⋃ x ∥ (∀ w -> w ∈ x -> y ∈ w) ⟧
        Intersection-definition = refl

        Intersection : (x y : 𝕍) -> y ∈ ⋂ x ≡
            (∃[ z ∈ 𝕍 ] (y ∈ z ∧ z ∈ x)) ∧ (∀ w -> w ∈ x -> y ∈ w)
        Intersection x y = refl
open Intersection public
{-# REWRITE Intersection #-}

module Singleton where
    abstract
        -- We can also define singleton sets now.
        ⟦_⟧ : 𝕍 -> 𝕍
        ⟦ x ⟧ = ⟦ w ∈ 𝒫 x ∥ w ≗ x ⟧

        -- Singletons are really singletons.
        ⟦_⟧-singleton : (x : 𝕍) {y : 𝕍} -> y ∈ ⟦ x ⟧ -> y ≡ x
        ⟦ x ⟧-singleton [ y⊆x , y≗x ] = ≗-≡ y≗x

        Singleton : (y ∈ ⟦ x ⟧) ≡ (y ≗ x)
        Singleton = equiv-equal [ π₂ , (\ { refl𝕍 -> [ idP , refl𝕍 ]}) ]
open Singleton public
{-# REWRITE Singleton #-}

-- 𝟙 is equivalently defined as a singleton.
𝟙≡⟦∅⟧ : 𝟙 ≡ ⟦ ∅ ⟧
𝟙≡⟦∅⟧ = Extensional
    \ z -> equiv-equal
    [ (\ u -> ≡-≗ (x⊆∅-≡ u)) , (\ { refl𝕍 -> idP }) ]

-- To unwrap a singleton, take the union.
⋃⟦x⟧ : ⋃ ⟦ x ⟧ ≡ x
⋃⟦x⟧ = Extensional
    \ z -> equiv-equal
    [ (\ { (exists _ [ z∈x , refl𝕍 ]) -> z∈x }) , (\ z∈x -> exists _ [ z∈x , refl𝕍 ]) ]

postulate
    Image : (x : 𝕍) {_↦_ : 𝕍 -> 𝕍 -> Prop} -> (∀ y -> y ∈ x -> ∃![ z ∈ 𝕍 ] y ↦ z) -> 𝕍
    Replacement : (x : 𝕍) {_↦_ : 𝕍 -> 𝕍 -> Prop}
        -> (unique : ∀ y -> y ∈ x -> ∃![ z ∈ 𝕍 ] y ↦ z)
        -> (∀ z -> z ∈ Image x unique ≡ ∃[ y ∈ 𝕍 ] (y ∈ x ∧ y ↦ z))
{-# REWRITE Replacement #-}

-- Now we can *really* start to make sets.
-- For a start, we prove Pairing, i.e. {a, b} is a set
-- We first need to get a predicate to replace.
private  -- Start a private block since we don't want to contaminate the namespace
    Pair : 𝕍 -> 𝕍 -> 𝕍 -> 𝕍 -> Prop
    Pair a b x y = (x ≗ ∅ ∧ y ≗ a) ∨ (x ≗ 𝟙 ∧ y ≗ b)
    -- Now let's prove that it is indeed a map!
    Pair-unique : ∀ a b -> ∀ y -> y ∈ 𝟚 -> ∃![ z ∈ 𝕍 ] (Pair a b y z)
    Pair-unique a b y y∈𝟚 with 𝟚-boolean {x = y} y∈𝟚
    ... | inj₁ refl = exists-unique a \ w ->
        \ { pairing -> ≗-≡ (w≗a w pairing) }
        where
            w≗a : ∀ w -> (∅ ≗ ∅) ∧ (w ≗ a) ∨ (∅ ≗ 𝟙) ∧ (w ≗ b) -> w ≗ a
            w≗a w (ι₁ left) = π₂ left
            w≗a w (ι₂ [ ∅≗𝟙 , _ ]) = ex-falso (∅≢𝟙 (≗-≡ ∅≗𝟙))
    ... | inj₂ refl = exists-unique b \ w ->
        \ { pairing -> ≗-≡ (w≗b w pairing) }
        where
            w≗b : ∀ w -> (𝟙 ≗ ∅) ∧ (w ≗ a) ∨ (𝟙 ≗ 𝟙) ∧ (w ≗ b) -> w ≗ b
            w≗b w (ι₂ right) = π₂ right
            w≗b w (ι₁ [ 𝟙≗∅ , _ ]) = ex-falso (∅≢𝟙 (symm (≗-≡ 𝟙≗∅)))

module Pairing where
    abstract
        ⟨_,_⟩ : 𝕍 -> 𝕍 -> 𝕍
        ⟨ x , y ⟩ = Image 𝟚 (Pair-unique x y)
        Pair-definition : ⟨ x , y ⟩ ≡ Image 𝟚 (Pair-unique x y)
        Pair-definition = refl

        private
            Pairing-> : z ∈ ⟨ x , y ⟩ -> (z ≗ x) ∨ (z ≗ y)
            Pairing-> (exists a [ a∈𝟚 , pairing ]) with 𝟚-boolean {x = a} a∈𝟚
            Pairing-> (exists ∅ [ a∈𝟚 , ι₁ [ _ , z≗x ] ]) | inj₁ refl = ι₁ z≗x
            Pairing-> (exists ∅ [ a∈𝟚 , ι₂ [ ∅≗𝟙 , _ ] ]) | inj₁ refl = ex-falso (∅≢𝟙 (≗-≡ ∅≗𝟙))
            Pairing-> (exists 𝟙 [ a∈𝟚 , ι₁ [ 𝟙≗∅ , _ ] ]) | inj₂ refl = ex-falso (∅≢𝟙 (symm (≗-≡ 𝟙≗∅)))
            Pairing-> (exists 𝟙 [ a∈𝟚 , ι₂ [ _ , z≗y ] ]) | inj₂ refl = ι₂ z≗y

            Pairing<- : (z ≗ x) ∨ (z ≗ y) -> z ∈ ⟨ x , y ⟩
            Pairing<- (ι₁ refl𝕍)
                = exists ∅ [ ex-falso , ι₁ [ refl𝕍 , refl𝕍 ] ]
            Pairing<- (ι₂ refl𝕍)
                = exists 𝟙 [ idP , ι₂ [ refl𝕍 , refl𝕍 ] ]
        
        Pairing : z ∈ ⟨ x , y ⟩ ≡ (z ≗ x) ∨ (z ≗ y)
        Pairing = equiv-equal [ Pairing-> , Pairing<- ]
open Pairing public

{-# REWRITE Pairing #-}

Pairing-≡ : z ∈ ⟨ x , y ⟩ -> (z ≡ x) ⊎ (z ≡ y)
Pairing-≡ {z = z} {x = x} {y = y} i with ∨-oracle (true-≡ i)
... | inj₁ l = inj₁ (≗-≡ (≡-true l))
... | inj₂ r = inj₂ (≗-≡ (≡-true r))

-- For example, 𝟚 is equal to ⟨ ∅ , 𝟙 ⟩.
𝟚≡⟨∅,𝟙⟩ : 𝟚 ≡ ⟨ ∅ , 𝟙 ⟩
𝟚≡⟨∅,𝟙⟩ = Extensional \ z ->
    equiv-equal [ zig z , zag z ]
    where
        zig : ∀ z -> z ∈ 𝟚 -> z ∈ ⟨ ∅ , 𝟙 ⟩
        zig z i with 𝟚-boolean {x = z} i
        ... | inj₁ refl = ι₁ refl𝕍
        ... | inj₂ refl = ι₂ refl𝕍
        zag : ∀ z -> z ∈ ⟨ ∅ , 𝟙 ⟩ -> z ∈ 𝟚
        zag .∅ (ι₁ refl𝕍) ()
        zag .(𝒫 ∅) (ι₂ refl𝕍) i = i

-- Pairs are unordered.
Pair-unordered : ∀ x y -> ⟨ x , y ⟩ ≡ ⟨ y , x ⟩
Pair-unordered x y = Extensional \ z ->
    equiv-equal [ zig x y z , zig y x z ]
    where
        zig : ∀ x y z -> z ∈ ⟨ x , y ⟩ -> z ∈ ⟨ y , x ⟩
        zig x y .x (ι₁ refl𝕍) = ι₂ refl𝕍
        zig x y .y (ι₂ refl𝕍) = ι₁ refl𝕍

-- We have a criterion for pair equality.
-- To prove that cleanly, we first develop some tools.
private
    Pair-equal-left : ∀ x y z w -> ⟨ x , y ⟩ ≡ ⟨ z , w ⟩ -> (x ≗ z) ∨ (x ≗ w)
    Pair-equal-left x y z w eq 
        = equal-equiv (Extensional-converse eq x) (ι₁ refl𝕍)

    Pair-equal-right : ∀ x y z w -> ⟨ x , y ⟩ ≡ ⟨ z , w ⟩ -> (y ≗ w) ∨ (y ≗ z)
    Pair-equal-right x y z w eq
        rewrite Pair-unordered x y rewrite Pair-unordered z w
            = Pair-equal-left _ _ _ _ eq

    Pair-equal-equiv : ∀ x y z w -> ⟨ x , y ⟩ ≡ ⟨ z , w ⟩
        -> (x ≗ z) ∧ (y ≗ w) ∨ (x ≗ w) ∧ (y ≗ z)
    Pair-equal-equiv x y z w eq
        with Pair-equal-left _ _ _ _ eq
        | Pair-equal-right _ _ _ _ eq
    ... | ι₁ xz | ι₁ yw = ι₁ [ xz , yw ]
    ... | ι₂ xw | ι₂ yz = ι₂ [ xw , yz ]
    ... | ι₁ refl𝕍 | ι₂ refl𝕍 = ι₁ [ refl𝕍 , xw ]
        where
            xw : x ≗ w
            xw with P∨P _
                (equal-equiv
                    (symm (Extensional-converse eq w))
                        (ι₂ refl𝕍))
            ... | refl𝕍 = refl𝕍
    ... | ι₂ refl𝕍 | ι₁ refl𝕍 = ι₂ [ refl𝕍 , yz ]
        where
            yz : y ≗ z
            yz with P∨P _
                (equal-equiv
                    (symm (Extensional-converse eq z))
                        (ι₁ refl𝕍))
            ... | refl𝕍 = refl𝕍

Pair-equal : ⟨ x , y ⟩ ≡ ⟨ z , w ⟩ -> (x ≡ z) * (y ≡ w) ⊎ (x ≡ w) * (y ≡ z)
Pair-equal {x} {y} {z} {w} eq with ∨-oracle (true-≡ (Pair-equal-equiv x y z w eq))
... | inj₁ l = let (ll , lr) = ∧-oracle l in inj₁ (≗-≡ (≡-true ll) , ≗-≡ (≡-true lr))
... | inj₂ r = let (rl , rr) = ∧-oracle r in inj₂ (≗-≡ (≡-true rl) , ≗-≡ (≡-true rr))

-- Singletons can be alternatively defined as unordered pairs.
singleton-pair : ⟦ x ⟧ ≡ ⟨ x , x ⟩
singleton-pair {x} = Extensional \ z -> equiv-equal
    (solve 1 (\ P -> P <=> P ||| P) (z ≗ x))

module Kuratowski where
    abstract
        -- Then, we can have Kuratowski pairs.
        -- This construction cleverly avoids the need for Regularity.
        ⟪_,_⟫ : 𝕍 -> 𝕍 -> 𝕍
        ⟪ x , y ⟫ = ⟨ ⟦ x ⟧ , ⟨ x , y ⟩ ⟩

        -- We can prove that Kuratowski pairs are indeed ordered.
        -- A lemma first
        private
            Pair-zig : ∀ x y z w -> (⟨ x , x ⟩ ≡ ⟨ z , z ⟩) * (⟨ x , y ⟩ ≡ ⟨ z , w ⟩)
                -> (x ≡ z) * (y ≡ w)
            Pair-zig x y z w (eq₁ , eq₂) with Pair-equal eq₁ | Pair-equal eq₂
            ... | inj₁ (refl , refl) | inj₁ (refl , refl) = refl , refl
            ... | inj₁ (refl , refl) | inj₂ (refl , refl) = refl , refl
            ... | inj₂ (refl , refl) | inj₁ (refl , refl) = refl , refl
            ... | inj₂ (refl , refl) | inj₂ (refl , refl) = refl , refl

            Pair-zag : ∀ x y z w -> (⟨ x , x ⟩ ≡ ⟨ z , w ⟩) * (⟨ x , y ⟩ ≡ ⟨ z , z ⟩)
                -> (x ≡ z) * (y ≡ w)
            Pair-zag x y z w (eq₁ , eq₂) with Pair-equal eq₁ | Pair-equal eq₂
            ... | inj₁ (refl , refl) | inj₁ (refl , refl) = refl , refl
            ... | inj₁ (refl , refl) | inj₂ (refl , refl) = refl , refl
            ... | inj₂ (refl , refl) | inj₁ (refl , refl) = refl , refl
            ... | inj₂ (refl , refl) | inj₂ (refl , refl) = refl , refl

        Pair-ordered : ⟪ x , y ⟫ ≡ ⟪ z , w ⟫ -> (x ≡ z) * (y ≡ w)
        Pair-ordered {x} {y} {z} {w} eq
            rewrite singleton-pair {x} rewrite singleton-pair {z}
            with Pair-equal eq
        ... | inj₁ eq₁ = Pair-zig x y z w eq₁
        ... | inj₂ eq₂ = Pair-zag x y z w eq₂

-- Now we can form pairwise unions and intersections.
module Pairwise-Union where
    infixl 15 _∪_
    abstract
        _∪_ : 𝕍 -> 𝕍 -> 𝕍
        x ∪ y = ⋃ ⟨ x , y ⟩

        private
            Pairwise-Union-> : (x y z : 𝕍)
                -> z ∈ (x ∪ y) -> (z ∈ x) ∨ (z ∈ y)
            Pairwise-Union-> x y z (exists .x [ z∈x , ι₁ refl𝕍 ]) = ι₁ z∈x
            Pairwise-Union-> x y z (exists .y [ z∈y , ι₂ refl𝕍 ]) = ι₂ z∈y

            Pairwise-Union<- : (x y z : 𝕍)
                -> (z ∈ x) ∨ (z ∈ y) -> z ∈ (x ∪ y)
            Pairwise-Union<- x y z (ι₁ z∈x) = exists x [ z∈x , ι₁ refl𝕍 ]
            Pairwise-Union<- x y z (ι₂ z∈y) = exists y [ z∈y , ι₂ refl𝕍 ]

        Pairwise-Union : (x y z : 𝕍)
            -> z ∈ (x ∪ y) ≡ (z ∈ x) ∨ (z ∈ y)
        Pairwise-Union x y z = equiv-equal [ Pairwise-Union-> x y z , Pairwise-Union<- x y z ]
open Pairwise-Union public
{-# REWRITE Pairwise-Union #-}

-- We have completely analogous development for intersections.
module Pairwise-Intersection where
    abstract
        infixl 16 _∩_
        _∩_ : 𝕍 -> 𝕍 -> 𝕍
        x ∩ y = ⋂ ⟨ x , y ⟩
        private
            Pairwise-Intersection-> : (x y z : 𝕍)
                -> z ∈ (x ∩ y) -> (z ∈ x) ∧ (z ∈ y)
            Pairwise-Intersection-> x y z [ z∈x , z∈y ] =
                [ z∈y x (ι₁ refl𝕍) , z∈y y (ι₂ refl𝕍) ]

            Pairwise-Intersection<- : (x y z : 𝕍)
                -> (z ∈ x) ∧ (z ∈ y) -> z ∈ (x ∩ y)
            Pairwise-Intersection<- x y z [ z∈x , z∈y ] =
                [ exists x [ z∈x , ι₁ refl𝕍 ] ,
                (\ { w (ι₁ refl𝕍) -> z∈x ;
                    w (ι₂ refl𝕍) -> z∈y }) ]

        Pairwise-Intersection : (x y z : 𝕍)
            -> z ∈ (x ∩ y) ≡ (z ∈ x) ∧ (z ∈ y)
        Pairwise-Intersection x y z = equiv-equal [ Pairwise-Intersection-> x y z , Pairwise-Intersection<- x y z ]
open Pairwise-Intersection public
{-# REWRITE Pairwise-Intersection #-}

-- Regularity
postulate
    Regularity : ∀ {a} -> (∀ x -> x ∈ a -> ∃[ y ∈ 𝕍 ] (y ∈ a ∧ y ∈ x)) -> a ≡ ∅

-- A set cannot contain itself.
x∉x : ¬ (x ∈ x)
x∉x {x} x∈x = equal-equiv (Extensional-converse ⟦x⟧≡∅ x) refl𝕍
    where
        ⟦x⟧≡∅ : ⟦ x ⟧ ≡ ∅
        ⟦x⟧≡∅ = Regularity \ { _ refl𝕍 -> exists x [ refl𝕍 , x∈x ] }

-- Two sets cannot mutually contain each other.
-- This pattern can be continued by induction, but we do not persue this here.
∉-cycle : (x ∈ y) -> (y ∈ x) -> ⊥ {lzero}
∉-cycle {x} {y} x∈y y∈x = equal-equiv (Extensional-converse ⟨x,y⟩≡∅ x) (ι₁ refl𝕍)
    where
        ⟨x,y⟩≡∅ : ⟨ x , y ⟩ ≡ ∅
        ⟨x,y⟩≡∅ = Regularity \ { w (ι₁ refl𝕍) -> exists y [ ι₂ refl𝕍 , y∈x ] ;
                                 w (ι₂ refl𝕍) -> exists x [ ι₁ refl𝕍 , x∈y ] }

-- A set cannot contain every set.
𝕍-proper : ¬ (∀ y -> y ∈ x)
𝕍-proper {x} univ = x∉x {x} (univ x)
-- The consequences of Regularity is profound. So we will not explore them too soon.

-- Infinity
-- Since we have Agda, let's define the set ω in a really neat way.

-- To be consistent, we use 𝟘 as an alias for the empty set.
𝟘 : 𝕍
𝟘 = ∅

infixl 21 _⁺
_⁺ : 𝕍 -> 𝕍  -- defines the successor
x ⁺ = x ∪ ⟦ x ⟧

-- 𝟙 is a successor.
𝟙≡∅⁺ : 𝟙 ≡ ∅ ⁺
𝟙≡∅⁺ = Extensional zigzag
    where
        zigzag : ∀ z -> (z ⊆ ∅) ≡ ⊥ ∨ (z ≗ ∅)
        zigzag z rewrite (x⊆∅ {z}) = equiv-equal [ ι₂ , (\ { (ι₂ x) -> x }) ]

-- 𝟚 is also a successor.
𝟚≡𝟙⁺ : 𝟚 ≡ 𝟙 ⁺
𝟚≡𝟙⁺ = Extensional \ z -> equiv-equal [ zig , zag ]
    where
        zig : z ∈ 𝟚 -> (z ⊆ ∅) ∨ (z ≗ 𝟙)
        zig {z} z∈𝟚 with 𝟚-boolean {z} z∈𝟚
        ... | inj₁ refl = ι₁ idP
        ... | inj₂ refl = ι₂ refl𝕍
        zag : (z ⊆ ∅) ∨ (z ≗ 𝟙) -> z ∈ 𝟚
        zag (ι₁ z⊆∅) w∈z _ = z⊆∅ w∈z
        zag (ι₂ refl𝕍) = idP

-- The successor operation is injective.
injective-⁺ : ∀ x y -> x ⁺ ≡ y ⁺ -> x ≡ y
injective-⁺ x y eq = Extensional \ z -> equiv-equal [ zig , zag ]
    where
        ext : (w : 𝕍) -> w ∈ x ∨ (w ≗ x) ≡ w ∈ y ∨ (w ≗ y)
        ext = Extensional-converse eq
        zig : z ∈ x -> z ∈ y
        zig z∈x with equal-equiv (ext _) (ι₁ z∈x) | equal-equiv (ext x) (ι₂ refl𝕍)
        ... | ι₁ z∈y | _ = z∈y
        ... | ι₂ refl𝕍 | ι₁ x∈y = ex-falso
            (∉-cycle {y} {x} z∈x x∈y)  -- Since we instantiated a refl𝕍, z∈x is actually y∈x.
        ... | ι₂ refl𝕍 | ι₂ refl𝕍 = z∈x
        zag : z ∈ y -> z ∈ x  -- I didn't bother reusing zig, maybe later..
        zag z∈y with equal-equiv (symm (ext _)) (ι₁ z∈y) | equal-equiv (symm (ext y)) (ι₂ refl𝕍)
        ... | ι₁ z∈x | _ = z∈x
        ... | ι₂ refl𝕍 | ι₁ y∈x = ex-falso
            (∉-cycle {x} {y} z∈y y∈x)
        ... | ι₂ refl𝕍 | ι₂ refl𝕍 = z∈y

x⁺≢∅ : ∀ x -> (x ⁺ ≡ ∅) -> ⊥ {lzero}
x⁺≢∅ x eq = equal-equiv (Extensional-converse eq x) (ι₂ refl𝕍)

-- The ord function embeds Nat into ω.
ord : Nat -> 𝕍
ord 0 = 𝟘
ord (succ n) = (ord n) ⁺

injective-ord : ∀ n m -> ord n ≡ ord m -> n ≡ m
injective-ord zero zero eq = refl
injective-ord zero (succ m) eq = magic (x⁺≢∅ (ord m) (symm eq))
injective-ord (succ n) zero eq = magic (x⁺≢∅ (ord n) eq)
injective-ord (succ n) (succ m) eq
    rewrite injective-ord n m (injective-⁺ (ord n) (ord m) eq) = refl

-- We now state the axiom of Infinity.
postulate
    ω : 𝕍
    Infinity : ∀ n -> ord n ∈ ω
    count : ∀ x -> .(x ∈ ω) -> Nat
    -- ord and count are inverses.
    ord-count : ∀ x i -> ord (count x i) ≡ x

-- From this, we can prove the other side of the inverse.
count-ord : ∀ n i -> count (ord n) i ≡ n
count-ord n _ = injective-ord _ _ (ord-count _ _)

{-# REWRITE ord-count count-ord #-}

-- The axiom of choice needs more machinery to state.
-- Therefore, we postpone it.
