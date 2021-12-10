{-# OPTIONS --prop --rewriting #-}

module funrel where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import logic
open import ZF
open _∧_

private variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ' ℓ'' : Level
    x y z w : 𝕍

module Cartesian where
    abstract
        _×_ : 𝕍 -> 𝕍 -> 𝕍
        x × y = ⟦ z ∈ 𝒫 (𝒫 (x ∪ y)) ∥
            ∃[ u ∈ 𝕍 ] ∃[ v ∈ 𝕍 ]
                (u ∈ x) ∧ (v ∈ y) ∧ (z ≗ ⟪ u , v ⟫) ⟧
        infixl 13 _×_

        Cartesian-definition : x × y ≡ ⟦ z ∈ 𝒫 (𝒫 (x ∪ y)) ∥
            ∃[ u ∈ 𝕍 ] ∃[ v ∈ 𝕍 ]
                (u ∈ x) ∧ (v ∈ y) ∧ (z ≗ ⟪ u , v ⟫) ⟧
        Cartesian-definition = refl

        -- Only pairs are elements of a cartesian product.
        Cartesian-elim : (x y z : 𝕍) -> z ∈ (x × y)
            -> ∃[ u ∈ 𝕍 ] ∃[ v ∈ 𝕍 ] (u ∈ x) ∧ (v ∈ y) ∧ (z ≗ ⟪ u , v ⟫)
        Cartesian-elim x y z = π₂

        Cartesian-intro : (x y u v : 𝕍)
            -> u ∈ x -> v ∈ y
            -> ⟪ u , v ⟫ ∈ (x × y)
        Cartesian-intro x y u v u∈x v∈y
            = [ ⟪u,v⟫∈𝒫𝒫x∪y {x = x} {y = y} u∈x v∈y {_} ,
                exists u (exists v [ [ u∈x , v∈y ] , refl𝕍 ]) ]

        -- This alternative reduction rule eliminates the arbitrarily chosen
        -- "z ∈ 𝒫 (𝒫 (x ∪ y))" condition.
        Cartesian : (x y z : 𝕍) -> z ∈ (x × y)
            ≡ ∃[ u ∈ 𝕍 ] ∃[ v ∈ 𝕍 ] (u ∈ x) ∧ (v ∈ y) ∧ (z ≗ ⟪ u , v ⟫)
        Cartesian x y z = equiv-equal
            [ Cartesian-elim x y z ,
            (\ { (exists u (exists v [ [ u∈x , v∈y ] , refl𝕍 ]))
                -> Cartesian-intro x y u v u∈x v∈y}) ]
open Cartesian public
{-# REWRITE Cartesian #-}

-- Relations and functions don't have intrinsic domain/codomains.
isRel : 𝕍 -> Prop
isRel R = ∀ x -> x ∈ R -> ∃[ u ∈ 𝕍 ] ∃[ v ∈ 𝕍 ] x ≗ ⟪ u , v ⟫

_⦅_⦆_ : 𝕍 -> 𝕍 -> 𝕍 -> Prop
x ⦅ R ⦆ y = ⟪ x , y ⟫ ∈ R

-- The identity relation is a relation.
Id-isRel : isRel (Id x)
Id-isRel .(⟪ w , w ⟫) (exists w [ w∈x , refl𝕍 ])
    = exists w (exists w refl𝕍)

module Relation where
    -- We provide a relation space with domain and range.
    REL : 𝕍 -> 𝕍 -> 𝕍
    REL x y = 𝒫 (x × y)

isFun : 𝕍 -> Prop
isFun R = isRel R ∧
    (∀ x -> ∃[ y ∈ 𝕍 ] ⟪ x , y ⟫ ∈ R -> ∃![ y ∈ 𝕍 ] ⟪ x , y ⟫ ∈ R )
