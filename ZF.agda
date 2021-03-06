{-# OPTIONS --prop --rewriting #-}

module ZF where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import logic
open _β§_

postulate
    -- We postulate a universe of sets, and a _β_ relation between them.
    π : Set
    _β_ : π -> π -> Prop
{-# INJECTIVE _β_ #-}
infix 20 _β_

private variable
    β ββ ββ ββ ββ ββ ββ ββ ββ β' β'' : Level
    x y z w : π  -- These will range over sets unless noted otherwise.

-- A propositional equality for convenience.
-- We avoid the use of this as much as possible.
data _β_ : π -> π -> Prop where
    reflπ : x β x

symmP : x β y -> y β x
symmP reflπ = reflπ

-- The _β_ relation is extensional. The elements of (_β x) uniquely defines x.
postulate
    Extensional : (β z -> z β x β‘ z β y) -> x β‘ y
-- The converse holds by Leibniz's law.
Extensional-converse : x β‘ y -> (β z -> z β x β‘ z β y)
Extensional-converse refl z = refl

-- Extensionality flattens the propositional equality into the regular one.
β-β‘ : x β y -> x β‘ y
β-β‘ eq = Extensional (\ z -> equiv-equal (ex eq z))
    where
        ex : x β y -> (z : π) -> (z β x -> z β y) β§ (z β y -> z β x)
        ex reflπ z = [ idP , idP ]

β‘-β : x β‘ y -> x β y
β‘-β refl = reflπ

_β_ : {A : Set β} (x y : π) -> (x β‘ y) β (x β‘ y -> A)
x β y with truth (x β y)
... | injβ eq = injβ (β-β‘ (β‘-true eq))
... | injβ neq = injβ \ { refl -> magic (β‘-false neq reflπ) }

-- We postulate the existence of an empty set, i.e. a set with no elements
-- This is actually redundant from the other axioms, but we keep it for
-- aesthetic considerations.
postulate
    β : π
    β-empty : x β β β‘ β₯

{-# REWRITE β-empty #-}

-- From extensionality, we immediately obtain that the empty set is unique.
β-unique : (β x -> x β y β‘ β₯) -> y β‘ β
β-unique = Extensional  -- Well, that's literally immediate.

-- Conversely, every non-empty set has an element.
-- This crucially depends on the principle of excluded middle.
non-empty : (x β’ β) -> β[ y β π ] y β x
non-empty {x} neq with Ξ΅[ y β π ] y β x
... | ΞΉβ no = ex-falso   -- Case 1 : y contains no element,
        (neq                  -- y is not the empty set (assumption), but
        (β-unique \ y ->      -- y is the empty set, since
            false-β‘ (no y)))  -- y is contains no element. (assumption)
                              -- Contradiction!
... | ΞΉβ yes = yes       -- Case 2 : y contains an element, QED.

-- We define the subset relation.
_β_ : π -> π -> Prop
x β y = β {z} -> z β x -> z β y

xββ-β‘ : x β β -> x β‘ β
xββ-β‘ s = β-unique \ y -> false-β‘ s

xββ : (x β β) β‘ (x β β)
xββ = equiv-equal [ (\ xββ -> β‘-β (xββ-β‘ xββ)) , (\{ reflπ -> idP }) ]

-- We postulate the existence of power sets.
postulate
    π« : π -> π
    Power : (x : π)
        -> β z -> z β π« x β‘ z β x
{-# REWRITE Power #-}

-- The empty set is in every power set.
ββπ«x : β β π« x
ββπ«x ()

-- The whole set is in every power set.
xβπ«x : x β π« x
xβπ«x i = i

π : π  -- the singleton set
π = π« β

π-singleton : (x β π) -> (x β‘ β)
π-singleton s = Extensional \ z -> false-β‘ s

-- π is not β
ββ’π : β β’ π
ββ’π eq = equal-equiv {P = β β π} {Q = β β β} Pβ‘Q (xβπ«x {x = β} {z = β})
    where
        Pβ‘Q : β β π β‘ β β β
        Pβ‘Q = cong (\ z -> β β z) (symm eq)

π : π  -- The boolean set
π = π« π

π-boolean : (x β π) -> (x β‘ β) β (x β‘ π)
π-boolean {x = x} xβπ
    -- We see if x is empty.
    with truth {lzero} (β y -> (y β x) -> β₯)
... | injβ is-empty = injβ (β-unique  -- x has no elements, then by extensionality
                                      -- we just need to prove that x is empty.
    \ y -> false-β‘                    -- If y is in x,
    \ yβx -> β‘-true is-empty y yβx )  -- By definition, we get contradiction.
... | injβ non-empty = injβ (Extensional  -- x is non-empty, we invoke extensionality.
    \ z -> equiv-equal
        [ xβπ , zβx z ])
    where
        zβx : β z -> z β β -> z β x
        zβx z zββ rewrite xββ-β‘ {z} zββ
            with choice-safe (β‘-false non-empty)
        ... | exists a aβx rewrite symm (β-unique {y = a} (\ z -> false-β‘ (xβπ aβx)))
            = aβx

postulate
    β : π -> π
    Union : (x : π) -> z β β x β‘ β[ y β π ] z β y β§ y β x
{-# REWRITE Union #-}

-- Union and powerset are "sort of" inverse to each other.
-- β (π« x) = x, but π« (β x) β x.
β-π« : β (π« x) β‘ x
β-π« {x = x} = Extensional
    \ z -> equiv-equal
        [ zig , zag ]
    where
        zig : z β β (π« x) -> z β x
        zig (exists a [ zβa , aβx ]) = aβx zβa
        zag : z β x -> z β β (π« x)
        zag i = exists x [ i , idP ]

π«-β : x β π« (β x)
π«-β zβx yβz = exists _ [ yβz , zβx ]

βββ‘β : β β β‘ β
βββ‘β = Extensional
    \ _ -> false-β‘
    \ { (exists _ ()) }

-- These two are direct application of the almost-inverse relation.
βπβ‘β : β π β‘ β
βπβ‘β = β-π«
βπβ‘π : β π β‘ π
βπβ‘π = β-π«

-- Since Agda wants the syntax { } and β¦ β¦ very much, we will avoid this.
-- Instead, we use β¦ β§ as set builders.
postulate
    Comprehension : (x : π) -> (P : π -> Prop) -> π
    Specification : (P : π -> Prop)
        -> z β Comprehension x P β‘ (z β x β§ P z)
{-# REWRITE Specification #-}
syntax Comprehension x (\ y -> P) = β¦ y β x β₯ P β§
infix 6 Comprehension

module Intersection where
    abstract
        -- Now intersections can be defined.
        β : π -> π
        β x = β¦ y β β x β₯ (β w -> w β x -> y β w) β§
        -- We can't prove much interesting stuff about intersections yet.

        Intersection-definition : β x β‘ β¦ y β β x β₯ (β w -> w β x -> y β w) β§
        Intersection-definition = refl

        Intersection : (x y : π) -> y β β x β‘
            (β[ z β π ] y β z β§ z β x) β§ (β w -> w β x -> y β w)
        Intersection x y = refl
open Intersection public
{-# REWRITE Intersection #-}

module Singleton where
    abstract
        -- We can also define singleton sets now.
        β¦_β§ : π -> π
        β¦ x β§ = β¦ w β π« x β₯ w β x β§

        -- Singletons are really singletons.
        β¦_β§-singleton : (x : π) {y : π} -> y β β¦ x β§ -> y β‘ x
        β¦ x β§-singleton [ yβx , yβx ] = β-β‘ yβx

        Singleton : (y β β¦ x β§) β‘ (y β x)
        Singleton = equiv-equal [ Οβ , (\ { reflπ -> [ idP , reflπ ]}) ]
open Singleton public
{-# REWRITE Singleton #-}

-- π is equivalently defined as a singleton.
πβ‘β¦ββ§ : π β‘ β¦ β β§
πβ‘β¦ββ§ = Extensional
    \ z -> equiv-equal
    [ (\ u -> β‘-β (xββ-β‘ u)) , (\ { reflπ -> idP }) ]

-- To unwrap a singleton, take the union.
ββ¦xβ§ : β β¦ x β§ β‘ x
ββ¦xβ§ = Extensional
    \ z -> equiv-equal
    [ (\ { (exists _ [ zβx , reflπ ]) -> zβx }) , (\ zβx -> exists _ [ zβx , reflπ ]) ]

postulate
    Image : (π -> π) -> (π -> π)
    Replacement : (F : π -> π) (x : π)
        -> (β z -> z β Image F x β‘ β[ y β π ] y β x β§ F y β z)
{-# REWRITE Replacement #-}

-- Now we can *really* start to make sets.
-- For a start, we prove Pairing, i.e. {a, b} is a set.
private  -- Start a private block since we don't want to contaminate the namespace
    Pair : π -> π -> (π -> π)
    Pair a b x with truth (x β β)
    ... | injβ _ = a
    ... | _ with truth (x β π)
    ... | injβ _ = b
    ... | _ = β

    Pair-β : Pair x y β β‘ x
    Pair-β with truth (β β β)
    ... | injβ _ = refl
    ... | injβ eq = magic (equal-equiv eq reflπ)

    Pair-π : Pair x y π β‘ y
    Pair-π with truth (π β β)
    ... | injβ eq = magic (ββ’π (symm (β-β‘ (β‘-true eq))))
    ... | injβ _ with truth (π β π)
    ... | injβ _ = refl
    ... | injβ eq = magic (equal-equiv eq reflπ)

module Pairing where
    abstract
        β¨_,_β© : π -> π -> π
        β¨ x , y β© = Image (Pair x y) π
        Pair-definition : β¨ x , y β© β‘ Image (Pair x y) π
        Pair-definition = refl

        xββ¨x,yβ© : x β β¨ x , y β©
        xββ¨x,yβ© = exists β [ (\ i _ -> i) , β‘-β Pair-β ]

        yββ¨x,yβ© : y β β¨ x , y β©
        yββ¨x,yβ© = exists π [ idP , β‘-β Pair-π ]

        Pairing : z β β¨ x , y β© β‘ (z β x) β¨ (z β y)
        Pairing = equiv-equal [ zig , zag ]
            where
                zig : z β β¨ x , y β© -> (z β x) β¨ (z β y)
                zig {z} {x} {y} (exists b [ bβπ , eq ]) with π-boolean {b} bβπ
                ... | injβ refl = ΞΉβ (symmP
                    (equal-equiv (cong (_β z) Pair-β) eq))
                ... | injβ refl = ΞΉβ (symmP
                    (equal-equiv (cong (_β z) Pair-π) eq))
                zag : (z β x) β¨ (z β y) -> z β β¨ x , y β©
                zag (ΞΉβ reflπ) = xββ¨x,yβ©
                zag (ΞΉβ reflπ) = yββ¨x,yβ©
open Pairing public

{-# REWRITE Pairing #-}

Pairing-β‘ : z β β¨ x , y β© -> (z β‘ x) β (z β‘ y)
Pairing-β‘ {z = z} {x = x} {y = y} i with β¨-oracle (true-β‘ i)
... | injβ l = injβ (β-β‘ (β‘-true l))
... | injβ r = injβ (β-β‘ (β‘-true r))

-- For example, π is equal to β¨ β , π β©.
πβ‘β¨β,πβ© : π β‘ β¨ β , π β©
πβ‘β¨β,πβ© = Extensional \ z ->
    equiv-equal [ zig z , zag z ]
    where
        zig : β z -> z β π -> z β β¨ β , π β©
        zig z i with π-boolean {x = z} i
        ... | injβ refl = ΞΉβ reflπ
        ... | injβ refl = ΞΉβ reflπ
        zag : β z -> z β β¨ β , π β© -> z β π
        zag .β (ΞΉβ reflπ) ()
        zag .(π« β) (ΞΉβ reflπ) i = i

-- Pairs are unordered.
Pair-unordered : β x y -> β¨ x , y β© β‘ β¨ y , x β©
Pair-unordered x y = Extensional \ z ->
    equiv-equal [ zig x y z , zig y x z ]
    where
        zig : β x y z -> z β β¨ x , y β© -> z β β¨ y , x β©
        zig x y .x (ΞΉβ reflπ) = ΞΉβ reflπ
        zig x y .y (ΞΉβ reflπ) = ΞΉβ reflπ

-- We have a criterion for pair equality.
-- To prove that cleanly, we first develop some tools.
private
    Pair-equal-left : β x y z w -> β¨ x , y β© β‘ β¨ z , w β© -> (x β z) β¨ (x β w)
    Pair-equal-left x y z w eq 
        = equal-equiv (Extensional-converse eq x) (ΞΉβ reflπ)

    Pair-equal-right : β x y z w -> β¨ x , y β© β‘ β¨ z , w β© -> (y β w) β¨ (y β z)
    Pair-equal-right x y z w eq
        rewrite Pair-unordered x y rewrite Pair-unordered z w
            = Pair-equal-left _ _ _ _ eq

    Pair-equal-equiv : β x y z w -> β¨ x , y β© β‘ β¨ z , w β©
        -> (x β z) β§ (y β w) β¨ (x β w) β§ (y β z)
    Pair-equal-equiv x y z w eq
        with Pair-equal-left _ _ _ _ eq
        | Pair-equal-right _ _ _ _ eq
    ... | ΞΉβ xz | ΞΉβ yw = ΞΉβ [ xz , yw ]
    ... | ΞΉβ xw | ΞΉβ yz = ΞΉβ [ xw , yz ]
    ... | ΞΉβ reflπ | ΞΉβ reflπ = ΞΉβ [ reflπ , xw ]
        where
            xw : x β w
            xw with Pβ¨P _
                (equal-equiv
                    (symm (Extensional-converse eq w))
                        (ΞΉβ reflπ))
            ... | reflπ = reflπ
    ... | ΞΉβ reflπ | ΞΉβ reflπ = ΞΉβ [ reflπ , yz ]
        where
            yz : y β z
            yz with Pβ¨P _
                (equal-equiv
                    (symm (Extensional-converse eq z))
                        (ΞΉβ reflπ))
            ... | reflπ = reflπ

Pair-equal : β¨ x , y β© β‘ β¨ z , w β© -> (x β‘ z) * (y β‘ w) β (x β‘ w) * (y β‘ z)
Pair-equal {x} {y} {z} {w} eq with β¨-oracle (true-β‘ (Pair-equal-equiv x y z w eq))
... | injβ l = let (ll , lr) = β§-oracle l in injβ (β-β‘ (β‘-true ll) , β-β‘ (β‘-true lr))
... | injβ r = let (rl , rr) = β§-oracle r in injβ (β-β‘ (β‘-true rl) , β-β‘ (β‘-true rr))

-- Singletons can be alternatively defined as unordered pairs.
singleton-pair : β¦ x β§ β‘ β¨ x , x β©
singleton-pair {x} = Extensional \ z -> equiv-equal
    (solve 1 (\ P -> P <=> P ||| P) (z β x))

-- Now we can form pairwise unions and intersections.
module Pairwise-Union where
    infixl 15 _βͺ_
    abstract
        _βͺ_ : π -> π -> π
        x βͺ y = β β¨ x , y β©

        private
            Pairwise-Union-> : (x y z : π)
                -> z β (x βͺ y) -> (z β x) β¨ (z β y)
            Pairwise-Union-> x y z (exists .x [ zβx , ΞΉβ reflπ ]) = ΞΉβ zβx
            Pairwise-Union-> x y z (exists .y [ zβy , ΞΉβ reflπ ]) = ΞΉβ zβy

            Pairwise-Union<- : (x y z : π)
                -> (z β x) β¨ (z β y) -> z β (x βͺ y)
            Pairwise-Union<- x y z (ΞΉβ zβx) = exists x [ zβx , ΞΉβ reflπ ]
            Pairwise-Union<- x y z (ΞΉβ zβy) = exists y [ zβy , ΞΉβ reflπ ]

        Pairwise-Union : (x y z : π)
            -> z β (x βͺ y) β‘ (z β x) β¨ (z β y)
        Pairwise-Union x y z = equiv-equal [ Pairwise-Union-> x y z , Pairwise-Union<- x y z ]
open Pairwise-Union public
{-# REWRITE Pairwise-Union #-}

-- We have completely analogous development for intersections.
module Pairwise-Intersection where
    abstract
        infixl 16 _β©_
        _β©_ : π -> π -> π
        x β© y = β β¨ x , y β©
        private
            Pairwise-Intersection-> : (x y z : π)
                -> z β (x β© y) -> (z β x) β§ (z β y)
            Pairwise-Intersection-> x y z [ zβx , zβy ] =
                [ zβy x (ΞΉβ reflπ) , zβy y (ΞΉβ reflπ) ]

            Pairwise-Intersection<- : (x y z : π)
                -> (z β x) β§ (z β y) -> z β (x β© y)
            Pairwise-Intersection<- x y z [ zβx , zβy ] =
                [ exists x [ zβx , ΞΉβ reflπ ] ,
                (\ { w (ΞΉβ reflπ) -> zβx ;
                    w (ΞΉβ reflπ) -> zβy }) ]

        Pairwise-Intersection : (x y z : π)
            -> z β (x β© y) β‘ (z β x) β§ (z β y)
        Pairwise-Intersection x y z = equiv-equal [ Pairwise-Intersection-> x y z , Pairwise-Intersection<- x y z ]
open Pairwise-Intersection public
{-# REWRITE Pairwise-Intersection #-}

module Kuratowski where
    abstract
        -- We can also construct Kuratowski pairs.
        -- This construction cleverly avoids the need for Regularity.
        βͺ_,_β« : π -> π -> π
        βͺ x , y β« = β¨ β¦ x β§ , β¨ x , y β© β©

        -- We can prove that Kuratowski pairs are indeed ordered.
        -- A lemma first
        private
            Pair-zig : β x y z w -> (β¨ x , x β© β‘ β¨ z , z β©) * (β¨ x , y β© β‘ β¨ z , w β©)
                -> (x β‘ z) * (y β‘ w)
            Pair-zig x y z w (eqβ , eqβ) with Pair-equal eqβ | Pair-equal eqβ
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl

            Pair-zag : β x y z w -> (β¨ x , x β© β‘ β¨ z , w β©) * (β¨ x , y β© β‘ β¨ z , z β©)
                -> (x β‘ z) * (y β‘ w)
            Pair-zag x y z w (eqβ , eqβ) with Pair-equal eqβ | Pair-equal eqβ
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl
            ... | injβ (refl , refl) | injβ (refl , refl) = refl , refl

        Pair-ordered : βͺ x , y β« β‘ βͺ z , w β« -> (x β‘ z) * (y β‘ w)
        Pair-ordered {x} {y} {z} {w} eq
            rewrite singleton-pair {x} rewrite singleton-pair {z}
            with Pair-equal eq
        ... | injβ eqβ = Pair-zig x y z w eqβ
        ... | injβ eqβ = Pair-zag x y z w eqβ

        -- This lemma is needed for proving that Cartesian products exist.
        -- It concerns implementation details of Kuratowski pairs, so we
        -- put it in the abstract block.
        βͺu,vβ«βπ«π«xβͺy : β {u v}
            -> u β x -> v β y
            -> βͺ u , v β« β π« (π« (x βͺ y))
        βͺu,vβ«βπ«π«xβͺy uβx vβy (ΞΉβ reflπ) reflπ = ΞΉβ uβx
        βͺu,vβ«βπ«π«xβͺy uβx vβy (ΞΉβ reflπ) (ΞΉβ reflπ) = ΞΉβ uβx
        βͺu,vβ«βπ«π«xβͺy uβx vβy (ΞΉβ reflπ) (ΞΉβ reflπ) = ΞΉβ vβy
open Kuratowski public

-- We can also form the diagonal set, or the identity function.
Id : π -> π
Id y = Image (\ x -> βͺ x , x β«) y

-- Regularity
postulate
    Regularity : β {a} -> (β x -> x β a -> β[ y β π ] y β a β§ y β x) -> a β‘ β

-- A set cannot contain itself.
xβx : Β¬ (x β x)
xβx {x} xβx = equal-equiv (Extensional-converse β¦xβ§β‘β x) reflπ
    where
        β¦xβ§β‘β : β¦ x β§ β‘ β
        β¦xβ§β‘β = Regularity \ { _ reflπ -> exists x [ reflπ , xβx ] }

-- Two sets cannot mutually contain each other.
-- This pattern can be continued by induction, but we do not persue this here.
β-cycle : (x β y) -> (y β x) -> β₯ {lzero}
β-cycle {x} {y} xβy yβx = equal-equiv (Extensional-converse β¨x,yβ©β‘β x) (ΞΉβ reflπ)
    where
        β¨x,yβ©β‘β : β¨ x , y β© β‘ β
        β¨x,yβ©β‘β = Regularity \ { w (ΞΉβ reflπ) -> exists y [ ΞΉβ reflπ , yβx ] ;
                                 w (ΞΉβ reflπ) -> exists x [ ΞΉβ reflπ , xβy ] }

-- A set cannot contain every set.
π-proper : Β¬ (β y -> y β x)
π-proper {x} univ = xβx {x} (univ x)
-- The consequences of Regularity is profound. So we will not explore them too soon.

-- Infinity
-- Since we have Agda, let's define the set Ο in a really neat way.

-- To be consistent, we use π as an alias for the empty set.
π : π
π = β

infixl 21 _βΊ
_βΊ : π -> π  -- defines the successor
x βΊ = x βͺ β¦ x β§

-- π is a successor.
πβ‘ββΊ : π β‘ β βΊ
πβ‘ββΊ = Extensional zigzag
    where
        zigzag : β z -> (z β β) β‘ β₯ β¨ (z β β)
        zigzag z rewrite (xββ {z}) = equiv-equal [ ΞΉβ , (\ { (ΞΉβ x) -> x }) ]

-- π is also a successor.
πβ‘πβΊ : π β‘ π βΊ
πβ‘πβΊ = Extensional \ z -> equiv-equal [ zig , zag ]
    where
        zig : z β π -> (z β β) β¨ (z β π)
        zig {z} zβπ with π-boolean {z} zβπ
        ... | injβ refl = ΞΉβ idP
        ... | injβ refl = ΞΉβ reflπ
        zag : (z β β) β¨ (z β π) -> z β π
        zag (ΞΉβ zββ) wβz _ = zββ wβz
        zag (ΞΉβ reflπ) = idP

-- The successor operation is injective.
injective-βΊ : β x y -> x βΊ β‘ y βΊ -> x β‘ y
injective-βΊ x y eq = Extensional \ z -> equiv-equal [ zig , zag ]
    where
        ext : (w : π) -> w β x β¨ (w β x) β‘ w β y β¨ (w β y)
        ext = Extensional-converse eq
        zig : z β x -> z β y
        zig zβx with equal-equiv (ext _) (ΞΉβ zβx) | equal-equiv (ext x) (ΞΉβ reflπ)
        ... | ΞΉβ zβy | _ = zβy
        ... | ΞΉβ reflπ | ΞΉβ xβy = ex-falso
            (β-cycle {y} {x} zβx xβy)  -- Since we instantiated a reflπ, zβx is actually yβx.
        ... | ΞΉβ reflπ | ΞΉβ reflπ = zβx
        zag : z β y -> z β x  -- I didn't bother reusing zig, maybe later..
        zag zβy with equal-equiv (symm (ext _)) (ΞΉβ zβy) | equal-equiv (symm (ext y)) (ΞΉβ reflπ)
        ... | ΞΉβ zβx | _ = zβx
        ... | ΞΉβ reflπ | ΞΉβ yβx = ex-falso
            (β-cycle {x} {y} zβy yβx)
        ... | ΞΉβ reflπ | ΞΉβ reflπ = zβy

xβΊβ’β : β x -> (x βΊ β‘ β) -> β₯ {lzero}
xβΊβ’β x eq = equal-equiv (Extensional-converse eq x) (ΞΉβ reflπ)

-- The ord function embeds Nat into Ο.
ord : Nat -> π
ord 0 = π
ord (succ n) = (ord n) βΊ

injective-ord : β n m -> ord n β‘ ord m -> n β‘ m
injective-ord zero zero eq = refl
injective-ord zero (succ m) eq = magic (xβΊβ’β (ord m) (symm eq))
injective-ord (succ n) zero eq = magic (xβΊβ’β (ord n) eq)
injective-ord (succ n) (succ m) eq
    rewrite injective-ord n m (injective-βΊ (ord n) (ord m) eq) = refl

-- We now state the axiom of Infinity.
postulate
    Ο : π
    Infinity : β n -> ord n β Ο
    count : β x -> (x β Ο) -> Nat
    -- ord and count are inverses.
    ord-count : β x i -> ord (count x i) β‘ x

-- From this, we can prove the other side of the inverse.
count-ord : β n i -> count (ord n) i β‘ n
count-ord n _ = injective-ord _ _ (ord-count _ _)

{-# REWRITE ord-count count-ord #-}

-- The axiom of choice needs more machinery to state.
-- Therefore, we postpone it.
