{-# OPTIONS --prop --rewriting #-}

module logic where
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive

private variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ' ℓ'' : Level
id : ∀ {A : Set ℓ} -> A -> A
id a = a
const : ∀ {A : Set ℓ} {B : Set ℓ'} -> A -> B -> A
const a _ = a
idP : ∀ {A : Prop ℓ} -> A -> A
idP a = a
constP : ∀ {A : Prop ℓ} {B : Prop ℓ'} -> A -> B -> A
constP a _ = a
-- The familiar constructs.
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
open _∧_
record _*_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,_
    field
        proj₁ : P
        proj₂ : Q
-- Note that Exists is a proposition.
data Exists (A : Set ℓ) (P : A -> Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    exists : (a : A) -> P a -> Exists A P
syntax Exists A (\x -> P) = ∃[ x ∈ A ] P

data ExistsUnique (A : Set ℓ) (P : A -> Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    exists-unique : (a : A) -> (∀ b -> P b -> b ≡ a) -> ExistsUnique A P
syntax ExistsUnique A (\x -> P) = ∃![ x ∈ A ] P

record Sum (A : Set ℓ) (B : A -> Prop ℓ') : Set (ℓ ⊔ ℓ') where
    constructor fiber
    field
        witness : A
        proof : B witness
syntax Sum A (\x -> P) = Σ[ x ∈ A ] P

infixr 7 Exists ExistsUnique Sum choice  -- choice is a similar syntax defined later

data ⊥ {ℓ} : Prop ℓ where
ex-falso : {P : Prop ℓ'} -> ⊥ {ℓ} -> P
ex-falso ()
magic : {A : Set ℓ'} -> ⊥ {ℓ} -> A
magic ()
record ⊤ {ℓ} : Prop ℓ where
    constructor trivial  -- This should never appear, as it can be inferred.

-- Equality.
transport : {A B : Set ℓ} -> A ≡ B -> A -> B
transport refl a = a

cong : {T : Set ℓ} {A B : T} {C : Set ℓ'} (f : T -> C)
    -> A ≡ B -> f A ≡ f B
cong f refl = refl

symm : {A : Set ℓ} {a b : A} -> a ≡ b -> b ≡ a
symm refl = refl

trans : {A : Set ℓ} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans refl refl = refl

-- Booleans, used for reflection.
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

equal-equiv : {P Q : Prop ℓ} -> P ≡ Q -> P -> Q
equal-equiv refl p = p

equiv-equal : {P Q : Prop ℓ} -> (P -> Q) ∧ (Q -> P) -> P ≡ Q
equiv-equal {P = P} {Q = Q} [ P->Q , Q->P ] with truth P | truth Q
... | inj₁ refl | inj₁ refl = refl
... | inj₁ refl | inj₂ refl = magic (P->Q _)
... | inj₂ refl | inj₁ refl = magic (Q->P _)
... | inj₂ refl | inj₂ refl = refl

truth-⊤ : truth {ℓ} ⊤ ≡ inj₁ refl
truth-⊤ {ℓ} with truth {ℓ} ⊤
... | inj₁ refl = refl
... | inj₂ eq = magic (equal-equiv eq _)

truth-⊥ : truth {ℓ} ⊥ ≡ inj₂ refl
truth-⊥ {ℓ} with truth {ℓ} ⊥
... | inj₂ refl = refl
... | inj₁ eq = magic (equal-equiv (symm eq) _)

{-# REWRITE truth-⊤ truth-⊥ #-}

infixr 15 ¬_
¬_ : Prop ℓ -> Prop ℓ
¬_ {ℓ} P = P -> ⊥ {ℓ}

_≢_ : {A : Set ℓ} -> A -> A -> Prop ℓ
a ≢ b = (a ≡ b) -> ⊥ {lzero}

¬⊤≡⊥ : ¬ ⊤ ≡ ⊥ {ℓ}
¬⊤≡⊥ = equiv-equal [ (\ f -> f _) , ex-falso ]

¬⊥≡⊤ : ¬ ⊥ ≡ ⊤ {ℓ}
¬⊥≡⊤ = equiv-equal [ (\ _ -> _) , (\ _ ()) ]

¬¬P≡P : ∀ {P : Prop ℓ} -> ¬ ¬ P ≡ P
¬¬P≡P {P = P} with truth P 
... | inj₁ refl = equiv-equal [ (\ _ -> _) , (\ _ z -> z _) ]
... | inj₂ refl = equiv-equal [ (\ f -> f \ z -> z) , (\ z f -> f z) ]

≡-true : {P : Prop ℓ} -> P ≡ ⊤ -> P
≡-true refl = _

true-≡ : {P : Prop ℓ} -> P -> P ≡ ⊤
true-≡ p = equiv-equal [ (\ _ -> _) , (\ _ -> p) ]

false-≡ : ∀ {P : Prop ℓ} -> ¬ P -> P ≡ ⊥
false-≡ ¬P = equiv-equal [ ¬P , (\ ()) ]

≡-false : ∀ {P : Prop ℓ} -> P ≡ ⊥ -> ¬ P
≡-false refl ()

choice : (A : Set ℓ) (P : A -> Prop ℓ')
    -> (∀ x -> ¬ P x) ∨ (∃[ x ∈ A ] P x)
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

-- Develop boolean reflection tools.
infixl 15 _&&_
infixl 14 _||_
infixr 13 _=>_ _==_
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

not-reflect : ∀ x -> prop {ℓ} (not x) -> ¬ (prop {ℓ} x)
not-reflect true ()
not-reflect false _ ()

_==_ : Bool -> Bool -> Bool
true == true = true
false == false = true
_ == _ = false

==-reflect : ∀ x y -> prop {ℓ} (x == y) -> prop {ℓ} x ≡ prop {ℓ} y
==-reflect true true _ = refl
==-reflect false false _ = refl

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

-- Now we can start to make a solver.
-- First, to represent propositional variables, we use de Bruijn indices.
data PVar : Nat -> Set where
    this : {i : Nat} -> PVar (succ i)
    that : {i : Nat} -> PVar i -> PVar (succ i)

infixl 15 _&&&_
infixl 14 _|||_
infixr 13 _==>_ _<=>_
infix 10 _⊨_ _⊢_
-- The formula syntax representation.
data Formula (n : Nat) : Set where
    tt : Formula n
    ff : Formula n
    F : PVar n -> Formula n
    _&&&_ : Formula n -> Formula n -> Formula n
    _|||_ : Formula n -> Formula n -> Formula n
    _==>_ : Formula n -> Formula n -> Formula n
    ¡_ : Formula n -> Formula n

-- <=> is not a constructor, because in later developments, we
-- prefer (P ≡ Q) over (P -> Q) ∧ (Q -> P).
-- So equivalences will be proved through implication.
_<=>_ : ∀ {n} -> Formula n -> Formula n -> Formula n
f <=> g = (f ==> g) &&& (g ==> f)

private
    -- We define truth-value models.
    -- Crucially, we use Γ ⊢ f to mean that f is true, *whatever* Γ is.
    -- In contrast, the usual meaning of Γ ⊢ f is that f is true whenever Γ is.
    _⊢_ : {i : Nat} -> (PVar i -> Prop ℓ) -> (Formula i -> Prop ℓ)
    Γ ⊢ tt = ⊤
    Γ ⊢ ff = ⊥
    Γ ⊢ F x = Γ x
    Γ ⊢ f &&& g = (Γ ⊢ f) ∧ (Γ ⊢ g)
    Γ ⊢ f ||| g = (Γ ⊢ f) ∨ (Γ ⊢ g)
    Γ ⊢ f ==> g = (Γ ⊢ f) -> (Γ ⊢ g)
    Γ ⊢ ¡ f = ¬ (Γ ⊢ f)

    _⊨_ : {i : Nat} -> (PVar i -> Bool) -> (Formula i -> Bool)
    Γ ⊨ tt = true
    Γ ⊨ ff = false
    Γ ⊨ F x = Γ x
    Γ ⊨ f &&& g = (Γ ⊨ f) && (Γ ⊨ g)
    Γ ⊨ f ||| g = (Γ ⊨ f) || (Γ ⊨ g)
    Γ ⊨ f ==> g = (Γ ⊨ f) => (Γ ⊨ g)
    Γ ⊨ ¡ f = not (Γ ⊨ f)

    -- With this interpretation, soundness and completeness are mutually recursive.
    Soundness : ∀ {i} (f : Formula i)
        -> ∀ {ℓ} Γ -> (\ x -> prop {ℓ} (Γ x)) ⊢ f
        -> prop {ℓ} (Γ ⊨ f)
    Completeness : ∀ {i} (f : Formula i)
        -> ∀ {ℓ} Γ -> prop {ℓ} (Γ ⊨ f)
        -> (\ x -> prop {ℓ} (Γ x)) ⊢ f

    Soundness tt Γ prf = _
    Soundness (F x) Γ prf = prf
    Soundness (f &&& g) Γ [ Pf , Pg ] with Γ ⊨ f in eqf | Γ ⊨ g in eqg
    ... | true | true = _
    ... | true | false = equal-equiv (cong prop eqg) (Soundness g Γ Pg)
    ... | false | _ = equal-equiv (cong prop eqf) (Soundness f Γ Pf)
    Soundness (f ||| g) Γ prf with Γ ⊨ f in eqf | Γ ⊨ g in eqg
    ... | true | _ = _
    ... | false | true = _
    Soundness (f ||| g) Γ (ι₁ Pf) | false | false = equal-equiv (cong prop eqf) (Soundness f Γ Pf)
    Soundness (f ||| g) Γ (ι₂ Pg) | false | false = equal-equiv (cong prop eqg) (Soundness g Γ Pg)
    Soundness (f ==> g) Γ prf with Γ ⊨ f in eqf | Γ ⊨ g in eqg
    ... | false | _ = _
    ... | true | true = _
    ... | true | false = equal-equiv (cong prop eqg)
        (Soundness g Γ
            (prf (Completeness f Γ
                (equal-equiv (cong prop (symm eqf)) _))))
    Soundness (¡ f) Γ prf with Γ ⊨ f in eqf  -- exactly analogous to f ==> g (take g = ff)
    ... | true = prf (Completeness f Γ (equal-equiv (cong prop (symm eqf)) _))
    ... | false = _

    Completeness tt Γ prf = _
    Completeness (F x) Γ prf = prf
    Completeness (f &&& g) Γ prf =
        [ Completeness f Γ (π₁ prf') , Completeness g Γ (π₂ prf') ]
        where
            prf' : prop (Γ ⊨ f) ∧ prop (Γ ⊨ g)
            prf' = &&-reflect _ _ prf
    Completeness (f ||| g) Γ prf with ||-reflect _ _ prf
    ... | ι₁ prf' = ι₁ (Completeness f Γ prf')
    ... | ι₂ prf' = ι₂ (Completeness g Γ prf')
    Completeness (f ==> g) Γ prf Pf =
        Completeness g Γ
            (=>-reflect _ _ prf
                (Soundness f Γ Pf))
    Completeness (¡ f) Γ prf Pf = not-reflect _ prf (Soundness f Γ Pf)

    -- Now we need some auxiliary functions to deal with functions
    -- of type (PVar i -> A), which is equivalent to Data.Vector.Functional
    -- in the standard library.
    extend : ∀ {i} {A : Set ℓ} -> (PVar i -> A) -> A -> (PVar (succ i) -> A)
    extend v b this = b
    extend v b (that x) = v x

    extend-tail : ∀ {i} {A : Set ℓ} -> (v : PVar i -> A) (u : A)
        -> ∀ x -> extend v u (that x) ≡ v x
    extend-tail _ _ _ = refl

    extend-head : ∀ {i} {A : Set ℓ} -> (v : PVar i -> A) (u : A)
        -> extend v u this ≡ u
    extend-head _ _ = refl

    extend-case : ∀ {i} -> (v : PVar (succ i) -> Bool)
        -> (v ≡ extend (\ x -> v (that x)) true)
        ⊎ (v ≡ extend (\ x -> v (that x)) false)
    extend-case v with v this in eq
    ... | true = inj₁ (transport (symm funext) aux-true)
        where
            aux-true : ∀ y -> v y ≡ extend (\ x -> v (that x)) true y
            aux-true this = eq
            aux-true (that y) = refl
    ... | false = inj₂ (transport (symm funext) aux-false)
        where
            aux-false : ∀ y -> v y ≡ extend (\ x -> v (that x)) false y
            aux-false this = eq
            aux-false (that y) = refl

    -- Since _⊢_ has the unconventional meaning, we can represent
    -- the truth value of Γ ⊢ f as a conjunction of all the cases
    -- of Γ.
    conjunct : ∀ {i}
        -> ((PVar i -> Bool) -> Bool) -> Bool
    conjunct {i = zero} f = f (λ ())
    conjunct {i = succ i} f =
        (conjunct {i} \ t -> f (extend t true)) &&
        (conjunct {i} \ t -> f (extend t false))

    -- If the large conjunction is true, then every term must be true.
    conjunct-constant : ∀ {i} (f : (PVar i -> Bool) -> Bool)
        -> prop {lzero} (conjunct f)
        -> ∀ v -> f v ≡ true
    conjunct-constant {i = zero} f t v = aux
        where
            v-trivial : v ≡ \ ()
            v-trivial = transport (symm funext) \ ()
            aux : f v ≡ true
            aux rewrite v-trivial = prop-≡ t
    conjunct-constant {i = succ i} f t v with extend-case v |
        &&-reflect
            (conjunct {i} \ _ -> f _)
            (conjunct {i} \ _ -> f _) t
    ... | inj₁ extend-true | t-reflect rewrite extend-true =
        conjunct-constant (\ t -> f (extend t true)) (π₁ t-reflect) _
    ... | inj₂ extend-false | t-reflect rewrite extend-false =
        conjunct-constant (\ t -> f (extend t false)) (π₂ t-reflect) _

-- At this point, we pause and turn to a boolean version of the truth oracle.
-- decide is inverse to prop.
abstract
    decide : Prop ℓ -> Bool
    decide P with truth P
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    prop-decide : (P : Prop ℓ) -> prop (decide P) ≡ P
    prop-decide P with truth P
    ... | inj₁ eq = symm eq
    ... | inj₂ eq = symm eq

    decide-prop : ∀ b -> decide {lzero} (prop b) ≡ b
    decide-prop true with truth {lzero} ⊤
    ... | inj₁ _ = refl
    ... | inj₂ eq = magic (equal-equiv eq _)
    decide-prop false with truth {lzero} ⊥
    ... | inj₁ eq = magic (equal-equiv (symm eq) _)
    ... | inj₂ _ = refl
{-# REWRITE prop-decide decide-prop #-}

-- Let's continue the develop the main solver.
private
    solve-uncurried : ∀ {i} (f : Formula i)
        -> prop {lzero} (conjunct (_⊨ f))
        -> (Γ : PVar i -> Prop ℓ) -> Γ ⊢ f
    solve-uncurried f t Γ = Completeness f _ aux
        where
            aux : prop {ℓ} ((\ v -> decide (Γ v)) ⊨ f)
            aux rewrite conjunct-constant (_⊨ f) t \ v -> decide (Γ v) = _

    -- Now we develop tools to curry so as to make it more usable.
    ext-app : ∀ {i} {T : PVar (succ i) -> Set ℓ} {Obj : (∀ v -> T v) -> Prop ℓ'}
        (t : T this) (args : ∀ v -> T (that v))
        -> ∀ v -> T v
    ext-app t args this = t
    ext-app t args (that v) = args v

    _===>_ : ∀ {i} (T : PVar i -> Set ℓ) (Obj : (∀ v -> T v) -> Prop ℓ')
        -> Prop (ℓ ⊔ ℓ')
    _===>_ {ℓ = ℓ} {i = zero} T Obj = ∀ {_ : ⊤ {ℓ}} -> Obj \ ()
        -- the implicit parameter to modulate universe levels
    _===>_ {ℓ = ℓ} {ℓ' = ℓ'} {i = succ i} T Obj =
        (t : T this) -> (\ v -> T (that v)) ===> \ args ->
            Obj (ext-app {Obj = Obj} t args)

    curry : ∀ {i} (T : PVar i -> Set ℓ) (Obj : (∀ v -> T v) -> Prop ℓ')
        -> (∀ Γ -> Obj Γ) -> T ===> Obj
    curry {i = zero} T Obj f = f \ ()
    curry {i = succ i} T Obj f t = curry {i = i}
        (\ z -> T (that z))
        (\ args -> Obj (ext-app {Obj = Obj} t args)) \ Γ -> f (ext-app {Obj = Obj} t Γ)

    solve-curried : ∀ {i} (f : Formula i)
        -> prop {lzero} (conjunct (_⊨ f))
        -> (\ _ -> Prop ℓ) ===> (_⊢ f)
    solve-curried f t = curry (\ _ -> Prop _) _
        (solve-uncurried f t)

    -- We can improve this even further.
    -- We can get rid of the de-bruijn indexing.
    -- But the distinction between Prop and Set is a bit tricky.
    data _≤_ : Nat -> Nat -> Prop where
        𝕫 : ∀ {m} -> m ≤ m
        𝕤 : ∀ {m n} -> m ≤ n -> m ≤ (succ n)

    ≤-succ : ∀ m n -> succ m ≤ succ n -> m ≤ n
    ≤-succ m .m 𝕫 = 𝕫
    ≤-succ m (succ n) (𝕤 r) = 𝕤 (≤-succ m n r)

    var-seq : (A : Set ℓ) (i j : Nat) (_ : j ≤ i) -> Set ℓ
    var-seq A i zero _ = A
    var-seq A i@(succ i') (succ j) r = Formula i -> var-seq A i j (≤-succ j (succ i') (𝕤 r))

    -- An alternate set of PVar constructors.
    there : (i : Nat) -> PVar (succ i)
    there zero = this
    there (succ i) = that (there i)

    here : (i : Nat) -> PVar i -> PVar (succ i)
    here _ this = this
    here _ (that v) = that (here _ v)

    var-gen : (i j : Nat) (_ : j ≤ i) -> PVar (succ i)
    var-gen i zero r = there i
    var-gen (succ i') (succ j) r = here (succ i') (var-gen i' j (≤-succ j i' r))

    -- We fill in the dBI's in the right order.
    formula-seq : (i j : Nat) (r : j ≤ i)
        -> var-seq (Formula i) i j r
        -> Formula i
    formula-seq i zero _ f = f
    formula-seq (succ i) (succ j) r f =
        formula-seq (succ i) j (≤-succ j (succ i) (𝕤 r))
            (f (F (var-gen i j (≤-succ j i r))))

Formula! : (i : Nat) -> Set
Formula! i = var-seq (Formula i) i i 𝕫

-- The main solver. The prop is made implicit, because ⊤ can always be inferred.
solve : ∀ i (f : Formula! i)
    -> {_ : prop {lzero} (conjunct (_⊨ (formula-seq i i 𝕫 f)))}
    -> (\ _ -> Prop ℓ) ===> (_⊢ (formula-seq i i 𝕫 f))
solve i f {t} = solve-curried (formula-seq i i 𝕫 f) t

-- Example usage:
P∨P : (P : Prop ℓ) -> P ∨ P -> P
P∨P P = solve 1  -- We invoke the solver with 1 free variable.
    (\ P -> (P ||| P ==> P))  -- The formula.
    -- We can freely choose the bound name P thanks to our previous work.
    -- Also, here is an implicit variable, calculated to be of type ⊤,
    -- because the solver decided that the formula above is a tautology.
    P  -- Now we instantiate the propositional variable to P.

-- TODO make a macro for this.
-- We also want better error messages.

-- With our strong version of LEM, _∨_ is also decidable.
∨-oracle : ∀ {P Q : Prop ℓ} -> (P ∨ Q ≡ ⊤) -> (P ≡ ⊤) ⊎ (Q ≡ ⊤)
∨-oracle {P = P} {Q = Q} PQ with truth P | truth Q
... | inj₁ p | _ = inj₁ p
... | _ | inj₁ q = inj₂ q
... | inj₂ ¬p | inj₂ ¬q rewrite ¬p rewrite ¬q = magic (P∨P ⊥ (≡-true PQ))

-- Not much of an oracle, but anyway to keep the symmetry.
∧-oracle : ∀ {P Q : Prop ℓ} -> (P ∧ Q ≡ ⊤) -> (P ≡ ⊤) * (Q ≡ ⊤)
∧-oracle {P = P} {Q = Q} PQ with truth P | truth Q
... | inj₁ p | inj₁ q = p , q
... | _ | inj₂ ¬q rewrite ¬q = magic (≡-true PQ .π₂)
... | inj₂ ¬p | _ rewrite ¬p = magic (≡-true PQ .π₁)
