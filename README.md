# ZFC
An embedding of ZFC into Agda. I assumed the excluded middle (on `Prop`) and function extensionality.

The theory of sets is represented as a postulated type of all sets `𝕍`, and a relation `_∈_` on it.
The non-non-constructive axioms (power set, replacement, etc.) are represented as postulated functions together with Agda `REWRITE` rules.
For instance, `z ∈ 𝒫 x` reduces to `z ⊆ x`; and `z ∈ ⟦ y ∈ x ∥ P ⟧` reduces to `z ∈ x ∧ P z`.
On the other hand, complex constructions based on these postulates are marked as abstract, to prevent definition explosion.

I haven't got to all the axioms yet. I haven't covered Regularity, Infinity and Choice. But some developments on the rest of the axioms are in place.
Hopefully I have enough comments in there.

Also, an (almost finished) propositional logic solver is present in the `logic.agda` file. Input a proposition with variables,
if it is a tautology, the solver outputs a function `⊤ -> [proposition]`; else it generates a function `⊥ -> [Proposition]`.
I have yet to prove some computationally irrelevant lemmas.

## Further explorations
- What is the best way to deal with stuff in Agda + LEM? This area seems unexplored by most of the people. I reckon
it'd be super cool to have a resolution + paramodulation solver implemented and verified entirely in Agda.
- ZFC (or any other set theory, constructive or not) with some computational rules is interesting to work with!
Maybe ZFC don't work out as well as NBG, but anyway look at this excerpt, isn't it cool?
```agda
-- From extensionality, we immediately obtain that the empty set is unique.
∅-unique : (∀ x -> x ∈ y ≡ ⊥) -> y ≡ ∅
∅-unique = Extensional  -- Well, that's literally immediate.
```
- Is my formulation equivalent to ZFC, or is the dependent types in Agda giving too much power?
For instance, the replacement axiom involves an arbitrary predicate `_↦_ : 𝕍 -> 𝕍 -> Prop`. Does agda give more than first order logic has to give?
