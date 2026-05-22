/-
# DSA5210 Session 4 — Lean code blocks from `session04-notes.md`

All `lean` fences in the notes are extracted here, grouped by slide and
wrapped as `example` / `theorem` / `def` so the whole file typechecks
against Mathlib `v4.28.0`.

* Statements that are illustrative *only* (pseudo-code, type signatures, or
  intentionally-broken baselines) appear inside `/- ... -/` comments and are
  flagged with a note explaining why they are not active Lean.
* All proof bodies are `sorry` — Session 4 is about statement alignment, not
  proofs.
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Set Filter Topology MeasureTheory intervalIntegral

namespace Session04

noncomputable section

/-! ## Slide 2. `sin x / x` — improper Riemann exists, Lebesgue does not -/

/-- First reading: the improper Riemann integral exists as a limit. -/
example :
    ∃ L : ℝ,
      Tendsto
        (fun R : ℝ => ∫ x in (1 : ℝ)..R, Real.sin x / x)
        atTop
        (𝓝 L) := by
  sorry

/-- Second reading: not Lebesgue integrable on `[1, ∞)`. -/
example : ¬ IntegrableOn (fun x : ℝ => Real.sin x / x) (Set.Ici 1) := by
  sorry

/-! ## Slide 3. Putnam 2025 B2 -/

theorem putnam_2025_b2
    (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1))
    (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) <
    (∫ x in (0:ℝ)..1, x * (f x) ^ 2) / (∫ x in (0:ℝ)..1, (f x) ^ 2) := by
  sorry

/-! ## Slide 4. Gemini draft, repaired (definition-layer)

The raw Gemini draft from the slide does *not* typecheck — by design.
Its problems (calling `area_R` as if it were a function, using `π` without
`Real.`, `noncomputable` missing, etc.) are discussed in the notes.
The repaired definition-layer version below typechecks.
-/

def area_R (f : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, f x

def centroid_x1 (f : ℝ → ℝ) : ℝ :=
  (∫ x in (0:ℝ)..1, x * f x) / area_R f

def vol_solid (f : ℝ → ℝ) : ℝ :=
  Real.pi * ∫ x in (0:ℝ)..1, (f x)^2

def centroid_x2 (f : ℝ → ℝ) : ℝ :=
  (Real.pi * ∫ x in (0:ℝ)..1, x * (f x)^2) / vol_solid f

theorem centroid_inequality_defs
    (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1))
    (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    centroid_x1 f < centroid_x2 f := by
  sorry

/-! ## Slide 5. The `deriv` junk-value trap -/

-- 类型签名（informational; the actual Mathlib declarations）:
#check @HasDerivAt        -- (𝕜 → F) → F → 𝕜 → Prop
#check @deriv             -- (𝕜 → F) → 𝕜 → F     -- total: returns 0 at non-differentiable points
#check @intervalIntegral  -- (ℝ → E) → ℝ → ℝ → Measure ℝ → E

/-- Heaviside step function `H(x) = 𝟙_{[0,∞)}(x)`. -/
def H : ℝ → ℝ := Set.indicator (Set.Ici (0 : ℝ)) (fun _ => 1)

/-- `H` is *not* differentiable at `0`, yet `deriv H 0 = 0` by the junk-value
convention. Reading `deriv H 0 = 0` as "the derivative at 0 is 0" is wrong. -/
example : deriv H 0 = 0 := by
  sorry

/-! ## Slide 6. FTC statement shapes -/

/-- FTC-1 shape (needs continuity / integrability hypotheses to be a real theorem). -/
example (f : ℝ → ℝ) (a x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..y, f t) (f x) x := by
  sorry

/-- FTC-2 shape (needs `∀ x, HasDerivAt F (f' x) x` plus integrability). -/
example (f' F : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f' x) = F b - F a := by
  sorry

-- Actual Mathlib lemma names:
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt
#check @intervalIntegral.integral_deriv_eq_sub'

/-! ## Slide 7. Worked example: `f' ≡ 0 ⟹ f` constant

The "obvious" LLM draft (kept as a comment) fails to compile for two reasons:
1.  `∀ x y ∈ S, P x y` is invalid Lean 4 syntax (no multi-binder `∈`).
2.  `eq_of_deriv_eq_zero` is a *hallucinated* identifier — the real Mathlib
    lemma is `constant_of_derivWithin_zero` (note: `derivWithin`, not `deriv`).

```lean
-- LLM draft — does NOT typecheck. Quoted for the slide.
theorem constant_of_deriv_zero
    {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, deriv f x = 0) :
    ∀ x y ∈ Icc a b, f x = f y := by
  exact eq_of_deriv_eq_zero hab hcont hdiff hderiv
```
-/

/-- Version A — real Mathlib API, `derivWithin`-style.
Note: `DifferentiableOn` on `Icc` already implies continuity; the derivative
condition lives on `Ico` (right-open), not `Ioo`, because at `a` the
right-derivative is meaningful. -/
example
    {a b : ℝ}
    {f : ℝ → ℝ}
    (hdiff : DifferentiableOn ℝ f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, derivWithin f (Icc a b) x = 0) :
    ∀ x ∈ Icc a b, f x = f a :=
  constant_of_derivWithin_zero hdiff hderiv

/-- Version B — `HasDerivWithinAt`-style. Keeps `ContinuousOn` as hypothesis;
the derivative is a *right* derivative on `Ici x`. -/
example
    {a b : ℝ}
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt f 0 (Ici x) x) :
    ∀ x ∈ Icc a b, f x = f a :=
  constant_of_has_deriv_right_zero hcont hderiv

-- Reference checks: the two lemmas actually used above.
#check @constant_of_derivWithin_zero
#check @constant_of_has_deriv_right_zero

/-! ## Slides 8–10. Interval integral notation, Bochner integral, BoxIntegral -/

-- Just notation snippets — the following expressions all elaborate:
example (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, f x
example (f : ℝ → ℝ) (μ : Measure ℝ) : ℝ := ∫ x, f x ∂μ
example (f : ℝ → ℝ) (s : Set ℝ) (μ : Measure ℝ) : ℝ := ∫ x in s, f x ∂μ
example (f : ℝ → ℝ) (a b : ℝ) (μ : Measure ℝ) : ℝ := ∫ x in a..b, f x ∂μ

-- BoxIntegral references (Riemann-style):
#check @BoxIntegral.HasIntegral
#check @BoxIntegral.Integrable
#check @BoxIntegral.integral
#check @BoxIntegral.IntegrationParams.Riemann

/-! ## Slide 14. Sum of first n odd numbers -/

example (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 * i + 1)) = n ^ 2 := by
  sorry

/-! ## Slide 15. Set distributivity -/

section SetDistrib
variable {α : Type*} (A B C : Set α)

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

end SetDistrib

/-! ## Slide 16. Inverse of a product -/

section InvProduct
variable {G : Type*} [Group G]

example (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end InvProduct

/-! ## Slide 17. Subgroup of cyclic group is cyclic (teaching approximation) -/

section CyclicSub
variable {G : Type*} [Group G]

/-- The natural-language statement, made precise: the subgroup, viewed as a
group via its inherited structure, is cyclic. -/
example : ∀ H : Subgroup G, IsCyclic G → IsCyclic H := by
  sorry

end CyclicSub

/-! ## Slide 18. Continuous function on `[a,b]` attains a maximum -/

example (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
    (h_cont : ContinuousOn f (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f y ≤ f x := by
  sorry

/-! ## Slide 19. `Gal(E/ℚ) ≅ Q₈` — three formalization shapes -/

/-- `α = √((2 + √2)(3 + √3))`. -/
def α : ℝ := Real.sqrt ((2 + Real.sqrt 2) * (3 + Real.sqrt 3))

/-- Field adjoin: `E = ℚ(α) ⊆ ℝ`. -/
def E : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {α}

/-- **Formalization A** — direct group isomorphism via `MulEquiv`.
`(↥E ≃ₐ[ℚ] ↥E)` is the type of `ℚ`-algebra automorphisms of `E`. -/
def gal_iso_Q8 : (↥E ≃ₐ[ℚ] ↥E) ≃* QuaternionGroup 2 := by
  sorry

/-- `≃*` lives in `Type`, so the proposition flavor uses `Nonempty`. -/
theorem gal_iso_Q8_nonempty :
    Nonempty ((↥E ≃ₐ[ℚ] ↥E) ≃* QuaternionGroup 2) := by
  sorry

/-- **Formalization B** — `Q₈` *is* the Galois group, expressed as a predicate.
Requires a `MulSemiringAction` instance to even state. -/
theorem q8_is_galois_group
    [MulSemiringAction (QuaternionGroup 2) (↥E)] :
    IsGaloisGroup (QuaternionGroup 2) ℚ (↥E) := by
  sorry

-- Mathlib bridge predicate signature:
#check @IsGaloisGroup

/-- **Formalization C** — package the extension as a `FiniteGaloisIntermediateField`,
then read off `finGaloisGroup`. We state only the existence shape here; building
the actual `Efin` requires proving finite-dimensional and Galois, which is real
mathematical content. -/
example :
    ∃ (Efin : FiniteGaloisIntermediateField ℚ ℝ),
      Efin.toIntermediateField = E := by
  sorry

/-! ## Slide 20. Noetherian local ring — exists `W` with `m_R W ≠ W`
   and every system of parameters is a regular sequence on `W` -/

/-- `IsRegularSeq R M s`: `s` is a regular sequence on the `R`-module `M`.
Defined by recursion on the list, with the module being quotiented at each step. -/
def IsRegularSeq (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    List R → Prop
  | []     => True
  | r :: t =>
    IsSMulRegular M r ∧
    IsRegularSeq R (M ⧸ (Ideal.span ({r} : Set R) • (⊤ : Submodule R M))) t

/-- `s : Fin n → R` is a system of parameters: it generates an 𝔪-primary ideal
of length equal to the Krull dimension. -/
def IsSystemOfParameters (R : Type*) [CommRing R] [IsLocalRing R] {n : ℕ} (s : Fin n → R) :
    Prop :=
  (Ideal.span (Set.range s)).radical = IsLocalRing.maximalIdeal R ∧
  (n : WithBot ℕ∞) = ringKrullDim R

/-- Existence of a balanced big Cohen–Macaulay-style module. -/
theorem exists_module_sop_regular (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W),
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R W) ≠ ⊤ ∧
      ∀ {n : ℕ} (s : Fin n → R),
        IsSystemOfParameters R s → IsRegularSeq R W (List.ofFn s) := by
  sorry

/-! ## Slide 22. The Polynomial `:=` trap

The expression below is *valid Lean syntax*, but `f` is a *parameter with a
default value*, not an equation `f = X^6 + ...`. Wrapping as `example` shows
the actual type. -/
example (f : Polynomial ℤ :=
    Polynomial.X ^ 6 + 30 * Polynomial.X ^ 5 - 15 * Polynomial.X ^ 3
      + 6 * Polynomial.X - 120) : Polynomial ℤ := f

/-! ## LoC-Decomp: explicit `continuous_at` -/

def continuous_at (x₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    |x - x₀| < δ → |f x - f x₀| < ε

/-! ## Slide 37. Herald `Set.Ico` example -/

example (a b c : ℝ) :
    c ∈ Set.Ico a b ↔ a ≤ c ∧ c < b := by
  sorry

/-! ## Slide 38. Eigenvector quantifier order -/

section Eigen
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable (T : V → V)

/-- Formalization A: every `v` has *its own* scalar `k`. -/
example : Prop := ∀ v : V, ∃ k : F, T v = k • v

/-- Formalization B: a *single* scalar `k` works for all `v`. -/
example : Prop := ∃ k : F, ∀ v : V, T v = k • v

end Eigen

/-! ## Slide 39. Four Lemma (mono half) — name reference only

The real Mathlib declaration carries auto-generated proof terms for the
`app'` indices that show up as `...` in the slide. We just `#check` it. -/
#check @CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono

/-! ## Slide 41. `@[blueprint]` attribute

`@[blueprint "label" (statement := /-- ... -/)]` is **not** an attribute that
ships with Mathlib v4.28.0 — it is part of the LeanArchitect project, applied
in its own repo. So the slide's example is left as a documentation comment.
-/

end -- noncomputable section

end Session04
