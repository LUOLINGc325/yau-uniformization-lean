import Yau.Blueprint.HodgeContracts
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
Scheduled-internal operator targets, not proofs or external inputs. The general
Hilbert/Lp assertions below use exact generator graphs; an evolution cannot be
chosen independently of its unbounded operator. Canonical Hodge instantiation
is a separate, unproved construction: see OperatorLeafLocks.md.
-/
open MeasureTheory Filter
open scoped Topology ENNReal NNReal InnerProductSpace
noncomputable section
namespace Yau.OperatorCandidates

/-! L03: a concrete prequotient formulation of essential self-adjointness of □.
No adjoint is applied to a non-dense domain and no totalized closure is used. -/
variable {n : ℕ} {M : ComplexManifold n}

def HodgeCorePair {k : ℕ} (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : RealForm M k) : Prop :=
  SmoothRealForm A ∧ CompactlySupportedRealForm A ∧ SmoothRealForm W ∧
    L2RealForm g μ A ∧ L2RealForm g μ W ∧ RepresentsHodge g A W

def HodgeMinimalGraph {k : ℕ} (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : RealForm M k) : Prop :=
  L2RealForm g μ A ∧ L2RealForm g μ W ∧
    ∃ As Ws : ℕ → RealForm M k,
      (∀ j, HodgeCorePair g μ (As j) (Ws j)) ∧
      Tendsto (fun j => formL2DistanceSq g μ (As j) A +
        formL2DistanceSq g μ (Ws j) W) atTop (𝓝 0)

/-- Distributional maximal graph: □A=W is tested against the actual computed
compactly supported smooth Hodge expression, using the actual metric pairing. -/
def HodgeMaximalGraph {k : ℕ} (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : RealForm M k) : Prop :=
  L2RealForm g μ A ∧ L2RealForm g μ W ∧
    ∀ B Z, HodgeCorePair g μ B Z →
      Integrable (formInner g A Z) μ ∧ Integrable (formInner g W B) μ ∧
      (∫ x, formInner g A Z x ∂μ) = ∫ x, formInner g W B x ∂μ

/-- BMS Cor. 2.10 / Remark 2.12, specialized to the complete de Rham Laplacian.
This is an internal real-form consequence, not a verbatim external signature.
AE quotient/descent and density are explicit remaining bridges. -/
def HodgeEssentialSelfAdjointness : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (g : SmoothMetric M),
    IsSmooth g → IsComplete g → ∀ μ : Measure M.Carrier,
    IsRiemannianVolume g.form μ → ∀ k (A W : RealForm M k),
      HodgeMinimalGraph g.form μ A W ↔ HodgeMaximalGraph g.form μ A W

/-- The finite de Rham exterior algebra, represented without transporting
between dependent finite indices. Degrees above the real dimension vanish. -/
abbrev GradedRealForm (M : ComplexManifold n) := (k : ℕ) → RealForm M k

def GradedL2 (g : HermitianField M) (μ : Measure M.Carrier)
    (A : GradedRealForm M) : Prop :=
  (∀ k, 2 * n < k → A k = 0) ∧ ∀ k, L2RealForm g μ (A k)

def gradedInner (g : HermitianField M) (A B : GradedRealForm M)
    (x : M.Carrier) : ℝ :=
  ∑ k : Fin (2 * n + 1), formInner g (A k.val) (B k.val) x

def gradedDistanceSq (g : HermitianField M) (μ : Measure M.Carrier)
    (A B : GradedRealForm M) : ℝ≥0∞ :=
  ∑ k : Fin (2 * n + 1), formL2DistanceSq g μ (A k.val) (B k.val)

/-- The actual expression d+δ on the whole exterior algebra. -/
def diracComponents (g : HermitianField M) (x : M.Carrier)
    (A : GradedRealForm M) : (k : ℕ) → FormComponents n k
  | 0 => codifferentialComponents g x (formComponents (A 1) x)
  | k + 1 => fun z I => exteriorComponents (formComponents (A k) x) z I +
      codifferentialComponents g x (formComponents (A (k + 2)) x) z I

def DiracCorePair (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : GradedRealForm M) : Prop :=
  GradedL2 g μ A ∧ GradedL2 g μ W ∧
    (∀ k, SmoothRealForm (A k) ∧ CompactlySupportedRealForm (A k) ∧
      SmoothRealForm (W k)) ∧
    ∀ x z, z ∈ chartTarget x → ∀ k I,
      formComponents (W k) x z I = diracComponents g x A k z I

def DiracMinimalGraph (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : GradedRealForm M) : Prop :=
  GradedL2 g μ A ∧ GradedL2 g μ W ∧ ∃ As Ws : ℕ → GradedRealForm M,
    (∀ j, DiracCorePair g μ (As j) (Ws j)) ∧
    Tendsto (fun j => gradedDistanceSq g μ (As j) A +
      gradedDistanceSq g μ (Ws j) W) atTop (𝓝 0)

def DiracMaximalGraph (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : GradedRealForm M) : Prop :=
  GradedL2 g μ A ∧ GradedL2 g μ W ∧ ∀ B Z, DiracCorePair g μ B Z →
    Integrable (gradedInner g A Z) μ ∧ Integrable (gradedInner g W B) μ ∧
    (∫ x, gradedInner g A Z x ∂μ) = ∫ x, gradedInner g W B x ∂μ

/-- Internal inference from the Hodge-square result; not attributed verbatim
to BMS Cor. 2.10. Includes the full-degree compact core and maximal domain. -/
def DiracEssentialSelfAdjointness : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (g : SmoothMetric M),
    IsSmooth g → IsComplete g → ∀ μ : Measure M.Carrier,
    IsRiemannianVolume g.form μ → ∀ A W : GradedRealForm M,
      DiracMinimalGraph g.form μ A W ↔ DiracMaximalGraph g.form μ A W

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Includes density because Mathlib's adjoint has a junk-value branch otherwise. -/
def NonnegativeSelfAdjoint (A : H →ₗ.[ℂ] H) : Prop :=
  Dense (A.domain : Set H) ∧ IsSelfAdjoint A ∧
    ∀ u : A.domain, 0 ≤ (inner ℂ (u : H) (A u)).re

/-- Full graph, including domain equality, of the square of an unbounded operator. -/
def SquareGraph (D A : H →ₗ.[ℂ] H) : Prop :=
  ∀ u w : H, (u, w) ∈ A.graph ↔ ∃ v : H, (u, v) ∈ D.graph ∧ (v, w) ∈ D.graph

/-- `T(t)=exp(-t A)` specified by its C0 semigroup and its exact right-generator
at zero. The reverse implication prevents a smaller prescribed domain. -/
def IsHeatOf (A : H →ₗ.[ℂ] H) (T : ℝ → H →L[ℂ] H) : Prop :=
  T 0 = ContinuousLinearMap.id ℂ H ∧
    (∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
    (∀ u, ContinuousOn (fun t => T t u) (Set.Ici 0)) ∧
    (∀ u v : H, HasDerivWithinAt (fun t => T t u) (-v) (Set.Ici 0) 0 ↔
      (u, v) ∈ A.graph)

/-- `U(t)=exp(itD)`, with the whole generator domain fixed by a graph equivalence. -/
def IsGroupOf (D : H →ₗ.[ℂ] H) (U : ℝ → H →L[ℂ] H) : Prop :=
  U 0 = ContinuousLinearMap.id ℂ H ∧
    (∀ s t, U (s + t) = (U s).comp (U t)) ∧
    (∀ u, Continuous (fun t => U t u)) ∧
    (∀ u v : H, HasDerivAt (fun t => U t u) (Complex.I • v) 0 ↔ (u, v) ∈ D.graph)

/-- The manuscript's deficiency-space deduction after BMS; internal algebraic
operator step, separated from the cited essential self-adjointness of D². -/
def EssentialSelfAdjointOfSquare : Prop :=
  ∀ D A : H →ₗ.[ℂ] H,
    Dense (D.domain : Set H) → D.IsFormalAdjoint D → SquareGraph D A →
    Dense (A.domain : Set H) → A.IsClosable → IsSelfAdjoint A.closure →
    D.IsClosable ∧ IsSelfAdjoint D.closure
end Hilbert

section MetricLp
variable {S E : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μ : Measure S)
abbrev SectionL2 := Lp E 2 μ

def SupportedIn (u : SectionL2 (E := E) μ) (K : Set S) : Prop :=
  ∀ᵐ x ∂μ, x ∉ K → u x = 0

/-- McIntosh--Morris Thm 3.1 (p=2, Bochner trivial-bundle case; Remark 3.4).
The commutator is a genuine bounded operator, identified pointwise a.e.; its
second commutator vanishes. No free multiplication-operator API is assumed. -/
def LipschitzCommutatorBound (D : SectionL2 (E := E) μ →ₗ.[ℂ] SectionL2 (E := E) μ)
    (κ : ℝ) : Prop :=
  ∀ (η : S → ℝ) (K : ℝ≥0), LipschitzWith K η → Bornology.IsBounded (Set.range η) →
    ∃ B : SectionL2 (E := E) μ →L[ℂ] SectionL2 (E := E) μ,
      ‖B‖ ≤ κ * K ∧
      (∀ u : D.domain, ∃ v : D.domain,
        (∀ᵐ x ∂μ, (v : SectionL2 (E := E) μ) x = (η x : ℂ) • (u : SectionL2 (E := E) μ) x) ∧
        (∀ᵐ x ∂μ, B (u : SectionL2 (E := E) μ) x =
          (η x : ℂ) • (D u) x - (D v) x)) ∧
      (∀ u v : SectionL2 (E := E) μ,
        (∀ᵐ x ∂μ, v x = (η x : ℂ) • u x) →
        ∀ᵐ x ∂μ, B v x = (η x : ℂ) • B u x)

def FinitePropagation (U : ℝ → SectionL2 (E := E) μ →L[ℂ] SectionL2 (E := E) μ)
    (v : ℝ) : Prop :=
  ∀ (K : Set S), IsClosed K → K.Nonempty → ∀ u, SupportedIn μ u K → ∀ t,
    SupportedIn μ (U t u) {x | Metric.infDist x K ≤ v * |t|}

/-- Source-general metric-space version actually used for the missing Hodge
instance; σ-finiteness and commutator/domain hypotheses are all retained. -/
def McIntoshMorrisFinitePropagation [SigmaFinite μ] : Prop :=
  ∀ (D : SectionL2 (E := E) μ →ₗ.[ℂ] SectionL2 (E := E) μ)
    (U : ℝ → SectionL2 (E := E) μ →L[ℂ] SectionL2 (E := E) μ) (c ω κ : ℝ),
    1 ≤ c → 0 ≤ ω → 0 < κ → IsGroupOf D U →
    (∀ t u, ‖U t u‖ ≤ c * Real.exp (ω * |t|) * ‖u‖) →
    LipschitzCommutatorBound μ D κ → FinitePropagation μ U (c * κ)

/-- Open-set formulation (3.5), with cos(tD)=(U(t)+U(-t))/2 for A=D².
Distance lower bounds avoid the empty-set conventions of `infDist`. -/
def CosineFinitePropagation (U : ℝ → SectionL2 (E := E) μ →L[ℂ] SectionL2 (E := E) μ) : Prop :=
  ∀ (O₁ O₂ : Set S), IsOpen O₁ → IsOpen O₂ → ∀ (r t : ℝ),
    0 < t → t < r → (∀ x ∈ O₁, ∀ y ∈ O₂, r ≤ dist x y) →
    ∀ f g, SupportedIn μ f O₁ → SupportedIn μ g O₂ →
      inner ℂ (((1 / 2 : ℂ) • (U t f + U (-t) f))) g = 0

/-- Exact Davies--Gaffney normalization (3.2), not unspecified C,c. -/
def DaviesGaffney (T : ℝ → SectionL2 (E := E) μ →L[ℂ] SectionL2 (E := E) μ) : Prop :=
  ∀ (O₁ O₂ : Set S), IsOpen O₁ → IsOpen O₂ → ∀ (r t : ℝ),
    0 ≤ r → 0 < t → (∀ x ∈ O₁, ∀ y ∈ O₂, r ≤ dist x y) →
    ∀ f g, SupportedIn μ f O₁ → SupportedIn μ g O₂ →
      ‖inner ℂ (T t f) g‖ ≤ Real.exp (-(r ^ 2) / (4 * t)) * ‖f‖ * ‖g‖

/-- Coulhon--Sikora Thm 3.4, D² specialization. Scalar source theorem is
obtained with E=ℂ; the bundle/Bochner extension is scheduled internally. -/
def WaveHeatEquivalence [SigmaFinite μ] : Prop :=
  ∀ (D A : SectionL2 (E := E) μ →ₗ.[ℂ] SectionL2 (E := E) μ)
    (U T : ℝ → SectionL2 (E := E) μ →L[ℂ] SectionL2 (E := E) μ),
    Dense (D.domain : Set (SectionL2 (E := E) μ)) → IsSelfAdjoint D →
    SquareGraph D A → NonnegativeSelfAdjoint A → IsGroupOf D U → IsHeatOf A T →
      (CosineFinitePropagation μ U ↔ DaviesGaffney μ T)
end MetricLp

section Exhaustion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hj : ℕ → Type*} [∀ j, NormedAddCommGroup (Hj j)]
  [∀ j, InnerProductSpace ℂ (Hj j)] [∀ j, CompleteSpace (Hj j)]

/-- R(λ)=(A+λ)⁻¹ expressed by its exact graph, for λ>0. -/
def IsPositiveResolvent (A : H →ₗ.[ℂ] H) (lam : ℝ) (R : H →L[ℂ] H) : Prop :=
  0 < lam ∧ ∀ f, (R f, f - (lam : ℂ) • R f) ∈ A.graph

/-- Teschl §6.6 varying-Hilbert-space convention, Thm 6.31/Cor 6.33,
common lower bound zero. Inclusion follows heat: Jj Tj(t) Pj.
`Pj` is the adjoint restriction, not a zero-extended generator. -/
def ExhaustionHeatConvergence : Prop :=
  ∀ (A : H →ₗ.[ℂ] H) (Aj : (j : ℕ) → Hj j →ₗ.[ℂ] Hj j)
    (J : (j : ℕ) → Hj j →ₗᵢ[ℂ] H) (P : (j : ℕ) → H →L[ℂ] Hj j)
    (R : ℝ → H →L[ℂ] H) (Rj : (j : ℕ) → ℝ → Hj j →L[ℂ] Hj j)
    (T : ℝ → H →L[ℂ] H) (Tj : (j : ℕ) → ℝ → Hj j →L[ℂ] Hj j),
    NonnegativeSelfAdjoint A → (∀ j, NonnegativeSelfAdjoint (Aj j)) →
    (∀ j u v, inner ℂ (P j u) v = inner ℂ u (J j v)) →
    (∀ u, Tendsto (fun j => J j (P j u)) atTop (𝓝 u)) →
    (∀ lam, 0 < lam → IsPositiveResolvent A lam (R lam)) →
    (∀ j lam, 0 < lam → IsPositiveResolvent (Aj j) lam (Rj j lam)) →
    (∀ lam, 0 < lam → ∀ u,
      Tendsto (fun j => J j (Rj j lam (P j u))) atTop (𝓝 (R lam u))) →
    IsHeatOf A T → (∀ j, IsHeatOf (Aj j) (Tj j)) →
    ∀ t, 0 ≤ t → ∀ u, Tendsto (fun j => J j (Tj j t (P j u))) atTop (𝓝 (T t u))
end Exhaustion
end Yau.OperatorCandidates
