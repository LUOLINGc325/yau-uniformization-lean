import spec.CHAIN.HeatTargetCandidates

/-! Concrete output constraints for the six registered heat targets.
No completion, realization, kernel or analytic assertion is proved here. -/
open MeasureTheory Filter
open scoped Topology ENNReal NNReal InnerProductSpace Manifold ContDiff
noncomputable section
namespace Yau.HeatConcreteBindings
open Yau.Blueprint Yau.OperatorCandidates Yau.HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}

/-- A connected smooth domain in the actual manifold, using regular real
local defining functions in its actual charts. -/
def SmoothPrecompactDomain (O : Set M.Carrier) : Prop :=
  IsOpen O ∧ O.Nonempty ∧ IsConnected O ∧ IsCompact (closure O) ∧
  ∀ p ∈ frontier O, ∃ (x : M.Carrier) (V : Set (ComplexVector n))
      (ρ : ComplexVector n → ℝ),
    p ∈ (chartAt (ComplexVector n) x).source ∧ IsOpen V ∧ chartPt x p ∈ V ∧
    V ⊆ chartTarget x ∧ ContDiffOn ℝ ∞ ρ V ∧ ρ (chartPt x p) = 0 ∧
    fderiv ℝ ρ (chartPt x p) ≠ 0 ∧
    ∀ z ∈ V, (chartInv x z ∈ O ↔ ρ z < 0)

def SmoothExhaustion (O : ℕ → Set M.Carrier) : Prop :=
  (∀ j, SmoothPrecompactDomain (O j)) ∧
  (∀ j, closure (O j) ⊆ O (j + 1)) ∧ (⋃ j, O j) = Set.univ

/-- Ordinary exhaustion existence on the actual manifold; an OUTPUT obligation,
not an assumed domain family. Its proof is planned. -/
def SmoothExhaustionExistenceTarget (X : KahlerManifold n) : Prop :=
  ∃ O : ℕ → Set X.manifold.Carrier, SmoothExhaustion O

/-- Smooth compact real data in every actual degree. Local volume finiteness
must supply L² membership as an OUTPUT, rather than an extra data hypothesis. -/
def GradedSmoothCompact (A : GradedRealForm M) : Prop :=
  (∀ k, 2 * n < k → A k = 0) ∧
  ∀ k, SmoothRealForm (A k) ∧ CompactlySupportedRealForm (A k)

/-- Actual real tests; support is in the domain, not a caller-supplied flag. -/
def GradedTest (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (A : GradedRealForm M) : Prop :=
  GradedL2 g μ A ∧ ∀ k, SmoothRealForm (A k) ∧
    CompactlySupportedRealForm (A k) ∧ closure {x | A k x ≠ 0} ⊆ O

/-- Pointwise scalar multiplication of actual forms, including rough data. -/
def scalarMultiply (η : M.Carrier → ℝ) (A : GradedRealForm M) : GradedRealForm M :=
  fun k x => η x • A k x

section Hilbert
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical complexification of the actual real L² pairing. Exact
pairing and dense COMPLEX test image exclude unrelated or zero realizations.
The embedding is total only for notation; constraints apply to actual L² data. -/
def ComplexL2Binding (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (ι : GradedRealForm M → H) : Prop :=
  ι 0 = 0 ∧
  (∀ A B, GradedL2 g (μ.restrict O) A → GradedL2 g (μ.restrict O) B →
    ι (A + B) = ι A + ι B) ∧
  (∀ (a : ℝ) A, GradedL2 g (μ.restrict O) A → ι (a • A) = (a : ℂ) • ι A) ∧
  (∀ A B, GradedL2 g (μ.restrict O) A → GradedL2 g (μ.restrict O) B →
    Integrable (gradedInner g A B) (μ.restrict O) ∧
    inner ℂ (ι A) (ι B) = ((∫ x in O, gradedInner g A B x ∂μ) : ℂ)) ∧
  (∀ A B, GradedL2 g (μ.restrict O) A → GradedL2 g (μ.restrict O) B →
    (ι A = ι B ↔ ∀ k, ∀ᵐ x ∂μ.restrict O, A k x = B k x)) ∧
  Dense {u : H | ∃ A B : GradedRealForm M,
    GradedTest g (μ.restrict O) O A ∧ GradedTest g (μ.restrict O) O B ∧
    u = ι A + Complex.I • ι B}

/-- Actual bounded scalar action, characterized on all real L² data and hence
on their dense complex span. Its norm is controlled by each actual bound B. -/
def ScalarMultiplierBinding (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (ι : GradedRealForm M → H)
    (mult : (M.Carrier → ℝ) → H →L[ℂ] H) : Prop :=
  ∀ η : M.Carrier → ℝ, Measurable η → ∀ B : ℝ, 0 ≤ B → (∀ x ∈ O, |η x| ≤ B) →
    ‖mult η‖ ≤ B ∧ ∀ A, GradedL2 g (μ.restrict O) A →
      mult η (ι A) = ι (scalarMultiply η A)

/-- Exact closure of the actual complexified compact Dirac graph, together
with its full distributional weak graph. Both equalities include the domain. -/
def CompleteDiracBinding (g : HermitianField M) (μ : Measure M.Carrier)
    (ι : GradedRealForm M → H) (D : H →ₗ.[ℂ] H) : Prop :=
  Dense (D.domain : Set H) ∧ IsSelfAdjoint D ∧
  (∀ u v : H, (u, v) ∈ D.graph ↔
    (u, v) ∈ closure {p : H × H | ∃ A W B Z : GradedRealForm M,
      DiracCorePair g μ A W ∧ DiracCorePair g μ B Z ∧
      p = (ι A + Complex.I • ι B, ι W + Complex.I • ι Z)}) ∧
  ∀ u v : H, (u, v) ∈ D.graph ↔ ∀ A W : GradedRealForm M,
    DiracCorePair g μ A W → inner ℂ u (ι W) = inner ℂ v (ι A)

end Hilbert

/-- Existence OUTPUT from actual geometry: no H, ι, D or multiplier is an inlet. -/
def CompleteDiracRealizationOutput (g : HermitianField M) (μ : Measure M.Carrier) : Prop :=
  ∃ (H : Type) (normH : NormedAddCommGroup H),
    letI := normH
    ∃ innerH : InnerProductSpace ℂ H,
      letI := innerH
      ∃ completeH : CompleteSpace H,
        letI := completeH
        ∃ (ι : GradedRealForm M → H) (D : H →ₗ.[ℂ] H)
          (mult : (M.Carrier → ℝ) → H →L[ℂ] H),
          ComplexL2Binding g μ Set.univ ι ∧
          ScalarMultiplierBinding g μ Set.univ ι mult ∧ CompleteDiracBinding g μ ι D

/-- Computed zero extension of the same actual section; no generator is
extended by zero. -/
def zeroExtend (O : Set M.Carrier) (A : GradedRealForm M) : GradedRealForm M :=
  fun k x => @ite _ (x ∈ O) (Classical.propDecidable _) (A k x) 0

/-- The actual d and δ triple on compact tests. -/
def CoreDerivativeTriple (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (A dA deltaA : GradedRealForm M) : Prop :=
  GradedTest g (μ.restrict O) O A ∧ GradedTest g (μ.restrict O) O dA ∧
  GradedTest g (μ.restrict O) O deltaA ∧ dA 0 = 0 ∧
  (∀ k, RepresentsExterior (A k) (dA (k + 1))) ∧
  ∀ k, RepresentsCodifferential g (A (k + 1)) (deltaA k)

section Energy
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closure in the sum of the L² norms of section, d and δ, with support in O.
This is the source's componentwise zero-Dirichlet form domain; no maximal
first-order graph is substituted at the boundary. -/
def EnergyGraphClosure (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (ι : GradedRealForm M → H) (u p q : H) : Prop :=
  (u, p, q) ∈ closure {v : H × H × H | ∃ A dA deltaA B dB deltaB : GradedRealForm M,
    CoreDerivativeTriple g μ O A dA deltaA ∧ CoreDerivativeTriple g μ O B dB deltaB ∧
    v = (ι A + Complex.I • ι B, ι dA + Complex.I • ι dB,
      ι deltaA + Complex.I • ι deltaB)}

/-- The full variational graph of □/2, exactly the same actual d/δ closed
form with its fixed one-half normalization. No desired smoothing is an inlet. -/
def FriedrichsHeatBinding (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (ι : GradedRealForm M → H)
    (A : H →ₗ.[ℂ] H) (T : ℝ → H →L[ℂ] H) : Prop :=
  NonnegativeSelfAdjoint A ∧ IsHeatOf A T ∧ ∀ u w : H,
    (u, w) ∈ A.graph ↔ ∃ p q : H, EnergyGraphClosure g μ O ι u p q ∧
      ∀ v r s : H, EnergyGraphClosure g μ O ι v r s →
        inner ℂ w v = (inner ℂ p r + inner ℂ q s) / 2

/-- Normalized square graph including both domains: A=D²/2. -/
def HalfSquareGraph (D A : H →ₗ.[ℂ] H) : Prop :=
  ∀ u w : H, (u, w) ∈ A.graph ↔ ∃ v : H,
    (u, v) ∈ D.graph ∧ (v, (2 : ℂ) • w) ∈ D.graph

variable {HO : Type} [NormedAddCommGroup HO] [InnerProductSpace ℂ HO] [CompleteSpace HO]

/-- Both represented maps use the same μ, actual O and pointwise sections.
J is zero extension and P its adjoint restriction, as in L26. -/
def RestrictionZeroExtensionBinding (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (ι : GradedRealForm M → H) (ιO : GradedRealForm M → HO)
    (J : HO →ₗᵢ[ℂ] H) (P : H →L[ℂ] HO) : Prop :=
  (∀ A, GradedL2 g μ A → P (ι A) = ιO A) ∧
  (∀ A, GradedL2 g (μ.restrict O) A → J (ιO A) = ι (zeroExtend O A)) ∧
  ∀ u v, inner ℂ (P u) v = inner ℂ u (J v)

end Energy

/-- Existence of the actual normalized domain realization, not a free
operator or Hilbert-space hypothesis. Smoothness remains a downstream goal. -/
def DomainFriedrichsRealizationOutput (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) : Prop :=
  ∃ (H : Type) (normH : NormedAddCommGroup H),
    letI := normH
    ∃ innerH : InnerProductSpace ℂ H,
      letI := innerH
      ∃ completeH : CompleteSpace H,
        letI := completeH
        ∃ (ι : GradedRealForm M → H) (A : H →ₗ.[ℂ] H) (T : ℝ → H →L[ℂ] H),
          ComplexL2Binding g μ O ι ∧ FriedrichsHeatBinding g μ O ι A T

end Yau.HeatConcreteBindings
