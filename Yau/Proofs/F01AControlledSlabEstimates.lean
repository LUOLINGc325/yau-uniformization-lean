import Yau.Proofs.F01AUniquePartialAssembly
import Yau.Proofs.F01ControlledUniformSolutionSandwich

/-! The released controlled a priori theorem gives one metric and scalar
budget before every endpoint and every actual solution witness. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

/-- Genuine common bounds on every closed slab through the target horizon. -/
theorem controlled_native_slab_estimates (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {D : ℝ} (hD : 0 < D) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ T, 0 < T → T ≤ D / 2 → ∀ h U,
      NativePotentialSlab α T h U → ∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef ∧
        |flowLogDetRatio α h x t| ≤ A ∧ |U x t| ≤ A * t := by
  obtain ⟨L0, hL0, hbounds⟩ := controlled_uniform_solution_sandwich X o u hu Ξ hΞ hRic hD
  refine ⟨L0, hL0, ?_⟩
  intro L hLL0 ho
  dsimp only
  obtain ⟨C, A, hC, hA, hbound⟩ := hbounds L hLL0 ho
  refine ⟨C, A, hC, hA, ?_⟩
  intro T hT hTD h U hsol
  obtain ⟨hh0, hh, hU, hU0, Cpre, hCpre, hdata⟩ := hsol
  exact hbound h U T Cpre hT (by linarith) hCpre hh hU hh0 hU0 hdata

/-- The common sandwich is independent of all solution choices. -/
theorem controlled_slab_common_sandwich (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {D : ℝ} (hD : 0 < D) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T, 0 < T → T ≤ D / 2 → ∀ h U,
      NativePotentialSlab α T h U → ∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef := by
  obtain ⟨L0, hL0, hbound⟩ := controlled_native_slab_estimates X o u hu Ξ hΞ hRic hD
  refine ⟨L0, hL0, ?_⟩
  intro L hL ho
  dsimp only
  obtain ⟨C, A, hC, hA, hbound'⟩ := hbound L hL ho
  exact ⟨C, hC, fun T hT hTD h U hsol x t ht =>
    ⟨(hbound' T hT hTD h U hsol x t ht).1, (hbound' T hT hTD h U hsol x t ht).2.1⟩⟩

/-- Replace the preliminary comparison constant by the genuine uniform one,
retaining the exact metric and potential witnesses. -/
theorem NativePotentialSlab.with_comparison {M : ComplexManifold n}
    {g : HermitianField M} {T C : ℝ} {h : ℝ → HermitianField M}
    {U : M.Carrier → ℝ → ℝ} (hsol : NativePotentialSlab g T h U) (hC : 1 ≤ C)
    (hbound : ∀ x t, t ∈ Icc 0 T →
      (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h t) x).PosSemidef) :
    NativePotentialTuple g T C h U := by
  obtain ⟨hh0, hh, hU, hU0, Cpre, hCpre, hdata⟩ := hsol
  exact ⟨hC, hh0, hh, hU, hU0, fun x t ht =>
    ⟨(hbound x t ht).1, (hbound x t ht).2,
      (hdata x t ht).2.2.1, (hdata x t ht).2.2.2⟩⟩

end Yau.NodeProofs.F01Aux
