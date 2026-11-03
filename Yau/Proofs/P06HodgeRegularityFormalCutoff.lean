import Yau.Proofs.P06HodgeRegularityFormalTestIntegral
import Yau.Proofs.P06HodgeRegularityFormalH1

/-! Actual compact localization of a local forward formal equation.
All value and flux terms contain only raw values of the input and source. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]

theorem regularityDivergenceFormal_cutoff
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (B : α → α → ι → E → ℝ) (C : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i)) (hC : ∀ r c, ContDiff ℝ ∞ (C r c))
    {O : Set E} (hO : IsOpen O) {χ : E → ℝ} (hχ : regularityTest O χ)
    (U W : E → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hW : ∀ r, MemLp (fun z => W z r) 2 (ν.restrict O))
    (hweak : ∀ r φ, regularityTest O φ →
      (∫ z, ∑ c, divergenceFormalTest v a B C φ z r c * U z c ∂ν) =
        ∫ z, φ z * W z r ∂ν) :
    divergenceSystemWeakEquation ν v a B C (fun z c => χ z * U z c)
      (regularityFormalCutoffValue v a B χ U W) (regularityFormalCutoffFlux v a χ U) := by
  classical
  let V (z : E) (r : α) := ∑ c, localizedDivergenceValueCoefficient v a B χ z r c * U z c
  let F := regularityFormalCutoffFlux v a χ U
  have hcut c := regularityCompact_mul_memLp ν hO hχ.1 hχ.2.1 hχ.2.2 (hU c)
  have hcutW r := regularityCompact_mul_memLp ν hO hχ.1 hχ.2.1 hχ.2.2 (hW r)
  have hV r : MemLp (fun z => V z r) 2 ν := by
    apply memLp_finsetSum Finset.univ
    intro c _
    have ht := regularityLocalizedValue_test v a B ha hB hχ r c
    exact regularityCompact_mul_memLp ν hO ht.1 ht.2.1 ht.2.2 (hU c)
  have hF r i := regularityFormalCutoffFlux_memLp ν v a ha hO hχ U hU r i
  intro r φ hφ hcφ
  have htφ : regularityTest Set.univ φ := ⟨hφ,hcφ,Set.subset_univ _⟩
  have hφL : MemLp φ 2 ν := hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hDφL i : MemLp (fun z => fderiv ℝ φ z (v i)) 2 ν :=
    (regularityTest_direction htφ (v i)).1.continuous.memLp_of_hasCompactSupport
      (regularityTest_direction htφ (v i)).2.1
  have hrow : Integrable (fun z => ∑ c,
      divergenceFormalTest v a B C φ z r c * (χ z * U z c)) ν := by
    apply integrable_finsetSum Finset.univ
    intro c _
    have ht := regularityDivergenceFormal_test v a B C ha hB hC htφ r c
    have htL : MemLp _ 2 ν := ht.1.continuous.memLp_of_hasCompactSupport ht.2.1
    exact htL.integrable_mul (hcut c)
  have hval : Integrable (fun z => V z r * φ z) ν := (hV r).integrable_mul hφL
  have hflux i : Integrable (fun z => F z r i * fderiv ℝ φ z (v i)) ν := (hF r i).integrable_mul (hDφL i)
  have hfluxsum : Integrable (fun z => ∑ i, F z r i * fderiv ℝ φ z (v i)) ν :=
    integrable_finsetSum Finset.univ fun i _ => hflux i
  have hpoint (z : E) : (∑ c, divergenceFormalTest v a B C φ z r c * (χ z * U z c)) =
    (∑ c, divergenceFormalTest v a B C (fun y => χ y * φ y) z r c * U z c) +
      V z r * φ z - ∑ i, F z r i * fderiv ℝ φ z (v i) :=
    divergenceFormalTest_mul_sum v a B C U χ φ hχ.1 hφ z r
  have htestrow : Integrable (fun z => ∑ c,
      divergenceFormalTest v a B C (fun y => χ y * φ y) z r c * U z c) ν :=
    ((hrow.sub hval).add hfluxsum).congr (Eventually.of_forall fun z => by
      dsimp only [Pi.add_apply, Pi.sub_apply]
      linarith [hpoint z])
  have hintegral :
      (∫ z, ∑ c, divergenceFormalTest v a B C φ z r c * (χ z * U z c) ∂ν) =
      (∫ z, ∑ c, divergenceFormalTest v a B C (fun y => χ y * φ y) z r c * U z c ∂ν) +
        (∫ z, V z r * φ z ∂ν) - ∑ i, ∫ z, F z r i * fderiv ℝ φ z (v i) ∂ν := by
    simp_rw [hpoint]
    have hsub := integral_sub (htestrow.add hval) hfluxsum
    have hadd := integral_add htestrow hval
    simp only [Pi.add_apply, Pi.sub_apply] at hsub hadd
    rw [hsub, hadd,
      integral_finsetSum Finset.univ (fun i _ => hflux i)]
  have hφχ : regularityTest O (fun z => χ z * φ z) := regularityTest_mul hχ hφ
  rw [hweak r _ hφχ] at hintegral
  have hsource : (∫ z, φ z * regularityFormalCutoffValue v a B χ U W z r ∂ν) =
      (∫ z, (χ z * φ z) * W z r ∂ν) + ∫ z, V z r * φ z ∂ν := by
    have hleft : Integrable (fun z => (χ z * φ z) * W z r) ν :=
      ((hcutW r).integrable_mul hφL).congr (Eventually.of_forall fun z => by
        dsimp only [Pi.mul_apply]
        ring)
    have heq : (fun z => φ z * regularityFormalCutoffValue v a B χ U W z r) =
        fun z => (χ z * φ z) * W z r + V z r * φ z := by
      funext z
      unfold regularityFormalCutoffValue V
      ring
    rw [heq, integral_add hleft hval]
  rw [← regularityDivergenceFormal_integral ν v a B C ha hB hC _ hcut hφ hcφ r, hsource]
  simpa only [mul_comm (fderiv ℝ φ _ (v _)) (regularityFormalCutoffFlux v a χ U _ _ _)] using hintegral

end Yau.NodeProofs.P06Aux
