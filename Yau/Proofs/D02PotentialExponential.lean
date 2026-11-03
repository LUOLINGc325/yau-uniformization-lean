import Yau.Proofs.D02PotentialBounds
import Yau.Proofs.D02RieszRadius
import Yau.Proofs.D02Jensen

/-! A small atom of the actual limiting Riesz measure gives a uniform
exponential integral for the entire original sequence, including its
finitely many initial terms. -/

open scoped Topology ContDiff CompactlySupported ENNReal
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau

theorem local_uniform_exp_of_riesz_limit {U : Set ℂ} (hU : IsOpen U)
    (ψ : ℕ → ℂ → ℝ) (u : ℂ → ℝ) (μ : Measure ℂ)
    (hψ : ∀ j, ContDiffOn ℝ ∞ (ψ j) U)
    (hΔ : ∀ j z, z ∈ U → 0 ≤ LeafCandidates.realPlanarLaplacian (ψ j) z)
    (hlocal : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      IntegrableOn u K volume ∧ Tendsto (fun j => ∫ z in K, |ψ j z - u z|) atTop (𝓝 0))
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ χ : C_c(ℂ, ℝ), tsupport χ ⊆ U →
      Tendsto (fun j => ∫ z, χ z ∂D02RieszAux.smoothRieszOn U (ψ j)) atTop (𝓝 (∫ z, χ z ∂μ)))
    {z₀ : ℂ} (hz : z₀ ∈ U) (hatom : μ {z₀} < 1) :
    ∃ r C : ℝ, 0 < r ∧ closedBall z₀ r ⊆ U ∧ 0 ≤ C ∧ ∀ j,
      IntegrableOn (fun z => Real.exp (-((3 : ℝ) / 2) * ψ j z)) (ball z₀ r) volume ∧
      (∫ z in ball z₀ r, Real.exp (-((3 : ℝ) / 2) * ψ j z)) ≤ C := by
  obtain ⟨R, hR, hRU, _, _, hlate⟩ :=
    D02RieszAux.exists_disc_eventually_mass_lt hU hψ hμ hvague hz hatom
  obtain ⟨J, hJ⟩ := hlate.exists_forall_of_atTop
  obtain ⟨M, _, hM⟩ := uniform_compact_L1_of_L1_tendsto (isCompact_closedBall z₀ R)
    ψ u (fun j => ((hψ j).continuousOn.mono hRU))
    (hlocal _ (isCompact_closedBall z₀ R) hRU).1
    (hlocal _ (isCompact_closedBall z₀ R) hRU).2
  obtain ⟨B, hB, htail⟩ := D02JensenAux.uniform_exp_three_halves hU
    (fun j => ψ (j + J)) z₀ R hR hRU (fun j => hψ (j + J)) (fun j => hΔ (j + J))
    1 M (by norm_num) (by norm_num) (fun j => by
      simpa only [ENNReal.ofReal_one] using (hJ (j + J) (by omega)).le)
    (fun j => hM (j + J))
  let I : ℕ → ℝ := fun j => ∫ z in ball z₀ (R / 4), Real.exp (-((3 : ℝ) / 2) * ψ j z)
  let A : ℝ := ∑ j ∈ Finset.range J, max 0 (I j)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => le_max_left 0 (I j))
  have hsmall : closedBall z₀ (R / 4) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hRU
  refine ⟨R / 4, B + A, by positivity, hsmall, add_nonneg hB hA, fun j => ⟨?_, ?_⟩⟩
  · exact ((Real.continuous_exp.comp_continuousOn
      (((hψ j).continuousOn.mono hsmall).const_mul (-((3 : ℝ) / 2)))).integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  · by_cases hj : j < J
    · have hi : max 0 (I j) ≤ A := Finset.single_le_sum
        (fun k _ => le_max_left 0 (I k)) (Finset.mem_range.mpr hj)
      change I j ≤ B + A
      linarith [le_max_right 0 (I j)]
    · have hjJ : J ≤ j := Nat.le_of_not_gt hj
      have ht := (htail (j - J)).2
      rw [Nat.sub_add_cancel hjJ] at ht
      change I j ≤ B + A
      change I j ≤ B at ht
      linarith

end Yau.NodeProofs.D02Aux
