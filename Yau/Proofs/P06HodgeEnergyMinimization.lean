import Yau.Proofs.P06HodgeEnergyRepresentation
import Yau.Proofs.P06HodgeEuler

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeImplicitResolvent_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (s : ℝ) (hs : 0 < s) (f : L2FormHilbert g μ 2) :
    ∃ u : HodgeEnergySpace g μ hμ, hodgeEnergyValue g μ hμ u = hodgeImplicitResolvent g μ hμ 2 s hs f ∧
      ∀ v : HodgeEnergySpace g μ hμ,
        hodgeEnergyPairing g μ hμ u v + s⁻¹ * inner ℝ (hodgeEnergyValue g μ hμ u) (hodgeEnergyValue g μ hμ v) =
          s⁻¹ * inner ℝ f (hodgeEnergyValue g μ hμ v) := by
  obtain ⟨u, he, hvar⟩ := hodgeCompleteGraph_energy g μ hμ (hodgeImplicitResolvent_graph g μ hμ 2 s hs f)
  refine ⟨u, he, ?_⟩
  intro v
  have hv := hvar v
  rw [inner_smul_left, inner_sub_left] at hv
  simp only [conj_trivial] at hv
  rw [← he] at hv
  linarith

theorem hodgeEnergy_difference_identity (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : L2FormHilbert g μ 2) (lam : ℝ)
    (u v : HodgeEnergySpace g μ hμ)
    (hvar : ∀ z : HodgeEnergySpace g μ hμ,
      hodgeEnergyPairing g μ hμ u z + lam * inner ℝ (hodgeEnergyValue g μ hμ u) (hodgeEnergyValue g μ hμ z) =
        lam * inner ℝ f (hodgeEnergyValue g μ hμ z)) :
    hodgeEnergy g μ hμ v + lam * ‖hodgeEnergyValue g μ hμ v - f‖ ^ 2 -
      (hodgeEnergy g μ hμ u + lam * ‖hodgeEnergyValue g μ hμ u - f‖ ^ 2) =
      hodgeEnergy g μ hμ (v - u) + lam * ‖hodgeEnergyValue g μ hμ (v - u)‖ ^ 2 := by
  have hv := hvar v
  have hu := hvar u
  rw [hodgeEnergyPairing_self, real_inner_self_eq_norm_sq] at hu
  have hq : hodgeEnergy g μ hμ (v - u) = hodgeEnergy g μ hμ v + hodgeEnergy g μ hμ u -
      2 * hodgeEnergyPairing g μ hμ u v := by
    simp only [hodgeEnergy, hodgeEnergyPairing, map_sub, norm_sub_sq_real]
    rw [real_inner_comm (hodgeEnergyExterior g μ hμ u) (hodgeEnergyExterior g μ hμ v),
      real_inner_comm (hodgeEnergyLower g μ hμ u) (hodgeEnergyLower g μ hμ v)]
    ring
  rw [hq, map_sub,
    norm_sub_sq_real (hodgeEnergyValue g μ hμ v) f,
    norm_sub_sq_real (hodgeEnergyValue g μ hμ u) f,
    norm_sub_sq_real (hodgeEnergyValue g μ hμ v) (hodgeEnergyValue g μ hμ u),
    real_inner_comm f (hodgeEnergyValue g μ hμ v),
    real_inner_comm f (hodgeEnergyValue g μ hμ u),
    real_inner_comm (hodgeEnergyValue g μ hμ u) (hodgeEnergyValue g μ hμ v)]
  nlinarith

theorem hodgeEnergy_minimizes (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : L2FormHilbert g μ 2) (lam : ℝ) (hlam : 0 ≤ lam)
    (u : HodgeEnergySpace g μ hμ)
    (hvar : ∀ z : HodgeEnergySpace g μ hμ,
      hodgeEnergyPairing g μ hμ u z + lam * inner ℝ (hodgeEnergyValue g μ hμ u) (hodgeEnergyValue g μ hμ z) =
        lam * inner ℝ f (hodgeEnergyValue g μ hμ z)) (v : HodgeEnergySpace g μ hμ) :
    hodgeEnergy g μ hμ u + lam * ‖hodgeEnergyValue g μ hμ u - f‖ ^ 2 ≤
      hodgeEnergy g μ hμ v + lam * ‖hodgeEnergyValue g μ hμ v - f‖ ^ 2 := by
  have he := hodgeEnergy_difference_identity g μ hμ f lam u v hvar
  have hq := hodgeEnergy_nonnegative g μ hμ (v - u)
  have hn := mul_nonneg hlam (sq_nonneg ‖hodgeEnergyValue g μ hμ (v - u)‖)
  linarith

/-- A genuine energy-decreasing projection competitor, with its sharp
Hilbert projection inequality, fixes the same actual resolvent value. -/
theorem hodgeEnergy_competitor_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : L2FormHilbert g μ 2) (lam : ℝ) (hlam : 0 < lam)
    (u v : HodgeEnergySpace g μ hμ)
    (hvar : ∀ z : HodgeEnergySpace g μ hμ,
      hodgeEnergyPairing g μ hμ u z + lam * inner ℝ (hodgeEnergyValue g μ hμ u) (hodgeEnergyValue g μ hμ z) =
        lam * inner ℝ f (hodgeEnergyValue g μ hμ z))
    (hq : hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ u)
    (hd : ‖hodgeEnergyValue g μ hμ v - f‖ ^ 2 ≤ ‖hodgeEnergyValue g μ hμ u - f‖ ^ 2 -
      ‖hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v‖ ^ 2) :
    hodgeEnergyValue g μ hμ u = hodgeEnergyValue g μ hμ v := by
  have hm := hodgeEnergy_minimizes g μ hμ f lam hlam.le u hvar v
  have hc := add_le_add hq (mul_le_mul_of_nonneg_left hd hlam.le)
  have hn : lam * ‖hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v‖ ^ 2 ≤ 0 := by
    linarith
  have hz : ‖hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v‖ ^ 2 = 0 := by
    exact le_antisymm ((mul_le_mul_iff_right₀ hlam).mp
      (by simpa only [zero_mul, mul_zero, mul_comm] using hn)) (sq_nonneg _)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v)]

end Yau.NodeProofs.P06Aux
