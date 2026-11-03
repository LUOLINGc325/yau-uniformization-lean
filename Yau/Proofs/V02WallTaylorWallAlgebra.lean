import Yau.Proofs.V02WallTaylorFactors
import Yau.Proofs.V03Walls

/-! The cleared identities refer to the original cutoff walls and recover
the original geometric boundary region. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundaryRegion_of_positive_walls {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {y : CotangentPoint X.manifold}
    (hb : 0 < deltaBase d j y.1) (hf : 0 < deltaFiber d j y) :
    y ∈ boundaryRegion d j := by
  have hp := setup_wallProfiles hd
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  exact ⟨(div_lt_one hA).mp ((hp.2.2.1 _).2.2.1.mp hb),
    (div_lt_one (sq_pos_of_pos hB)).mp ((hp.2.2.2 _).2.2.1.mp hf)⟩

theorem boundaryRegion_persists_of_wall_factors {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 1 ≤ a) {y y' : CotangentPoint X.manifold}
    (hy : y ∈ boundaryRegion d j) {Rb Rf : ℝ} (hRb : |Rb| ≤ 1 / 2) (hRf : |Rf| ≤ 1 / 2)
    (heb : deltaBase d j y'.1 = deltaBase d j y.1 + wallPower d j a y * Rb)
    (hef : deltaFiber d j y' = deltaFiber d j y + wallPower d j a y * Rf) :
    y' ∈ boundaryRegion d j := by
  have hp := setup_wallProfiles hd
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  have hb := deltaBase_pos hp hA hy.1
  have hf := deltaFiber_pos hp hB hy.2
  apply boundaryRegion_of_positive_walls hd j
  · rw [heb]
    exact wall_factor_positive ha hb (deltaBase_le_one hp j y.1)
      ⟨hf.le, deltaFiber_le_one hp j y⟩ hRb
  · rw [hef]
    have he : wallPower d j a y = (deltaFiber d j y * deltaBase d j y.1) ^ a := by
      simp only [wallPower, wallProduct, mul_comm]
    rw [he]
    exact wall_factor_positive ha hf (deltaFiber_le_one hp j y)
      ⟨hb.le, deltaBase_le_one hp j y.1⟩ hRf

theorem actual_reciprocal_walls_difference {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 2 ≤ a) {y y' : CotangentPoint X.manifold}
    (hy : y ∈ boundaryRegion d j) {Rb Rf : ℝ} (hRb : |Rb| ≤ 1 / 2) (hRf : |Rf| ≤ 1 / 2)
    (heb : deltaBase d j y'.1 = deltaBase d j y.1 + wallPower d j a y * Rb)
    (hef : deltaFiber d j y' = deltaFiber d j y + wallPower d j a y * Rf) :
    (wallBase d j y'.1 + wallFiber d j y') - (wallBase d j y.1 + wallFiber d j y) =
      -(wallInverseMultiplier a (deltaBase d j y.1) (deltaFiber d j y) * Rb) /
        (1 + wallRatioMultiplier a (deltaBase d j y.1) (deltaFiber d j y) * Rb) +
      -(wallInverseMultiplier a (deltaFiber d j y) (deltaBase d j y.1) * Rf) /
        (1 + wallRatioMultiplier a (deltaFiber d j y) (deltaBase d j y.1) * Rf) := by
  have hp := setup_wallProfiles hd
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  have hb := deltaBase_pos hp hA hy.1
  have hf := deltaFiber_pos hp hB hy.2
  have hub : deltaBase d j y.1 ∈ Set.Icc 0 1 := ⟨hb.le, deltaBase_le_one hp j y.1⟩
  have huf : deltaFiber d j y ∈ Set.Icc 0 1 := ⟨hf.le, deltaFiber_le_one hp j y⟩
  have hbr := (wall_ratio_bounds (a := a) hub huf hRb).1
  have hfr := (wall_ratio_bounds (a := a) huf hub hRf).1
  have hbi := reciprocal_wall_difference ha hb.ne' (by linarith :
    1 + wallRatioMultiplier a (deltaBase d j y.1) (deltaFiber d j y) * Rb ≠ 0)
  have hfi := reciprocal_wall_difference ha hf.ne' (by linarith :
    1 + wallRatioMultiplier a (deltaFiber d j y) (deltaBase d j y.1) * Rf ≠ 0)
  unfold wallBase wallFiber
  rw [heb, hef]
  have hpow : wallPower d j a y = (deltaBase d j y.1 * deltaFiber d j y) ^ a := rfl
  rw [hpow]
  rw [mul_comm (deltaFiber d j y) (deltaBase d j y.1)] at hfi
  linarith

theorem actual_log_walls_difference {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 1 ≤ a) {y y' : CotangentPoint X.manifold}
    (hy : y ∈ boundaryRegion d j) {Rb Rf : ℝ} (hRb : |Rb| ≤ 1 / 2) (hRf : |Rf| ≤ 1 / 2)
    (heb : deltaBase d j y'.1 = deltaBase d j y.1 + wallPower d j a y * Rb)
    (hef : deltaFiber d j y' = deltaFiber d j y + wallPower d j a y * Rf) :
    Real.log (wallProduct d j y') - Real.log (wallProduct d j y) =
      Real.log (1 + wallRatioMultiplier a (deltaBase d j y.1) (deltaFiber d j y) * Rb) +
      Real.log (1 + wallRatioMultiplier a (deltaFiber d j y) (deltaBase d j y.1) * Rf) := by
  have hp := setup_wallProfiles hd
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  have hb := deltaBase_pos hp hA hy.1
  have hf := deltaFiber_pos hp hB hy.2
  have hy' := boundaryRegion_persists_of_wall_factors hd j a ha hy hRb hRf heb hef
  have hb' := deltaBase_pos hp hA hy'.1
  have hf' := deltaFiber_pos hp hB hy'.2
  have hbr := (wall_ratio_bounds (a := a) ⟨hb.le, deltaBase_le_one hp j y.1⟩
    ⟨hf.le, deltaFiber_le_one hp j y⟩ hRb).1
  have hfr := (wall_ratio_bounds (a := a) ⟨hf.le, deltaFiber_le_one hp j y⟩
    ⟨hb.le, deltaBase_le_one hp j y.1⟩ hRf).1
  have hbi := log_wall_difference ha hb.ne' (by linarith :
    1 + wallRatioMultiplier a (deltaBase d j y.1) (deltaFiber d j y) * Rb ≠ 0)
  have hfi := log_wall_difference ha hf.ne' (by linarith :
    1 + wallRatioMultiplier a (deltaFiber d j y) (deltaBase d j y.1) * Rf ≠ 0)
  have hef' : deltaFiber d j y' = deltaFiber d j y +
      (deltaFiber d j y * deltaBase d j y.1) ^ a * Rf := by
    simpa only [wallPower, wallProduct, mul_comm] using hef
  change deltaBase d j y'.1 = deltaBase d j y.1 +
    (deltaBase d j y.1 * deltaFiber d j y) ^ a * Rb at heb
  rw [← heb] at hbi
  rw [← hef'] at hfi
  unfold wallProduct
  rw [Real.log_mul hb'.ne' hf'.ne', Real.log_mul hb.ne' hf.ne']
  linarith

end Yau.Blueprint.V02WallTaylorProof
