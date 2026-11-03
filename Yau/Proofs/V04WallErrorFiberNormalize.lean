import Yau.Proofs.V04WallErrorFiberIdentity
import Yau.Proofs.V04WallErrorFiberCompact

/-! Fiber normalization places every admissible radius in the old compact
box before any new radius-dependent estimate is taken. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem one_le_admissible_radius {j : ℕ} {b : ℝ} (hb : (j + 1 : ℝ) ≤ b) : 1 ≤ b := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem normalized_point_mem_old_compact {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {b : ℝ} (hb : (j + 1 : ℝ) ≤ b) {y : CotangentPoint X.manifold}
    (hy : y ∈ boundaryRegion {d with B := Function.update d.B j b} j) :
    fiberScale ((b⁻¹ : ℝ) : ℂ) y ∈ boundaryCompact d j := by
  have hb1 := one_le_admissible_radius hb
  have hb0 : 0 < b := zero_lt_one.trans_le hb1
  have hBold := hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j
  have hBold1 : 1 ≤ d.B j := one_le_admissible_radius hBold.2.1
  refine ⟨hy.1.le, ?_⟩
  rw [dualNorm_fiberScale_real]
  have hyN : dualNorm (d.h 0) y.1 y.2 < b ^ 2 := by
    simpa only [Function.update_self] using hy.2
  have hnorm := mul_lt_mul_of_pos_left hyN (sq_pos_of_pos (inv_pos.mpr hb0))
  have hc : b⁻¹ ^ 2 * b ^ 2 = 1 := by field_simp
  rw [hc] at hnorm
  exact hnorm.le.trans (one_le_pow₀ hBold1)

theorem fiberScale_normalized_roundtrip {b : ℝ} (hb : b ≠ 0)
    (y : CotangentPoint X.manifold) :
    fiberScale (b : ℂ) (fiberScale ((b⁻¹ : ℝ) : ℂ) y) = y := by
  apply Prod.ext
  · rfl
  · change (b : ℂ) • ((b⁻¹ : ℝ) : ℂ) • y.2 = y.2
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hb, Complex.ofReal_one, one_smul]

theorem exists_fiber_uniform_bound {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ b : ℝ, (j + 1 : ℝ) ≤ b →
      ∀ y ∈ boundaryRegion {d with B := Function.update d.B j b} j,
      ∀ t ∈ Set.Icc 0 d.T, ∀ s ∈ Set.Icc d.cylinderTimeLo d.cylinderTimeHi,
      |fiberErrorScalar {d with B := Function.update d.B j b} j y t s| ≤
        M * (1 + b) ^ 6 *
          (wallProduct {d with B := Function.update d.B j b} j y ^ 6)⁻¹ := by
  obtain ⟨r, x, C, hC, hcover⟩ := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  choose M hM using fun i : Fin r => exists_fiber_chart_bound hd j (x i) (hC i).1 (hC i).2
  let B : ℝ := 1 + ∑ i, M i
  have hM0 : ∀ i, 0 ≤ M i := fun i => zero_le_one.trans (hM i).1
  have hB1 : 1 ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hM0 i)
  have hMi : ∀ i, M i ≤ B := by
    intro i
    have hi := Finset.single_le_sum (s := Finset.univ) (fun a _ => hM0 a) (Finset.mem_univ i)
    dsimp [B]
    linarith
  refine ⟨B, hB1, ?_⟩
  intro b hb y hy t ht s hs
  have hb1 := one_le_admissible_radius hb
  have hb0 : 0 < b := zero_lt_one.trans_le hb1
  have hn := normalized_point_mem_old_compact hd j hb hy
  rw [hcover] at hn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
  obtain ⟨z, hz, hzrep⟩ := hi
  have hyrep : y = cotangentChartInv (x i) (fiberDilation b z) := by
    calc
      y = fiberScale (b : ℂ) (fiberScale ((b⁻¹ : ℝ) : ℂ) y) :=
        (fiberScale_normalized_roundtrip hb0.ne' y).symm
      _ = fiberScale (b : ℂ) (cotangentChartInv (x i) z) := by rw [hzrep]
      _ = _ := fiberScale_chartInv (b : ℂ) (x i) z
  have hp : WallProfiles {d with B := Function.update d.B j b} := setup_wallProfiles (d := d) hd
  have hδo : 0 < deltaBase d j y.1 :=
    deltaBase_pos (setup_wallProfiles hd) (setup_index_bounds hd j).1 hy.1
  have hεo : 0 < deltaFiber {d with B := Function.update d.B j b} j y :=
    deltaFiber_pos hp (by simpa only [Function.update_self] using hb0) hy.2
  have hδ : deltaBase d j (cotangentChartInv (x i) z).1 ≠ 0 := by
    rw [hyrep] at hδo
    exact hδo.ne'
  have hε : normalizedFiberProfile d (x i) z ≠ 0 := by
    rw [hyrep, deltaFiber_update_dilation d j (x i) hb0.ne' z] at hεo
    exact hεo.ne'
  have hid := fiber_error_cleared_identity hd j (x i) hb0.ne' ((hC i).2 hz) ht s hδ hε
  rw [← hyrep] at hid
  have hinv : b⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(inv_pos.mpr hb0).le, (inv_le_one₀ hb0).mpr hb1⟩
  have hbound := ((hM i).2 z hz t ht s hs b⁻¹ hinv).trans (hMi i)
  have hprod : 0 < wallProduct {d with B := Function.update d.B j b} j y := by
    change 0 < deltaBase d j y.1 * deltaFiber {d with B := Function.update d.B j b} j y
    exact mul_pos hδo hεo
  have hQ : 0 < wallProduct {d with B := Function.update d.B j b} j y ^ 6 :=
    pow_pos hprod 6
  rw [← hid, abs_mul, abs_of_nonneg hQ.le] at hbound
  have herr : |fiberErrorScalar {d with B := Function.update d.B j b} j y t s| ≤
      B * (wallProduct {d with B := Function.update d.B j b} j y ^ 6)⁻¹ := by
    apply (le_div_iff₀ hQ).mpr
    simpa only [mul_comm] using hbound
  exact herr.trans (mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (zero_le_one.trans hB1) (one_le_pow₀ (by linarith : 1 ≤ 1 + b)))
    (inv_nonneg.mpr hQ.le))

end Yau.Blueprint.V04Proof.WallErrorAux
