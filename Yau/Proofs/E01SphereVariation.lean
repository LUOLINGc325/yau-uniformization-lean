import Yau.Proofs.E01ContactSet
import Yau.Proofs.E01QuadraticBound

/-! Strictly descending contact directions give genuine small feasible sphere variations. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem exists_small_feasible_sphere_variation
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η)
    (H : Herm n) (hstrict : ∀ η ∈ unitContactSet v, ellipsoidQuadratic H η < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic (1 + (s : ℂ) • H) η : EReal) ≤ v η := by
  classical
  obtain ⟨κ, hκ, hneg⟩ := (isCompact_unitContactSet v hv hlower).exists_forall_le'
    (continuous_ellipsoidQuadratic_fiber H).neg.continuousOn
    (fun η hη => neg_pos.mpr (hstrict η hη))
  let K : Set (ComplexVector n) := Metric.sphere 0 1 ∩
    {η | -κ / 2 ≤ ellipsoidQuadratic H η}
  have hK : IsCompact K := (isCompact_sphere (0 : ComplexVector n) 1).inter_right
    (isClosed_le continuous_const (continuous_ellipsoidQuadratic_fiber H))
  have hvK : LowerSemicontinuousOn v K := hv.mono (fun η hη => hη.1)
  have hgapK : ∀ η ∈ K, (1 : EReal) < v η := by
    intro η hη
    apply lt_of_le_of_ne (hlower η hη.1)
    intro heq
    have hηc : η ∈ unitContactSet v := ⟨hη.1, heq.symm⟩
    have hnc := hneg η hηc
    have hq := hη.2
    change κ ≤ -ellipsoidQuadratic H η at hnc
    change -κ / 2 ≤ ellipsoidQuadratic H η at hq
    linarith
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_real_gap_of_lsc hK v hvK 1 hgapK
  let b : ℝ := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H‖
  have hb : 0 ≤ b := norm_nonneg _
  have hb1 : 0 < b + 1 := by positivity
  refine ⟨ε / (b + 1), div_pos hε hb1, fun s hs0 hs η hη => ?_⟩
  have hn : ‖η‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hη
  have hline : ellipsoidQuadratic (1 + (s : ℂ) • H) η =
      1 + s * ellipsoidQuadratic H η := by
    rw [ellipsoidQuadratic_add, ellipsoidQuadratic_one,
      ellipsoidQuadratic_real_smul, hn]
    norm_num
  rw [hline]
  by_cases hηK : η ∈ K
  · have hq : ellipsoidQuadratic H η ≤ b := by
      apply (le_abs_self _).trans
      simpa only [hn, one_pow, mul_one] using abs_ellipsoidQuadratic_le_opNorm H η
    have hs1 : s * (b + 1) < ε := (lt_div_iff₀ hb1).mp hs
    have hs2 : s * b < ε := (mul_lt_mul_of_pos_left (lt_add_one b) hs0).trans hs1
    have hsmul := mul_le_mul_of_nonneg_left hq hs0.le
    apply (EReal.coe_le_coe_iff.mpr ?_).trans (hgap η hηK)
    linarith
  · have hq : ellipsoidQuadratic H η < -κ / 2 := by
      apply lt_of_not_ge
      exact fun hq => hηK ⟨hη, hq⟩
    have hqneg : ellipsoidQuadratic H η < 0 := by linarith
    have hmul := mul_nonpos_of_nonneg_of_nonpos hs0.le hqneg.le
    apply (EReal.coe_le_coe_iff.mpr ?_).trans (hlower η hη)
    linarith

theorem exists_small_positive_sphere_variation
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η)
    (H : Herm n) (hH : H.IsHermitian)
    (hstrict : ∀ η ∈ unitContactSet v, ellipsoidQuadratic H η < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      (1 + (s : ℂ) • H).PosDef ∧
      ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic (1 + (s : ℂ) • H) η : EReal) ≤ v η := by
  obtain ⟨δ, hδ, hfeasible⟩ := exists_small_feasible_sphere_variation v hv hlower H hstrict
  let b : ℝ := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H‖
  have hb : 0 ≤ b := norm_nonneg _
  have hb1 : 0 < b + 1 := by positivity
  refine ⟨min δ (1 / (b + 1)), lt_min hδ (div_pos zero_lt_one hb1), fun s hs0 hs => ?_⟩
  refine ⟨one_add_matrix_line_posDef H hH hs0.le ?_,
    hfeasible s hs0 (hs.trans_le (min_le_left _ _))⟩
  have hs1 : s * (b + 1) < 1 :=
    (lt_div_iff₀ hb1).mp (hs.trans_le (min_le_right _ _))
  exact (mul_lt_mul_of_pos_left (lt_add_one b) hs0).trans hs1

end Yau.NodeProofs.E01Aux
