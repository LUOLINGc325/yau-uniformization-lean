import Yau.Proofs.C05RicciCubicJetsAlgebra

/-! The actual cubic contraction uses only the same-point Ricci jets through order two. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciCubicJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05RicciSquareJetsAux
open Yau.Proofs.C05RicciSquareJetsAux.Generic
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem realRicci_generic_jet (k : HermitianField M) (c : M.Carrier) (j : ℕ) :
    jet k c (realRicciJet k c 0) j = realRicciJet k c j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change covariantD k c (jet k c (realRicciJet k c 0) j) =
        covariantD k c (realRicciJet k c j)
      rw [ih]

theorem cubicJet_norm_le_two (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (realRicciJet k c j z) ≤ B)
    (m : ℕ) (hm : m ≤ 2) :
    metricTensorNorm (realMetricFn k c z) (cubicJet k c m z) ≤
      16 * (2*n:ℕ) * Real.sqrt (2*n:ℕ) * B ^ 3 := by
  let A := realRicciJet k c 0
  have hA := realRicciJet_contDiffOn k hk c 0
  have hJA : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (jet k c A j z) ≤ B := by
    intro j hj
    rw [realRicci_generic_jet]
    exact hR j hj
  have hC : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z)
      (jet k c (compositionField k c A) j z) ≤ 4 * Real.sqrt (2*n:ℕ) * B ^ 2 :=
    composition_jet_norm_le_two k hk c A hA hz hB hJA
  have H := word_covariantJet_norm_le_two ricciSquareWord k hk c
    (compositionField k c A) A (compositionField_contDiffOn k hk c A hA) hA hz
    (by positivity : 0 ≤ 4 * Real.sqrt (2*n:ℕ) * B ^ 2) hB hC hJA m hm
  calc
    _ = metricTensorNorm (realMetricFn k c z)
        (jet k c (fun u => ricciSquareWord.eval (realMetricFn k c u)⁻¹
          (compositionField k c A u) (A u)) m z) := by
      interval_cases m <;> rfl
    _ ≤ 4 * (2*n:ℕ) * (4 * Real.sqrt (2*n:ℕ) * B ^ 2) * B := H
    _ = _ := by ring

theorem scalarJetNorm_ricciCube_le_sqrt (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (m : ℕ) (hm : m ≤ 2) (x : M.Carrier)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ j ≤ 2, realRicciJetNorm k j x ≤ B) :
    scalarJetNorm k (ricciCube k) m x ≤
      8 * (2*n:ℕ) * Real.sqrt (2*n:ℕ) * B ^ 3 := by
  have hbound := cubicJet_norm_le_two k hk x (mem_extChartAt_target x) hB
    (fun j hj => hR j hj) m hm
  unfold scalarJetNorm
  simp only [chartPt]
  rw [scalarJet_ricciCube_eq k hk hK x m (mem_extChartAt_target x),
    sqrt_covTensorNormSq_const_mul]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  calc
    _ ≤ (1/2:ℝ) * (16 * (2*n:ℕ) * Real.sqrt (2*n:ℕ) * B ^ 3) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end Yau.Proofs.C05RicciCubicJetsAux
