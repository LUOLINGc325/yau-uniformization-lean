import Yau.Proofs.C04PullbackOrder
import Yau.Proofs.C04CompactContraction
import Yau.Proofs.Y03CenterFrame

/-! The original C02 charts satisfy the original C03 static distortion premises. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem pullback_zero_eq_conjugate {M : ComplexManifold n} (k : HermitianField M)
    (p : M.Carrier) (Φ : ComplexVector n → M.Carrier) (hΦ : Φ 0 = p) :
    let P := Blueprint.Alignment.Y03Proof.centerFrameMatrix p Φ
    P.conjTranspose * gMat k p * P = pullbackMat k Φ 0 := by
  dsimp only
  ext i j
  rw [Blueprint.Alignment.Y03Proof.gMat_conjugate_apply,
    Blueprint.Alignment.Y03Proof.centerFrameMatrix_chartVec,
    Blueprint.Alignment.Y03Proof.centerFrameMatrix_chartVec]
  unfold pullbackMat
  rw [hΦ]

theorem unitary_frame_isUnit {H P : Herm n} (hgram : P.conjTranspose * H * P = 1) : IsUnit P := by
  apply (Matrix.isUnit_iff_isUnit_det P).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hh := congrArg Matrix.det hgram
  simp only [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at hh
  exact zero_ne_one hh

theorem conjugate_order_reflect (A B P : Herm n) (hP : IsUnit P)
    (hAB : HermLE (P.conjTranspose * A * P) (P.conjTranspose * B * P)) : HermLE A B := by
  change (P.conjTranspose * B * P - P.conjTranspose * A * P).PosSemidef at hAB
  have hh : (P.conjTranspose * (B - A) * P).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul] using hAB
  exact (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hP).mp hh

theorem original_chart_distortion (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hCharts : UniformCharts X h) (hStatic : StaticDistortion X)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ r c C T D : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧ 0 ≤ T ∧ 0 < D ∧
      ∀ t, T ≤ t → ∀ p ∈ K, ∃ Φ : ComplexVector n → Pt X,
        UnitaryChart (h t) p Φ r c C ∧
        Real.sqrt (relMaxEigenvalue 1 (pullbackMat X.metric.form Φ 0)) ≤
          D * (1 + Real.sqrt (relMinEigenvalue 1 (pullbackMat X.metric.form Φ 0))) ^ D := by
  obtain ⟨r, c, C, T₀, hr, hc, hC, Cm, hcharts⟩ := hCharts K hK
  obtain ⟨D, hD, hdistortion⟩ := hStatic r c hr hc K hK
  refine ⟨r, c, C, max T₀ 0, D, hr, hc, hC, le_max_right _ _, hD, ?_⟩
  intro t ht p hp
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
  obtain ⟨Φ, hΦ, hCm⟩ := hcharts t ((le_max_left _ _).trans ht) p hp
  refine ⟨Φ, hΦ, hdistortion Φ hΦ.1 ?_ ?_⟩
  · simpa only [hΦ.2.1] using hp
  · intro z hz
    have hkg := pullbackMat_order (h t) X.metric.form Φ z (hf.2.2.2.2.1 t ht0 (Φ z))
    exact hermLE_trans (hΦ.2.2.2 z hz).1 hkg

end Yau.Proofs.C04Aux
