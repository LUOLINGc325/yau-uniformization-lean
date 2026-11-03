import Mathlib

/-! The contraction on an actual closed Banach ball solves the source
fixed-point equation for a genuine bounded right inverse. -/

noncomputable section
namespace Yau.Proofs.F05Aux

theorem F05_contraction_equation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (B : F →L[ℝ] E)
    (hLB : L.comp B = ContinuousLinearMap.id ℝ F)
    (N : E → F) {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hLip : ∀ u v : E, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ K*‖u-v‖)
    (hSmall : ‖B‖*K ≤ (1/2 : ℝ)) (hZero : ‖B‖*‖N 0‖ ≤ r/2) :
    ∃ z : E, ‖z‖ ≤ r ∧ L z = N z := by
  let D : Set E := Metric.closedBall 0 r
  let Φ : E → E := fun u => B (N u)
  have hLipΦ (u v : E) (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) :
      ‖Φ u-Φ v‖ ≤ (1/2 : ℝ)*‖u-v‖ := by
    change ‖B (N u)-B (N v)‖ ≤ _
    rw [← map_sub]
    calc
      ‖B (N u-N v)‖ ≤ ‖B‖*‖N u-N v‖ := B.le_opNorm _
      _ ≤ ‖B‖*(K*‖u-v‖) := mul_le_mul_of_nonneg_left (hLip u v hu hv) (norm_nonneg _)
      _ ≤ (1/2 : ℝ)*‖u-v‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hSmall (norm_nonneg _)
  have hMap : Set.MapsTo Φ D D := by
    intro u hu
    have hNorm : ‖u‖ ≤ r := by simpa only [D,Metric.mem_closedBall,dist_zero_right] using hu
    have hStep := hLipΦ u 0 hNorm (by simpa only [norm_zero] using hr.le)
    simp only [sub_zero] at hStep
    have hSum : ‖Φ u‖ ≤ ‖Φ u-Φ 0‖+‖Φ 0‖ := by simpa only [add_comm] using norm_le_insert' (Φ u) (Φ 0)
    have hAtZero : ‖Φ 0‖ ≤ r/2 := (B.le_opNorm (N 0)).trans hZero
    have hResult : ‖Φ u‖ ≤ r := by
      simpa only [sub_zero] using (show ‖Φ u‖ ≤ r by linarith)
    simpa only [D,Metric.mem_closedBall,dist_zero_right] using hResult
  have hContract : ContractingWith (1/2) (hMap.restrict Φ D D) := by
    refine ⟨by norm_num,?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [Subtype.dist_eq,Set.MapsTo.val_restrict_apply,dist_eq_norm,
      NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      hLipΦ u.val v.val
        (by simpa only [D,Metric.mem_closedBall,dist_zero_right] using u.property)
        (by simpa only [D,Metric.mem_closedBall,dist_zero_right] using v.property)
  obtain ⟨z,hz,hFix,_,_⟩ := ContractingWith.exists_fixedPoint'
    (s := D) (f := Φ) Metric.isClosed_closedBall.isComplete hMap hContract
    (show (0 : E) ∈ D by simpa only [D,Metric.mem_closedBall,dist_self] using hr.le) (edist_ne_top _ _)
  refine ⟨z,by simpa only [D,Metric.mem_closedBall,dist_zero_right] using hz,?_⟩
  have hAt := DFunLike.congr_fun hLB (N z)
  change L (B (N z)) = N z at hAt
  exact (congrArg L hFix).symm.trans hAt

end Yau.Proofs.F05Aux
