import Yau.Proofs.P06HodgeRegularityStrongChart

/-! Reconstruct actual alternating model tensors from the finite scalar
chart representatives, with joint smoothness and actual compact support. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeStrongChartScalar_tsupport {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (t : ℝ) :
    tsupport (hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c t) ⊆ tsupport χ := by
  by_cases ht : 0 < t
  · simp only [hodgeStrongChartScalar,dif_pos ht]
    exact (hodgeCanonicalChart_properties g μ hμ (t/2) (by positivity) x b χ hχ hcχ hχO c (h (t/2))).2.1
  · simp only [hodgeStrongChartScalar,dif_neg ht,tsupport_zero,Set.empty_subset]

def hodgeStrongChartModel {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (t : ℝ) (z : ComplexVector n) : HodgeJets.Fiber n k :=
  ∑ c, hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c t z • b c

theorem hodgeStrongChartModel_joint_contDiffOn {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      hodgeStrongChartModel g μ hμ h x b χ hχ hcχ hχO p.2 p.1) (Set.univ ×ˢ Set.Ioi 0) :=
  ContDiffOn.sum fun c _ =>
    (hodgeStrongChartScalar_joint_contDiffOn g μ hμ h hheat x b χ hχ hcχ hχO c).smul contDiffOn_const

theorem hodgeStrongChartModel_tsupport {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (t : ℝ) :
    tsupport (hodgeStrongChartModel g μ hμ h x b χ hχ hcχ hχO t) ⊆ tsupport χ := by
  classical
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra hzχ
  apply hz
  apply Finset.sum_eq_zero
  intro c _
  rw [image_eq_zero_of_notMem_tsupport
    (fun h0 => hzχ (hodgeStrongChartScalar_tsupport g μ hμ h x b χ hχ hcχ hχO c t h0)),zero_smul]

theorem hodgeStrongChartModel_ae {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) {t : ℝ} (ht : 0 < t)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hAt : realizeActualForm g μ A hA = h t) :
    hodgeStrongChartModel g μ hμ h x b χ hχ hcχ hχO t =ᵐ[lebesgueC n]
      (fun z => χ z • chartForm A x z) := by
  have hcoeff (c : α) : ∀ᵐ z ∂lebesgueC n,
      hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c t z = χ z * b.repr (chartForm A x z) c := by
    have hp := chartProjection_actual_ae g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap A hA
    rw [hAt] at hp
    filter_upwards [hodgeStrongChartScalar_ae g μ hμ h hheat x b χ hχ hcχ hχO c ht,hp] with z hz hraw
    rw [hz,hraw]
    rfl
  filter_upwards [ae_all_iff.mpr hcoeff] with z hz
  calc
    _ = ∑ c, (b.repr (χ z • chartForm A x z)) c • b c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hz c,map_smul, Finsupp.smul_apply,smul_eq_mul]
    _ = _ := b.sum_repr _

end Yau.NodeProofs.P06Aux
