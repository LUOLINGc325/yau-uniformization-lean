import Yau.LeafProofs.L05AutonomousAveragePairing

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Actual Fubini transfers the uniform spatial positive-part integral to the parabolic cylinder. -/
theorem auto_positive_cylinder_integral {n : ℕ} {r a b B : ℝ} (hab : a≤ b)
    {q : Point n → ℝ} (hq : ContinuousOn q (Metric.closedBall 0 r ×ˢ Icc a b))
    (hb : ∀ t∈Icc a b, (∫ x in Metric.ball (0 : Space n) r, max (q (x,t)) 0)≤ B) :
    IntegrableOn (fun p => max (q p) 0) (Metric.ball (0 : Space n) r ×ˢ Ioo a b) ∧
      (∫ p in Metric.ball (0 : Space n) r ×ˢ Ioo a b, max (q p) 0)≤ (b-a)*B := by
  have hcont := hq.sup (continuousOn_const (c := (0 : ℝ)))
  have hi : IntegrableOn (fun p => max (q p) 0) (Metric.ball (0 : Space n) r ×ˢ Ioo a b) :=
    (hcont.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set
      (prod_mono Metric.ball_subset_closedBall Ioo_subset_Icc_self)
  have hProd : Integrable (fun p : Point n => max (q p) 0)
      (((volume : Measure (Space n)).restrict (Metric.ball 0 r)).prod
        ((volume : Measure ℝ).restrict (Ioo a b))) := by
    simpa only [IntegrableOn,Measure.prod_restrict,← Measure.volume_eq_prod] using hi
  have hFubini := integral_prod_symm (fun p : Point n => max (q p) 0) hProd
  have hBound := integral_mono_ae hProd.integral_prod_right (integrable_const B) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hb t (Ioo_subset_Icc_self ht))
  have hEq : (∫ p in Metric.ball (0 : Space n) r ×ˢ Ioo a b, max (q p) 0)=
      ∫ t in Ioo a b, ∫ x in Metric.ball (0 : Space n) r, max (q (x,t)) 0 := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod] using hFubini
  rw [setIntegral_const,smul_eq_mul,Real.volume_real_Ioo_of_le hab] at hBound
  exact ⟨hi,hEq.le.trans (by simpa only [mul_comm] using hBound)⟩

end Yau.LeafProofs.L05AutonomousAux
