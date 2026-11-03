import Yau.Proofs.P08CanonicalRegularization
import Yau.Proofs.P08RegularizedLog
import Yau.Proofs.P08HeatAbsoluteAverage
import Yau.Proofs.P08HeatBallTransfer
import Yau.Proofs.P08LogFatou

/-! Uniform regularized canonical-logarithm averages and the original
absolute logarithmic average, with the constant fixed before the volume. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L18Aux L19Aux HeatMeasure
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- All constants are chosen from the fixed section and its original growth
witness before the Riemannian volume, epsilon, or ball radius. -/
theorem canonical_regularized_averages (X : KahlerManifold n) (o : Pt X)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S) (ho : S o ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ x, Real.log (canonicalNormSq X.metric.form S x) ≤
      C * (1 + distFrom X.metric.form o x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ, IsRiemannianVolume X.metric.form μ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ L : ℝ, 1 ≤ L →
        BallIntegralLE X.metric.form μ o
          (fun x => |Real.log (canonicalNormSq X.metric.form S x + ε)|) L (C * L) := by
  obtain ⟨A, hA, hAgrowth⟩ := canonical_regularized_log_growth X.metric S o hgrowth
  let w₀ := Real.log (canonicalNormSq X.metric.form S o)
  let K : ℝ := 2 * A * (2 * n + 2) + |w₀| + 1
  let C : ℝ := ballHeatConstant n * K
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := mul_pos (ballHeatConstant_pos n) hK
  have hn := manifold_dimension_pos X.manifold
  have hRic := P06Aux.kahlerManifold_ricci_posSemidef X
  have hqo : 0 < canonicalNormSq X.metric.form S o :=
    lt_of_le_of_ne (Yau.Proofs.P04Aux.canonicalNormSq_nonneg _ _ _)
      (Ne.symm ((Yau.Proofs.P04Aux.canonicalNormSq_eq_zero_iff _ _ _).not.mpr ho))
  refine ⟨C, hC, ?_⟩
  intro μ hμ ε hε hε1 L hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let w : Pt X → ℝ := fun x => Real.log (canonicalNormSq X.metric.form S x + ε)
  have hw : SmoothFn w := canonical_regularized_log_smooth X.metric S hS hε
  have hb (x : Pt X) : Real.log ε ≤ w x :=
    log_add_regularization_lower (Yau.Proofs.P04Aux.canonicalNormSq_nonneg _ _ _) hε
  have hΔ (x : Pt X) : 0 ≤ laplacian X.metric.form w x :=
    (canonical_regularized_laplacian_lower X S hS hε x).1.trans
      (canonical_regularized_laplacian_lower X S hS hε x).2
  have hbase : w₀ ≤ w o := log_add_regularization_basepoint hqo hε
  obtain ⟨hi, hheat⟩ := linear_subharmonic_abs_heat_average hn X.metric X.complete_metric X.kahler_metric hRic
    μ hμ o hw hΔ hb hA.le (hAgrowth ε hε hε1) hbase hL
  have hball := continuous_ball_integral_abs_le_heat hn X.metric X.complete_metric X.kahler_metric hRic μ hμ o
    hLpos (continuous_of_smoothFn hw) hi
  have hreal : (∫ x in distBall X.metric.form o L, |w x| ∂μ) ≤
      (C * L) * (μ (distBall X.metric.form o L)).toReal := by
    calc
      _ ≤ ballHeatConstant n * (μ (distBall X.metric.form o L)).toReal * (K * L) :=
        hball.trans (mul_le_mul_of_nonneg_left hheat
          (mul_nonneg (ballHeatConstant_pos n).le ENNReal.toReal_nonneg))
      _ = _ := by dsimp only [C]; ring
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite X.metric μ hμ
  have hwi : IntegrableOn w (distBall X.metric.form o L) μ := smoothFn_integrableOn_distBall X.metric μ hμ hw o hLpos
  have hvol := riemannianVolume_distBall_lt_top X.metric μ hμ o hLpos
  have hmass : ENNReal.ofReal (C * L) * μ (distBall X.metric.form o L) =
      ENNReal.ofReal ((C * L) * (μ (distBall X.metric.form o L)).toReal) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hC.le hLpos.le), ENNReal.ofReal_toReal hvol.ne]
  change (∫⁻ x in distBall X.metric.form o L, ENNReal.ofReal |w x| ∂μ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hwi.abs (ae_of_all _ (fun x => abs_nonneg (w x))), hmass]
  exact ENNReal.ofReal_le_ofReal hreal

/-- This is precisely the first frozen clause of `CanonicalAverages` for
an arbitrary qualifying canonical section. -/
theorem canonical_log_average (X : KahlerManifold n) (o : Pt X)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S) (ho : S o ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ x, Real.log (canonicalNormSq X.metric.form S x) ≤
      C * (1 + distFrom X.metric.form o x)) :
    ∃ C : ℝ, ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ L : ℝ, 1 ≤ L →
      BallIntegralLE X.metric.form μ o
        (fun x => |Real.log (canonicalNormSq X.metric.form S x)|) L (C * L) := by
  obtain ⟨C, _, hC⟩ := canonical_regularized_averages X o S hS ho hgrowth
  refine ⟨C, ?_⟩
  intro μ hμ L hL
  exact canonical_log_ball_of_regularized X.metric S hS μ o L (C * L)
    (fun ε hε hε1 => hC μ hμ ε hε hε1 L hL)

end Yau.NodeProofs.P08Aux
