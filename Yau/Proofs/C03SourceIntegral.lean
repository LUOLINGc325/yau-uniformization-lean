import Yau.Proofs.C03SourceIntegralZero
import Yau.Proofs.C03FlatComplete

/-! Actual half-flat source norms and volume give the original integral cap. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Topology Manifold ENNReal Classical
namespace Yau.Proofs.C03Aux.SourceIntegral
open Yau Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem half_flat_inverse_zero (hn : 1 ≤ n) (φ : ComplexVector n → ℝ)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (x : ComplexVector n)
    (hN : WeightedNakanoNonnegative (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) flatMetric φ)
    (hzero : ∀ i : Fin n, ∀ α : Fin 1, coefficients (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) f x
      (chartPt (M := ComplexEuclideanManifold n hn) x x) (fun _ => i) α = 0) :
    inverseCurvatureNormSq (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x = 0 :=
  inverse_zero_of_centered_coefficients (M := ComplexEuclideanManifold n hn)
    (FlatComplete.euclideanCompleteMetric n hn).form φ f x hN hzero

theorem inverseCurvatureIntegral_le_ball (hn : 1 ≤ n) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (φ : ComplexVector n → ℝ)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (hpoint : ∀ x : ComplexVector n,
      inverseCurvatureNormSq (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
        (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x *
          ENNReal.ofReal (Real.exp (-φ x)) ≤
            if x ∈ closedBall (0 : ComplexVector n) R then ENNReal.ofReal C else 0) :
    inverseCurvatureIntegral (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) φ f ≤
      ENNReal.ofReal (C * (volume : Measure (ComplexVector n)).real (closedBall 0 R)) := by
  let s : Set (ComplexEuclideanManifold n hn).Carrier :=
    {x | (x : ComplexVector n) ∈ closedBall (0 : ComplexVector n) R}
  have hid : Continuous (X := (ComplexEuclideanManifold n hn).Carrier)
      (Y := ComplexVector n) (fun x => (x : ComplexVector n)) := continuous_id
  have hsB : @MeasurableSet (ComplexVector n) (borel (ComplexVector n))
      (closedBall (0 : ComplexVector n) R) := by
    have hborel : (inferInstance : MeasurableSpace (ComplexVector n)) =
        borel (ComplexVector n) := BorelSpace.measurable_eq
    rw [← hborel]
    exact measurableSet_closedBall
  have hs : @MeasurableSet (ComplexEuclideanManifold n hn).Carrier
      (borel (ComplexEuclideanManifold n hn).Carrier) s :=
    hsB.preimage hid.borel_measurable
  have hvol : FlatComplete.euclideanVolume n hn s =
      (volume : Measure (ComplexVector n)) (closedBall 0 R) :=
    FlatComplete.euclideanVolume_apply n hn s hs
  have hfinite : (volume : Measure (ComplexVector n)) (closedBall 0 R) ≠ ⊤ :=
    (isCompact_closedBall (0 : ComplexVector n) R).measure_lt_top.ne
  unfold inverseCurvatureIntegral
  calc
    _ ≤ ∫⁻ x, s.indicator (fun _ => ENNReal.ofReal C) x
        ∂(FlatComplete.euclideanVolume n hn) := by
      apply lintegral_mono
      intro x
      simpa only [Set.indicator_apply, s, Set.mem_setOf_eq] using hpoint x
    _ = ENNReal.ofReal C * FlatComplete.euclideanVolume n hn s := by
      rw [lintegral_indicator hs, setLIntegral_const]
    _ = ENNReal.ofReal C * (volume : Measure (ComplexVector n)) (closedBall 0 R) := by rw [hvol]
    _ = _ := by
      rw [ENNReal.ofReal_mul hC, measureReal_def, ENNReal.ofReal_toReal hfinite]

end Yau.Proofs.C03Aux.SourceIntegral
