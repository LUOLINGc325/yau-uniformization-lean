import Yau.Proofs.C03MetricLowerBound
import Yau.Proofs.C03CompactMinimizers

/-! A canonical, smooth source metric extension has compact distance balls.
Its inner-ball values are the actual pullback of the given chart. -/

noncomputable section
open Set
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def chartExtendedField (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) :
    HermitianField (ComplexEuclideanManifold n hn) :=
  cutoffPullbackField hn X Φ r hΦ (chartCutoff n r hr)
    (fun _ => ⟨ContDiffBump.nonneg _, ContDiffBump.le_one _⟩)

theorem chartExtendedField_metricSmooth (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) :
    MetricSmooth (chartExtendedField hn X Φ r hr hΦ) :=
  cutoffPullbackField_metricSmooth hn X Φ r hΦ _ _
    (chartCutoff n r hr).contDiff (chartCutoff_tsupport_subset r hr)

theorem chartExtendedField_inner (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r)
    (z : ComplexVector n)
    (hz : z ∈ Metric.closedBall (0 : ComplexVector n) (3 * r / 4)) :
    (chartExtendedField hn X Φ r hr hΦ z).toFun =
      (localPullbackProduct hn X Φ r hΦ z (by
        have H : dist z (0 : ComplexVector n) ≤ 3 * r / 4 := hz
        change dist z (0 : ComplexVector n) < r
        linarith)).toFun := by
  have hzr : z ∈ Metric.ball (0 : ComplexVector n) r := by
    have H : dist z (0 : ComplexVector n) ≤ 3 * r / 4 := hz
    change dist z (0 : ComplexVector n) < r
    linarith
  funext u v
  exact cutoffPullbackField_eq_pullback_of_one hn X Φ r hΦ _ _ z hzr
    ((chartCutoff n r hr).one_of_mem_closedBall hz) u v

theorem chartExtendedField_lower (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (z : ComplexVector n) :
    HermLE (((min c 1 : ℝ) : ℂ) • (1 : Herm n))
      (gMat (chartExtendedField hn X Φ r hr hΦ) z) :=
  cutoffPullbackField_global_lower_bound hn X Φ r c hΦ _ _
    (chartCutoff_tsupport_subset r hr) hlo z

theorem chartExtendedField_compact_sublevels (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (o : ComplexVector n) (R : ℝ) :
    IsCompact {y : ComplexVector n |
      inducedDistance (chartExtendedField hn X Φ r hr hΦ) o y ≤ R} :=
  field_distance_sublevel_isCompact hn _
    (chartExtendedField_metricSmooth hn X Φ r hr hΦ) (min c 1)
    (lt_min hc zero_lt_one) (chartExtendedField_lower hn X Φ r c hr hΦ hlo) o R

theorem fieldMetric_proper_of_compact_sublevels {M : ComplexManifold n}
    (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R}) :
    letI := metricSpaceOfField h hh
    ProperSpace M.Carrier := by
  letI := metricSpaceOfField h hh
  constructor
  intro x R
  convert hcompact x R using 1
  ext y
  change inducedDistance h y x ≤ R ↔ inducedDistance h x y ≤ R
  rw [inducedDistance_symm h hh y x]

end Yau.Proofs.C03Aux
