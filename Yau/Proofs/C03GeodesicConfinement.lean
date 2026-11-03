import Yau.Proofs.C03GlobalGeometry
import Yau.Proofs.C03GeodesicRetreat

/-! Short actual minimizing segments stay in the inner ball where the
extended source metric equals the original pullback metric. -/

noncomputable section
open Set
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem short_source_geodesic_in_inner_ball (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    (r ρ : ℝ) (hsmall : Real.sqrt (d⁻¹) * ρ < r / 4)
    (z y : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hzy : inducedDistance k z y ≤ ρ)
    (δ : ℝ) (hδ : 0 < δ) (γ : ℝ → ComplexVector n) (hγ0 : γ 0 = z)
    (hgeo : FieldGeodesicOn k γ (Ioo (-δ) (1 + δ)))
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, actualSpeedSq k γ t = inducedDistance k z y ^ 2) :
    MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball (0 : ComplexVector n) (3 * r / 4)) := by
  letI := manifold_realSmooth (ComplexEuclideanManifold n hn)
  intro u hu
  have hC : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Icc 0 u) :=
    (hgeo.1.of_le (by norm_num)).mono (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2, hu.2])
  have H := field_segment_distance_le k hk γ 0 u (inducedDistance k z y) hu.1
    (inducedDistance_nonneg k hk z y) hC (by
      intro t ht
      exact hspeed t ⟨ht.1, ht.2.trans hu.2⟩)
  rw [hγ0, sub_zero] at H
  have hnear : inducedDistance k z (γ u) ≤ ρ := by
    have huD := mul_le_mul_of_nonneg_right hu.2 (inducedDistance_nonneg k hk z y)
    have huD' : u * inducedDistance k z y ≤ inducedDistance k z y := by
      simpa only [one_mul] using huD
    exact H.trans (huD'.trans hzy)
  have HE := euclidean_dist_le_field_distance hn k hk d hd hlo z (γ u)
  have hstandard : dist (γ u) z ≤ Real.sqrt (d⁻¹) * ρ := by
    rw [dist_comm]
    exact HE.trans (mul_le_mul_of_nonneg_left hnear (Real.sqrt_nonneg _))
  change dist (γ u) 0 < 3 * r / 4
  have hz' : dist z 0 < r / 2 := hz
  linarith [dist_triangle (γ u) z 0]

end Yau.Proofs.C03Aux
