import Yau.Proofs.C03GeodesicConfinement
import Yau.Proofs.C03CurveNeighborhood
import Yau.Proofs.C03ParallelVector
import Yau.Proofs.C03CurveExtension
import Yau.Proofs.C03CurveGerms

/-! Short intrinsic balls supply actual global C³ path/vector data, with
all original speed, geodesic and parallel equations retained on [0,1]. -/

noncomputable section
open Filter Set
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_short_source_parallel_data (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    (r ρ : ℝ) (hsmall : Real.sqrt (d⁻¹) * ρ < r / 4)
    (hI : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ u v,
      chartChristoffelBilin k (0 : ComplexVector n) z u (Complex.I • v) =
        Complex.I • chartChristoffelBilin k (0 : ComplexVector n) z u v)
    (z y V : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hzy : inducedDistance k z y ≤ ρ) :
    ∃ γ W : ℝ → ComplexVector n, ContDiff ℝ 3 γ ∧ ContDiff ℝ 3 W ∧
      γ 0 = z ∧ γ 1 = y ∧ W 0 = V ∧
      MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball (0 : ComplexVector n) (3 * r / 4)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, actualSpeedSq k γ t = inducedDistance k z y ^ 2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv γ)
        (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (deriv γ t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℂ, HasDerivAt (fun s => a • W s)
        (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (a • W t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, realMetricInChart k (0 : ComplexVector n) (γ t) (W t) (W t) =
        realMetricInChart k (0 : ComplexVector n) z V V := by
  letI := manifold_realSmooth (ComplexEuclideanManifold n hn)
  have hcompact (p : (ComplexEuclideanManifold n hn).Carrier) (R : ℝ) :
      IsCompact {x | inducedDistance k p x ≤ R} :=
    field_distance_sublevel_isCompact hn k hk d hd hlo p R
  obtain ⟨δ, hδ, β, hβ0, hβ1, hβgeo, hβspeed⟩ :=
    minimizing_geodesic_of_compact_sublevels k hk hcompact z y
  let βv : ℝ → ComplexVector n := β
  have hsrc : MapsTo βv (Ioo (-δ) (1 + δ))
      (chartAt (ComplexVector n) (0 : ComplexVector n)).source := by
    rw [euclidean_chartSource hn]
    exact mapsTo_univ _ _
  have hβC : ContDiffOn ℝ 3 βv (Ioo (-δ) (1 + δ)) := by
    have H := curve_coordinates_contDiffOn_three β (0 : ComplexVector n)
      (Ioo (-δ) (1 + δ)) isOpen_Ioo hβgeo.1 hsrc
    simpa only [euclidean_chartPt] using H
  have hinner : MapsTo βv (Icc (0 : ℝ) 1) (Metric.ball (0 : ComplexVector n) (3 * r / 4)) :=
    short_source_geodesic_in_inner_ball hn k hk d hd hlo r ρ hsmall z y hz hzy
      δ hδ βv hβ0 hβgeo hβspeed
  obtain ⟨η, hη, hηsub, hηimage⟩ := exists_curve_interval_neighborhood βv δ hδ
    hβC.continuousOn _ Metric.isOpen_ball hinner
  have hunitη : Icc (0 : ℝ) 1 ⊆ Ioo (-η) (1 + η) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨ε, hε, P, hP0, hPC, hεsub, hPpar, hPnorm⟩ :=
    exists_source_parallel_vector hn k hk βv _ isOpen_Ioo (hβC.mono hηsub) hunitη
      (fun t ht v => hI (βv t) (hηimage ht) (deriv βv t) v) V
  have hβCε := hβC.mono (hεsub.trans hηsub)
  obtain ⟨γ, W, hγ, hW, heq⟩ := exists_global_curve_pair_extension βv P ε hε hβCε hPC
  have hunitε : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hg0 : γ 0 = z := ((heq 0 (by norm_num)).1.self_of_nhds).trans hβ0
  have hg1 : γ 1 = y := ((heq 1 (by norm_num)).1.self_of_nhds).trans hβ1
  refine ⟨γ, W, hγ, hW, hg0, hg1,
    ((heq 0 (by norm_num)).2.self_of_nhds).trans hP0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [(heq t ht).1.self_of_nhds]
    exact hinner ht
  · intro t ht
    rw [source_speed_congr_germ hn k γ βv t (hγ.contDiffAt.of_le (by norm_num))
      ((hβCε.contDiffAt (isOpen_Ioo.mem_nhds (hunitε ht))).of_le (by norm_num)) (heq t ht).1]
    exact hβspeed t ht
  · intro t ht
    apply source_geodesic_equation_congr_germ _ γ βv t (heq t ht).1
    exact source_geodesic_velocity_equation hn k βv (Ioo (-δ) (1 + δ)) hβgeo t
      (hηsub (hεsub (hunitε ht)))
  · intro t ht a
    exact source_parallel_equation_congr_germs _ γ βv W P t a (heq t ht).1 (heq t ht).2
      (hPpar t (hunitε ht) a)
  · intro t ht
    rw [(heq t ht).1.self_of_nhds, (heq t ht).2.self_of_nhds]
    have H := hPnorm t (hunitε ht)
    have hβv0 : βv 0 = z := hβ0
    rwa [hβv0] at H

end Yau.Proofs.C03Aux
