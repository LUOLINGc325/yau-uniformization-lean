import Yau.Proofs.C03ShortParallelData
import Yau.Proofs.C03NonzeroVariations
import Yau.Proofs.C03NegativeEnergyTrace
import Yau.Proofs.C03MovingAdmissibility
import Yau.Proofs.C03InteriorTrial
import Yau.Proofs.C03EndpointSupport
import Yau.Proofs.C03ConstantSupport

/-! Actual short minimizing paths give planar lower supports of the
moving-ball maximum, including at boundary maximizers and the cut locus. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract L22Aux
open Yau.NodeProofs.P02Aux
open Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_ball_lower_support_nonzero (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    (r ρ : ℝ) (hρ : 0 < ρ) (hsmall : Real.sqrt (d⁻¹) * ρ < r / 4)
    (hI : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ u v,
      chartChristoffelBilin k (0 : ComplexVector n) z u (Complex.I • v) =
        Complex.I • chartChristoffelBilin k (0 : ComplexVector n) z u v)
    (hII : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ v,
      chartChristoffelBilin k (0 : ComplexVector n) z
        (Complex.I • v) (Complex.I • v) =
          -chartChristoffelBilin k (0 : ComplexVector n) z v v)
    (hcurv : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4),
      ∀ T W : ComplexVector n, T ≠ 0 → W ≠ 0 →
        0 < coordinateBisectional k (0 : ComplexVector n) z T W)
    (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ 2 ψ) (κ : ℝ)
    (z V : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hLevi : ∀ y ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4),
      inducedDistance k z y ≤ ρ → ∀ W,
        κ * ellipsoidQuadratic (gMat k y) W ≤ complexLeviQuadratic ψ y W)
    (hV : V ≠ 0) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = fieldBallMaximum k ψ ρ z ∧
      (∀ᶠ a : ℂ in 𝓝 0, s a ≤ fieldBallMaximum k ψ ρ (z + a • V)) ∧
      4 * κ * ellipsoidQuadratic (gMat k z) V ≤ planarTrace s 0 := by
  have hcompact (p : (ComplexEuclideanManifold n hn).Carrier) (R : ℝ) :
      IsCompact {x | inducedDistance k p x ≤ R} :=
    field_distance_sublevel_isCompact hn k hk d hd hlo p R
  have hmax : ∃ y : ComplexVector n, inducedDistance k z y ≤ ρ ∧
      ψ y = fieldBallMaximum k ψ ρ z := by
    obtain ⟨y, hzy, hy, _⟩ := fieldBallMaximum_spec k hk hcompact ψ hψ.continuous ρ hρ.le z
    exact ⟨y, hzy, hy⟩
  obtain ⟨y, hzy, hy⟩ := hmax
  obtain ⟨γ, W, hγ, hW, hγ0, hγ1, hW0, himage, hspeed, hgeo, hparallel, hnorm⟩ :=
    exists_short_source_parallel_data hn k hk d hd hlo r ρ hsmall hI z y V hz hzy
  have hyinner : y ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4) := by
    rw [← hγ1]
    exact himage ⟨zero_le_one, le_rfl⟩
  have hadmissible : ∃ Q : ComplexVector n, ∀ᶠ a : ℂ in 𝓝 0,
      inducedDistance k (z + a • V)
        (y + a • W 1 + ((1 / 2 : ℂ) * a ^ 2) • Q) ≤ ρ := by
    by_cases hinterior : inducedDistance k z y < ρ
    · refine ⟨0, ?_⟩
      have hmargin : inducedDistance k z y ^ 2 < ρ ^ 2 :=
        (sq_lt_sq₀ (inducedDistance_nonneg k hk z y) hρ.le).2 hinterior
      simpa only [hγ0, hγ1, hW0, smul_zero, add_zero] using
        moving_trial_admissible_of_energy_margin hn k hk γ W hγ hW
          (inducedDistance k z y) ρ hρ hmargin hspeed
    · have hboundary : inducedDistance k z y = ρ :=
        le_antisymm hzy (le_of_not_gt hinterior)
      have hspeedρ : ∀ t ∈ Icc (0 : ℝ) 1, actualSpeedSq k γ t = ρ ^ 2 := by
        intro t ht
        rw [hspeed t ht, hboundary]
      have hpositive : ∀ t ∈ Icc (0 : ℝ) 1,
          0 < coordinateBisectional k (0 : ComplexVector n) (γ t) (deriv γ t) (W t) := by
        intro t ht
        apply hcurv (γ t) (himage ht)
        · exact source_velocity_ne_zero_of_speed hn k γ t ρ hρ
            (hγ.contDiffAt.of_le (by norm_num)) (hspeedρ t ht)
        · exact source_parallel_vector_ne_zero hn k z (γ t) V (W t) hV (hnorm t ht)
      have htrace := movingEnergy_trace_negative hn k hk γ W hγ hW
        (Metric.ball (0 : ComplexVector n) (3 * r / 4)) Metric.isOpen_ball
        himage hII hparallel hpositive
      obtain ⟨Q, hQ⟩ := exists_moving_trial_admissible hn k hk γ W hγ hW ρ hρ
        hspeedρ hgeo hparallel htrace
      exact ⟨Q, by simpa only [hγ0, hγ1, hW0] using hQ⟩
  obtain ⟨Q, hQ⟩ := hadmissible
  obtain ⟨s, hsc, hs0, hsle, hstrace⟩ := exists_endpoint_lower_support hn k hk
    hcompact ψ hψ.continuous ρ hρ.le z y V (W 1) Q hψ.contDiffAt hy hQ
  have hquad : ellipsoidQuadratic (gMat k y) (W 1) =
      ellipsoidQuadratic (gMat k z) V := by
    have H := hnorm 1 ⟨zero_le_one, le_rfl⟩
    rw [hγ1, source_realMetric_quadratic hn k y (W 1),
      source_realMetric_quadratic hn k z V] at H
    linarith
  refine ⟨s, hsc, hs0, hsle, ?_⟩
  rw [hstrace]
  calc
    4 * κ * ellipsoidQuadratic (gMat k z) V =
        4 * (κ * ellipsoidQuadratic (gMat k y) (W 1)) := by rw [hquad]; ring
    _ ≤ 4 * complexLeviQuadratic ψ y (W 1) :=
      mul_le_mul_of_nonneg_left (hLevi y hyinner hzy (W 1)) (by norm_num)

theorem exists_ball_lower_support (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    (r ρ : ℝ) (hρ : 0 < ρ) (hsmall : Real.sqrt (d⁻¹) * ρ < r / 4)
    (hI : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ u v,
      chartChristoffelBilin k (0 : ComplexVector n) z u (Complex.I • v) =
        Complex.I • chartChristoffelBilin k (0 : ComplexVector n) z u v)
    (hII : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ v,
      chartChristoffelBilin k (0 : ComplexVector n) z
        (Complex.I • v) (Complex.I • v) =
          -chartChristoffelBilin k (0 : ComplexVector n) z v v)
    (hcurv : ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4),
      ∀ T W : ComplexVector n, T ≠ 0 → W ≠ 0 →
        0 < coordinateBisectional k (0 : ComplexVector n) z T W)
    (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ 2 ψ) (κ : ℝ)
    (z V : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hLevi : ∀ y ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4),
      inducedDistance k z y ≤ ρ → ∀ W,
        κ * ellipsoidQuadratic (gMat k y) W ≤ complexLeviQuadratic ψ y W) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = fieldBallMaximum k ψ ρ z ∧
      (∀ᶠ a : ℂ in 𝓝 0, s a ≤ fieldBallMaximum k ψ ρ (z + a • V)) ∧
      4 * κ * ellipsoidQuadratic (gMat k z) V ≤ planarTrace s 0 := by
  by_cases hV : V = 0
  · subst V
    exact exists_zero_direction_lower_support (fieldBallMaximum k ψ ρ) z (gMat k z) κ
  · exact exists_ball_lower_support_nonzero hn k hk d hd hlo r ρ hρ hsmall hI hII
      hcurv ψ hψ κ z V hz hLevi hV

end Yau.Proofs.C03Aux
