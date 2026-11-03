import Yau.Proofs.C03MovingJets
import Yau.Proofs.C03CovariantCancellation

/-! Two moving endpoints use unscaled parallel first variations. Their
covariant time derivatives vanish, unlike fixed-start radial variations. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mapDirection_time (Z : ℂ × ℝ → E) {a : ℂ} {t : ℝ}
    (hZ : DifferentiableAt ℝ Z (a, t)) :
    mapDirection Z (0, 1) (a, t) = deriv (fun s => Z (a, s)) t := by
  have H := hZ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t a).prodMk (hasDerivAt_id t))
  exact H.deriv.symm

theorem mapCovariantD_unscaled_parallelVariation
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (Z : ℂ × ℝ → E) {t : ℝ}
    (hZ : ContDiffAt ℝ 2 Z (0, t)) (P : ℝ → E) (a : ℂ)
    (hP : HasDerivAt P (-Γ (Z (0, t)) (mapDirection Z (0, 1) (0, t)) (P t)) t)
    (hJ : (fun s => mapDirection Z (a, 0) (0, s)) =ᶠ[𝓝 t] P) :
    mapCovariantD Γ Z (0, 1) (mapDirection Z (a, 0)) (0, t) = 0 := by
  have hD : DifferentiableAt ℝ (mapDirection Z (a, 0)) (0, t) :=
    ((hZ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt_one
  unfold mapCovariantD
  have hv : mapDirection Z (a, 0) (0, t) = P t := hJ.self_of_nhds
  rw [mapDirection_time _ hD, hJ.deriv_eq, hP.deriv, hv]
  exact neg_add_cancel _

theorem map_radial_pair_zero_of_connection_I {n : ℕ}
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ℂ × ℝ → ComplexVector n) (p : ℂ × ℝ)
    (hI : ∀ v, Γ (Z p) (Complex.I • v) (Complex.I • v) = -Γ (Z p) v v)
    (hfirst : mapDirection Z (Complex.I, 0) p = Complex.I • mapDirection Z (1, 0) p)
    (hsecond : mapDirection (mapDirection Z (1, 0)) (1, 0) p +
      mapDirection (mapDirection Z (Complex.I, 0)) (Complex.I, 0) p = 0) :
    mapCovariantD Γ Z (1, 0) (mapDirection Z (1, 0)) p +
      mapCovariantD Γ Z (Complex.I, 0) (mapDirection Z (Complex.I, 0)) p = 0 := by
  unfold mapCovariantD
  rw [hfirst, hI]
  convert hsecond using 1 <;> abel

theorem covariant_radial_pair_time_zero {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (Z : ℂ × ℝ → ComplexVector n) {p : ℂ × ℝ}
    (hz : Z p ∈ chartTarget c) (hZ : ContDiffAt ℝ 3 Z p)
    (hsum : (fun q =>
      mapCovariantD (chartChristoffelBilin h c) Z (1, 0) (mapDirection Z (1, 0)) q +
        mapCovariantD (chartChristoffelBilin h c) Z (Complex.I, 0)
          (mapDirection Z (Complex.I, 0)) q) =ᶠ[𝓝 p] fun _ => 0) :
    mapCovariantD (chartChristoffelBilin h c) Z (0, 1)
        (mapCovariantD (chartChristoffelBilin h c) Z (1, 0) (mapDirection Z (1, 0))) p +
      mapCovariantD (chartChristoffelBilin h c) Z (0, 1)
        (mapCovariantD (chartChristoffelBilin h c) Z (Complex.I, 0)
          (mapDirection Z (Complex.I, 0))) p = 0 := by
  apply covariant_pair_zero_of_eventually_sum_zero _ Z _ _
    ((mapCovariantD_contDiffAt h hh c Z _ hz 1 (hZ.of_le (by norm_num))
      (mapDirection_contDiffAt Z 2 hZ (1, 0)) (1, 0)).differentiableAt_one)
    ((mapCovariantD_contDiffAt h hh c Z _ hz 1 (hZ.of_le (by norm_num))
      (mapDirection_contDiffAt Z 2 hZ (Complex.I, 0)) (Complex.I, 0)).differentiableAt_one)
    hsum (0, 1)

end Yau.Proofs.C03Aux
