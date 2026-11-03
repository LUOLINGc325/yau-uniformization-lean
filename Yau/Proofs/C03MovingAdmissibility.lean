import Yau.Proofs.C03EnergyCorrection
import Yau.Proofs.C03MovingEnergyDistance
import Yau.Proofs.C03MovingEnergyTrace
import Yau.Proofs.C03CorrectionVector
import Yau.Proofs.C03HessianCorrection
import Yau.Proofs.C03ScalarHessianTest
import Yau.Proofs.C03SourceSpeed

/-! A negative actual energy trace is corrected into a negative scalar
Hessian. The resulting explicit holomorphic endpoints are admissible on
one whole complex neighborhood, independently of the cut locus. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ}

theorem exists_moving_trial_admissible (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, actualSpeedSq k γ t = ρ ^ 2)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv γ)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (deriv γ t)) t)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℂ, HasDerivAt (fun s => a • W s)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (a • W t)) t)
    (htrace :
      fderiv ℝ (fderiv ℝ (sourceEnergy hn k (movingJoint γ W 0))) 0 1 1 +
        fderiv ℝ (fderiv ℝ (sourceEnergy hn k (movingJoint γ W 0))) 0 Complex.I Complex.I < 0) :
    ∃ Q : ComplexVector n, ∀ᶠ a : ℂ in 𝓝 0,
      inducedDistance k (γ 0 + a • W 0)
        (γ 1 + a • W 1 + ((1 / 2 : ℂ) * a ^ 2) • Q) ≤ ρ := by
  let F (q : ComplexVector n) := sourceEnergy hn k (movingJoint γ W q)
  have hF (q : ComplexVector n) : ContDiff ℝ 2 (F q) := by
    apply contDiffOn_univ.mp
    exact sourceEnergy_contDiffOn hn k hk _ univ univ isOpen_univ isOpen_univ (subset_univ _)
      (movingJoint_contDiffOn γ W q univ hγ.contDiffOn hW.contDiffOn)
  let H := fderiv ℝ (fderiv ℝ (F 0)) 0
  let u := (H Complex.I Complex.I - H 1 1) / 4
  let v := -H 1 Complex.I / 2
  let Q := energyCorrectionVector (deriv γ 1) (ρ ^ 2) u v
  let K := fderiv ℝ (fderiv ℝ (F Q)) 0
  let S : ℂ →L[ℂ] ComplexVector n := (ContinuousLinearMap.id ℂ ℂ).smulRight Q
  let L : ℂ →L[ℝ] ℝ :=
    (realMetricInChart k (0 : ComplexVector n) (γ 1) (deriv γ 1)).comp (S.restrictScalars ℝ)
  have hL (a : ℂ) : L a = realMetricInChart k (0 : ComplexVector n) (γ 1) (deriv γ 1)
      (a • Q) := rfl
  have hT : realMetricInChart k (0 : ComplexVector n) (γ 1) (deriv γ 1) (deriv γ 1) = ρ ^ 2 := by
    rw [← actualSpeedSq_source_chart hn k γ 1 (hγ.contDiffAt.of_le (by norm_num))]
    exact hspeed 1 ⟨zero_le_one, le_rfl⟩
  have hpair := energyCorrectionVector_pairings k (0 : ComplexVector n) (γ 1) (deriv γ 1)
    (by rw [euclidean_chartTarget hn]; trivial) (ρ ^ 2) (pow_ne_zero 2 hρ.ne') hT u v
  have hL1 : L 1 = (H Complex.I Complex.I - H 1 1) / 4 := by
    rw [hL]
    simpa only [one_smul] using hpair.1
  have hLI : L Complex.I = -H 1 Complex.I / 2 := by
    rw [hL]
    exact hpair.2
  have hdir (q : ComplexVector n) (a : ℂ) :
      mapDirection (mapDirection (F q) a) a 0 = fderiv ℝ (fderiv ℝ (F q)) 0 a a := by
    have HD := (mapDirection_hasFDerivAt (F q) (p := (0 : ℂ)) (hF q).contDiffAt a).fderiv
    have HH := congrArg (fun A : ℂ →L[ℝ] ℝ => A a) HD
    exact HH
  have hdiag (a : ℂ) : K a a - H a a = 2 * L (a ^ 2) := by
    have HE := movingEnergy_second_correction hn k hk γ W Q hγ hW a hgeo
      (fun t ht => hparallel t ht a)
    change mapDirection (mapDirection (F Q) a) a 0 - mapDirection (mapDirection (F 0) a) a 0 = _ at HE
    rw [hdir Q a, hdir 0 a] at HE
    exact HE
  have hK := complex_hessian_correction_scalar H K L
    ((hF 0).contDiffAt.isSymmSndFDerivAt (by norm_num))
    ((hF Q).contDiffAt.isSymmSndFDerivAt (by norm_num)) hdiag hL1 hLI
  let c := (H 1 1 + H Complex.I Complex.I) / 4
  have hc : c < 0 := by
    change H 1 1 + H Complex.I Complex.I < 0 at htrace
    change (H 1 1 + H Complex.I Complex.I) / 4 < 0
    linarith
  have hcoeff : (H 1 1 + H Complex.I Complex.I) / 2 = 2 * c := by dsimp only [c]; ring
  rw [hcoeff] at hK
  have hfirst : fderiv ℝ (F Q) 0 = 0 := movingEnergy_fderiv_zero hn k hk γ W Q hγ hW hparallel
  have hnear := eventually_lt_of_scalar_negative_hessian (F Q) c hc
    (hF Q).contDiffAt hfirst hK
  have hzero : F Q 0 = ρ ^ 2 := movingEnergy_zero hn k γ W Q hγ hW (ρ ^ 2) hspeed
  refine ⟨Q, ?_⟩
  filter_upwards [hnear] with a ha
  have hbound := movingEnergy_bounds_distance hn k hk γ W Q hγ hW a
  by_cases h0 : a = 0
  · subst a
    change _ ≤ F Q 0 at hbound
    rw [hzero] at hbound
    nlinarith [sq_nonneg (inducedDistance k (γ 0 + (0 : ℂ) • W 0)
      (γ 1 + (0 : ℂ) • W 1 + ((1 / 2 : ℂ) * (0 : ℂ) ^ 2) • Q) - ρ)]
  · have hE : F Q a < ρ ^ 2 := by rw [← hzero]; exact ha h0
    exact (distance_lt_radius_of_energy_lt hρ hbound hE).le

end Yau.Proofs.C03Aux
