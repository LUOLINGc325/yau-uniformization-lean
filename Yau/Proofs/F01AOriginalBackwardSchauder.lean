import Yau.Proofs.F01ACompactInitialCoefficients
import Yau.Proofs.F01ALocalInitialPotential
import Yau.Proofs.F01AffinePotentialSlice
import Yau.Proofs.F01LogDetInteriorSchauder
import Yau.Proofs.F01BackwardSchauderRestriction
import Yau.Proofs.F01MetricComparisonScalarBounds
import Yau.Proofs.F01ShiftedRealBackground

/-! The actual backward Chu estimate in a fixed original chart.  Only
the local metric range and scalar clock are inputs; the real Hessian
estimate is the conclusion of the original transformed-matrix theorem. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
attribute [local instance] backgroundRealSymNormedSpace backgroundRealSymContinuousSMul
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem fixed_original_chart_backward_schauder
    (hn : 0 < n) (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r α β ell upper Mclock Tcap ρ : ℝ} (hball : closedBall 0 r ⊆ e.source)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hell : 0 < ell) (hUpper : ell ≤ upper) (hM : 0 ≤ Mclock)
    (hTcap : 0 ≤ Tcap) (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρ1 : ρ ≤ 1) :
    ∃ Ci : ℝ, 0 < Ci ∧ ∀ (F : Point n → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T) →
      (∀ x ∈ ball 0 r, F (x,0) = 0) →
      (∀ x ∈ ball 0 r, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => F (x,s))
        (localNativePotentialClock (pullbackMatrix g e) F (x,t)) (Icc 0 T) t) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T, |localNativePotentialClock (pullbackMatrix g e) F p| ≤ Mclock) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T,
        (localNativePotentialMatrix (pullbackMatrix g e) F p - (ell : ℂ) • 1).PosSemidef ∧
        ((upper : ℂ) • 1 - localNativePotentialMatrix (pullbackMatrix g e) F p).PosSemidef) →
      SchauderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 8)) 0)
        (affineParabolicPotential ρ 0 τ F) Ci := by
  let G : Space n → Matrix (Fin n) (Fin n) ℂ := pullbackMatrix g e
  obtain ⟨hG, hRic, hq⟩ := original_chart_background_smooth g hg e he hei
  obtain ⟨Ks, hKs, hScoeff⟩ := fixed_compact_backward_coefficient_budgets e.open_source hball
    (iota_comp_contDiffOn hG) (iota_comp_contDiffOn hRic) hTcap hβ1.le
  obtain ⟨Kd, hKd, hdcoeff⟩ := fixed_compact_backward_coefficient_budgets e.open_source hball
    hq hq hTcap hα1.le
  let K : ℝ := max (Ks 0) (Kd 0)
  let B : ℝ := (ρ ^ 2)⁻¹ * (Mclock * Tcap)
  have hK : 0 < K := (hKs 0).trans_le (le_max_left _ _)
  have hB : 0 ≤ B := mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (mul_nonneg hM hTcap)
  obtain ⟨Ci, hCi, hEstimate⟩ := native_logdet_backward_schauder hn hα hα1 hβ hβ1 hell hUpper hK hB
  refine ⟨Ci, hCi, ?_⟩
  intro F T τ hCap hLower hUpperTime hF hF0 hPDE hClock hRange
  let Q : Set (Point n) := cylinder (ball 0 1) (-1) 0
  let V := affineParabolicPotential ρ 0 τ F
  let S : Point n → Matrix (Fin n) (Fin n) ℂ := fun p =>
    G (ρ • p.1) - ((τ + ρ ^ 2 * p.2 : ℝ) : ℂ) • backgroundRicci G (ρ • p.1)
  let d : Space n → ℝ := fun z => -Real.log (G (ρ • z)).det.re
  have hτ0 : 0 ≤ τ := (sq_nonneg ρ).trans hLower
  have hτ : |τ| ≤ Tcap := by rw [abs_of_nonneg hτ0]; exact hUpperTime.trans hCap
  have hSlope : |-(ρ ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg ρ)]
    nlinarith
  have hSpace {z : Space n} (hz : z ∈ ball 0 1) : ρ • z ∈ ball 0 r :=
    spatialDilation_mem_ball hρ hρr hz
  have hTime : MapsTo (fun t : ℝ => τ + ρ ^ 2 * t) (Icc (-1) 0) (Icc 0 T) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, sq_nonneg ρ]
  have hMap {p : Point n} (hp : p ∈ Q) : affineParabolicPoint ρ 0 τ p ∈ ball 0 r ×ˢ Icc 0 T := by
    exact ⟨by simpa only [affineParabolicPoint, add_zero] using hSpace hp.1, hTime hp.2⟩
  have hVsmooth : ContDiffOn ℝ ∞ V Q := by
    change ContDiffOn ℝ ∞ (fun p => (ρ ^ 2)⁻¹ * F (affineParabolicPoint ρ 0 τ p)) Q
    exact contDiffOn_const.mul (hF.comp (by unfold affineParabolicPoint; fun_prop) (fun p hp => hMap hp))
  have hC2 : C2 Q V := closed_slab_parabolic_C2 isOpen_ball
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hVsmooth
  have hMatrix (p : Point n) (hp : p ∈ Q) :
      chartPotentialMatrix S V p = localNativePotentialMatrix G F (affineParabolicPoint ρ 0 τ p) := by
    have hj := (closed_slab_slice_jets hF isOpen_ball (hMap hp).1 (hMap hp).2).1
    unfold chartPotentialMatrix
    rw [leviC_affineParabolicPotential_slice hρ.ne' hj]
    simp only [S, localNativePotentialMatrix, affineParabolicPoint, add_zero]
  have hPos (p : Point n) (hp : p ∈ Q) : (chartPotentialMatrix S V p).PosDef := by
    rw [hMatrix p hp]
    have hh := (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)).add_posSemidef
      (hRange _ (hMap hp)).1
    simpa only [add_sub_cancel] using hh
  have hS : HolderBound β Q (fun p => iota (S p)) K := by
    have hh : HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iota (G (ρ • p.1)) + (-τ + -(ρ ^ 2) * p.2) •
          iota (backgroundRicci G (ρ • p.1))) (Ks 0) :=
      holderBound_from_zero_spatial_jet (n := n) (F := Sym n)
        (f := fun p => iota (G (ρ • p.1)) + (-τ + -(ρ ^ 2) * p.2) •
          iota (backgroundRicci G (ρ • p.1)))
        (hScoeff 0 ρ (-τ) (-(ρ ^ 2)) hρ hρr hρ1
          (by simpa only [abs_neg] using hτ) hSlope)
    have hSub : Q ⊆ cylinder (ball (0 : Space n) 1) (-1) 1 :=
      fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans zero_le_one⟩
    apply holderBound_mono_const (C := Ks 0) (D := K) ?_ (le_max_left _ _)
    apply holderBound_congr_on_native (holderBound_restrict hh hSub)
    intro p hp
    simp only [S, iota_sub, iota_real_smul]
    rw [show -τ + -(ρ ^ 2) * p.2 = -(τ + ρ ^ 2 * p.2) by ring, neg_smul]
    rfl
  have hd : HolderBound α Q (fun p => d p.1) K := by
    have hRaw : HolderBound α (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ 0 (fun z => Real.log (G (ρ • z)).det.re) p.1) (Kd 0) := by
      simpa only [zero_mul, zero_add, zero_smul, add_zero] using
        hdcoeff 0 ρ 0 0 hρ hρr hρ1 (by simpa only [abs_zero] using hTcap) (by norm_num)
    have hh : HolderBound α (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => Real.log (G (ρ • p.1)).det.re) (Kd 0) :=
      holderBound_from_zero_spatial_jet (n := n) (F := ℝ)
        (f := fun p => Real.log (G (ρ • p.1)).det.re) hRaw
    have hSub : Q ⊆ cylinder (ball (0 : Space n) 1) (-1) 1 :=
      fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans zero_le_one⟩
    apply holderBound_mono_const (C := Kd 0) (D := K) ?_ (le_max_right _ _)
    simpa only [d, zero_smul, smul_zero, add_zero, mul_zero, zero_add] using
      holderBound_neg (holderBound_restrict hh hSub)
  have hSup (p : Point n) (hp : p ∈ Q) : |V p| ≤ B := by
    have hu := closed_potential_abs_bound_of_time_value
      (hτ0.trans hUpperTime) (hF0 _ (hMap hp).1)
      (hPDE _ (hMap hp).1) (fun t ht => hClock (_,t) ⟨(hMap hp).1,ht⟩)
      _ (hMap hp).2
    have hub : |F (affineParabolicPoint ρ 0 τ p)| ≤ Mclock * Tcap :=
      hu.trans (mul_le_mul_of_nonneg_left ((hMap hp).2.2.trans hCap) hM)
    dsimp only [V, affineParabolicPotential, affineParabolicPullback, B]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ρ))]
    exact mul_le_mul_of_nonneg_left hub (inv_nonneg.mpr (sq_nonneg ρ))
  have hTransformed (p : Point n) (hp : p ∈ Q) :
      (((iota (S p) + complexHessianMap (hessian V p) : Sym n) : Mat n) - ell • 1).PosSemidef ∧
      (upper • 1 - ((iota (S p) + complexHessianMap (hessian V p) : Sym n) : Mat n)).PosSemidef := by
    rw [real_chart_potential_matrix hC2 hp, hMatrix p hp]
    exact iota_scalar_matrix_sandwich (hRange _ (hMap hp)).1 (hRange _ (hMap hp)).2
  have hEquation (p : Point n) (hp : p ∈ Q) :
      timeD Q V p - logDetReal (iota (S p) + complexHessianMap (hessian V p)) = d p.1 := by
    have hj := affine_potential_clock_jet hρ.ne' hp.2 hTime
      (fun s hs => hPDE (ρ • p.1 + 0) (by simpa only [add_zero] using hSpace hp.1) s hs)
    have hSet : {s : ℝ | (p.1,s) ∈ Q} = Icc (-1) 0 := by
      ext s
      exact and_iff_right hp.1
    have ht : timeD Q V p = localNativePotentialClock G F (affineParabolicPoint ρ 0 τ p) := by
      simpa only [timeD, hSet] using
        hj.derivWithin (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) p.2 hp.2)
    rw [ht, real_chart_potential_matrix hC2 hp, logDetReal_iota_posDef _ (hPos p hp), hMatrix p hp]
    simp only [localNativePotentialClock, affineParabolicPoint, add_zero, d]
    ring
  have hSub : backward (n := n) 1 ⊆ Q := by
    intro p hp
    exact ⟨hp.1, by simpa only [one_pow] using hp.2.1.le, hp.2.2⟩
  have huOpen : C2 (backward 1) V := by
    simpa only [backward, one_pow] using c2_closed_open_lower hC2
  have hEqOpen : ∀ p ∈ backward 1, timeD (backward 1) V p -
      logDetReal (iota (S p) + complexHessianMap (hessian V p)) = d p.1 := by
    intro p hp
    have hp' : p ∈ ball (0 : Space n) 1 ×ˢ Ioc (-1) 0 := by
      simpa only [backward, one_pow] using hp
    have ht := timeD_closed_open_lower V hp'
    have hh := hEquation p (hSub hp)
    change timeD (cylinder (ball 0 1) (-1) 0) V p -
      logDetReal (iota (S p) + complexHessianMap (hessian V p)) = d p.1 at hh
    rw [ht] at hh
    simpa only [backward, one_pow] using hh
  have hSch := hEstimate (fun p => iota (S p)) (fun p => d p.1) V
    (holderBound_restrict hS hSub) (holderBound_restrict hd hSub) huOpen
    (fun p hp => hSup p (hSub hp)) (fun p hp => hTransformed p (hSub hp)) hEqOpen
  apply backward_schauder_closed_restrict hC2 hSch Subset.rfl
    (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
  · intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  · intro t ht
    exact ⟨by nlinarith [ht.1], ht.2⟩
  · norm_num

end Yau.NodeProofs.F01Aux
