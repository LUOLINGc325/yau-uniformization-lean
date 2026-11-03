import Yau.Proofs.F01AOriginalBackwardSchauder
import Yau.Proofs.F01AOriginalInitialSchauder
import Yau.Proofs.F01ACompactSpatialJets
import Yau.Proofs.F01ACompactBackwardSpatialJets
import Yau.Proofs.F01AsymmetricSandwichConstant
import Yau.Proofs.F01InverseTensorDilation
import Yau.Proofs.F01ClosedPotentialWordEquations
import Yau.Proofs.F01ShiftedPotentialScale

/-! All spatial orders for a local potential in one fixed original chart.
The initial and terminal clock faces are kept closed, and every numerical
budget is fixed before the potential is supplied. -/
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem fixed_original_chart_initial_spatial_jets
    (hn : 0 < n) (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r α β ell upper Mclock : ℝ} (hball : closedBall 0 r ⊆ e.source)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hell : 0 < ell) (hUpper : ell ≤ upper) (hM : 0 ≤ Mclock) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ (F : Point n → ℝ) (T ρ : ℝ),
      0 < ρ → 2 * ρ ≤ r → 2 * ρ ≤ 1 → (2 * ρ) ^ 2 ≤ T →
      ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T) →
      (∀ x ∈ ball 0 r, F (x,0) = 0) →
      (∀ x ∈ ball 0 r, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => F (x,s))
        (localNativePotentialClock (pullbackMatrix g e) F (x,t)) (Icc 0 T) t) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T, |localNativePotentialClock (pullbackMatrix g e) F p| ≤ Mclock) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T,
        (localNativePotentialMatrix (pullbackMatrix g e) F p - (ell : ℂ) • 1).PosSemidef ∧
        ((upper : ℂ) • 1 - localNativePotentialMatrix (pullbackMatrix g e) F p).PosSemidef) →
      ∀ k p, p ∈ cylinder (ball 0 (1 / 2)) (-(1 / 2)) (1 / 2) →
        ‖iteratedFDeriv ℝ k (fun z =>
          forwardZeroSpaceTime (parabolicRescalePotential ρ F) (z,p.2)) p.1‖ ≤ K k := by
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  let G : Space n → Matrix (Fin n) (Fin n) ℂ := pullbackMatrix g e
  obtain ⟨hG, hRic, hq⟩ := original_chart_background_smooth g hg e he hei
  obtain ⟨Ci, hCi, hInitial⟩ := fixed_original_chart_initial_schauder hn g hg e he hei
    hball hα hα1 hβ hβ1 hell hUpper hM
  obtain ⟨D, hD, hWiden⟩ := exists_relative_sandwich_constant (ι := Fin n) (b := upper) hell
  obtain ⟨Ks, hKs, hSjets⟩ := fixed_compact_initial_coefficient_budgets e.open_source hball hG hRic hδ1.le
  obtain ⟨Kd, hKd, hDjets⟩ := fixed_compact_initial_coefficient_budgets e.open_source hball hq.neg hq.neg hδ1.le
  let B : ℕ → ℝ := fun j => max (Ks j) (Kd j)
  have hB (j : ℕ) : 0 < B j := (hKs j).trans_le (le_max_left _ _)
  obtain ⟨K, hK, hJets⟩ := compact_coordinate_spatial_jet_budgets hn hδ hδ1 hD hCi B hB
  refine ⟨K, hK, ?_⟩
  intro F T ρ hρ hρr2 hρ12 hρT2 hF hF0 hPDE hClock hRange
  have hρr : ρ ≤ r := by linarith [hρ.le]
  have hρ1 : ρ ≤ 1 := by linarith [hρ.le]
  have hρT : ρ ^ 2 ≤ T := by nlinarith [sq_nonneg ρ]
  let u := parabolicRescalePotential ρ F
  let V := forwardZeroSpaceTime u
  let S := localNormalizedComplexBackground G ρ
  let d : Space n → ℝ := fun z => -Real.log (G (ρ • z)).det.re
  let P : Point n → ℝ := fun p => localNativePotentialClock G F (parabolicDilation ρ p)
  have hMap {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
      parabolicDilation ρ (p.1,max p.2 0) ∈ ball 0 r ×ˢ Icc 0 T :=
    parabolicDilation_maps_positive hρ hρr hρT
      ⟨hp.1, le_max_right _ _, max_le hp.2.2 zero_le_one⟩
  have hMatrix (p : Point n) (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
      chartPotentialMatrix S V p = localNativePotentialMatrix G F
        (parabolicDilation ρ (p.1,max p.2 0)) :=
    normalized_local_initial_complex_matrix G F hρ hρr hρT hF hF0 hp
  have hPos (p : Point n) (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
      (chartPotentialMatrix S V p).PosDef := by
    rw [hMatrix p hp]
    have hh := (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)).add_posSemidef
      (hRange _ (hMap hp)).1
    simpa only [add_sub_cancel] using hh
  have hBounds (p : Point n) (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
      (chartPotentialMatrix S V p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((D : ℂ) • 1 - chartPotentialMatrix S V p).PosSemidef := by
    rw [hMatrix p hp]
    exact hWiden 1 _ Matrix.PosSemidef.one (hRange _ (hMap hp)).1 (hRange _ (hMap hp)).2
  have hu : ContDiffOn ℝ ∞ u (ball 0 1 ×ˢ Icc 0 1) :=
    parabolicRescalePotential_smooth hρ hρr hρT hF
  have hu0 (x : Space n) (hx : x ∈ ball 0 1) : u (x,0) = 0 := by
    simp only [u, parabolicRescalePotential, parabolicDilation, mul_zero,
      hF0 _ (spatialDilation_mem_ball hρ hρr hx)]
  have hP0 (x : Space n) (hx : x ∈ ball 0 1) : P (x,0) = 0 := by
    simpa only [P, parabolicDilation, mul_zero] using
      localNativePotentialClock_initial G F isOpen_ball hF0 (spatialDilation_mem_ball hρ hρr hx)
  have hJet (x : Space n) (hx : x ∈ ball 0 1) (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivWithinAt (fun s => u (x,s)) (P (x,t)) (Icc 0 1) t :=
    parabolicRescalePotential_time_jet hρ hρr hρT hPDE (p := (x,t)) ⟨hx,ht⟩
  have hGρ : ContDiffOn ℝ ∞ (fun z => G (ρ • z)) (ball 0 1) :=
    hG.comp (by fun_prop) (fun z hz => hball (ball_subset_closedBall (spatialDilation_mem_ball hρ hρr hz)))
  have hRicρ : ContDiffOn ℝ ∞ (fun z => backgroundRicci G (ρ • z)) (ball 0 1) :=
    hRic.comp (by fun_prop) (fun z hz => hball (ball_subset_closedBall (spatialDilation_mem_ball hρ hρr hz)))
  have hSs (t : ℝ) (_ : t ∈ Icc (-1 : ℝ) 1) : ContDiffOn ℝ ∞ (fun z => S (z,t)) (ball 0 1) :=
    hGρ.add ((hRicρ.const_smul (-(ρ ^ 2))).const_smul (max t 0))
  have hd : ContDiffOn ℝ ∞ d (ball 0 1) :=
    (hq.comp (by fun_prop) (fun z hz => hball (ball_subset_closedBall (spatialDilation_mem_ball hρ hρr hz)))).neg
  have hVs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : ContDiffOn ℝ ∞ (fun z => V (z,t)) (ball 0 1) :=
    forwardZeroSpaceTime_smooth_slices (fun s hs => contDiffOn_space_slice hu hs) ht.2
  have hLog (p : Point n) (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
      forwardZeroSpaceTime P p = Real.log (chartPotentialMatrix S V p).det.re + d p.1 := by
    rw [hMatrix p hp]
    have he := forwardZeroSpaceTime_eq_clamped (F := P) (S := ball (0 : Space n) 1) hP0 hp.1 p.2
    rw [he]
    simp only [P, d, localNativePotentialClock, parabolicDilation, sub_eq_add_neg]
  have hEq (i : RIdx n) : PotentialSpatialWordEquations S V d (realVec i) :=
    zero_extended_potential_word_equations S u P d isOpen_ball zero_lt_one (by norm_num)
      hu hu0 hP0 hJet hSs hd hPos hLog (realVec i)
  have hSlope : |-(ρ ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg ρ)]
    nlinarith
  have hSj (j : ℕ) : HolderBound δ (cylinder (ball 0 1) (-1) 1)
      (fun p => iteratedFDeriv ℝ j (fun z => S (z,p.2)) p.1) (B j) :=
    holderBound_mono_const (hSjets j ρ hρ hρr hρ1 (-(ρ ^ 2)) hSlope) (le_max_left _ _)
  have hdj (j : ℕ) : HolderBound δ (cylinder (ball 0 1) (-1) 1)
      (fun p => iteratedFDeriv ℝ j d p.1) (B j) := by
    apply holderBound_mono_const (C := Kd j) (D := B j) ?_ (le_max_right _ _)
    simpa only [zero_smul, smul_zero, add_zero] using hDjets j ρ hρ hρr hρ1 0 (by norm_num)
  have hi := hInitial F T ρ hρ hρr2 hρ12 hρT2 hF hF0 hPDE hClock hRange
  exact fun k p hp => hJets k S V d hi hSs hVs hd hSj hdj hPos hBounds hEq p hp

theorem affine_potential_zero_scale (ρ τ κ : ℝ) (F : Point n → ℝ) :
    affineParabolicPotential κ 0 0 (affineParabolicPotential ρ 0 τ F) =
      affineParabolicPotential (ρ * κ) 0 τ F := by
  funext p
  simp only [affineParabolicPotential, affineParabolicPullback, affineParabolicPoint,
    add_zero, zero_add, smul_smul, mul_pow, mul_inv_rev, mul_assoc]

theorem affine_potential_quarter_schauder (ρ τ : ℝ) (F : Point n → ℝ)
    {β C : ℝ} (hβ : 0 ≤ β)
    (hu : SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 8)) 0)
      (affineParabolicPotential ρ 0 τ F) C) :
    SchauderBound β (cylinder (ball 0 1) (-1) 0)
      (affineParabolicPotential (ρ * (1 / 4)) 0 τ F) (16 * C) := by
  have hSpace : MapsTo (fun z : Space n => (1 / 4 : ℝ) • z + 0) (ball 0 1) (ball 0 (1 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    simpa only [mem_ball, dist_zero_right, add_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] using
      (show (1 / 4 : ℝ) * ‖z‖ < 1 / 2 by linarith)
  have hClock : MapsTo (fun t : ℝ => 0 + (1 / 4 : ℝ) ^ 2 * t) (Icc (-1) 0) (Icc (-(1 / 8)) 0) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hh := schauderBound_affineParabolicPotential (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : |(1 / 4 : ℝ)| ≤ 1) hβ hSpace hClock hu
  rw [affine_potential_zero_scale] at hh
  simpa only [show |(((1 / 4 : ℝ) ^ 2)⁻¹)| = 16 by norm_num] using hh

theorem fixed_original_chart_backward_spatial_jets
    (hn : 0 < n) (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r α β ell upper Mclock Tcap ρ : ℝ} (hball : closedBall 0 r ⊆ e.source)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hell : 0 < ell) (hUpper : ell ≤ upper) (hM : 0 ≤ Mclock)
    (hTcap : 0 ≤ Tcap) (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρ1 : ρ ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ (F : Point n → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T) →
      (∀ x ∈ ball 0 r, F (x,0) = 0) →
      (∀ x ∈ ball 0 r, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => F (x,s))
        (localNativePotentialClock (pullbackMatrix g e) F (x,t)) (Icc 0 T) t) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T, |localNativePotentialClock (pullbackMatrix g e) F p| ≤ Mclock) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T,
        (localNativePotentialMatrix (pullbackMatrix g e) F p - (ell : ℂ) • 1).PosSemidef ∧
        ((upper : ℂ) • 1 - localNativePotentialMatrix (pullbackMatrix g e) F p).PosSemidef) →
      ∀ k p, p ∈ cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0 →
        ‖iteratedFDeriv ℝ k (fun z => affineParabolicPotential (ρ * (1 / 4)) 0 τ F (z,p.2)) p.1‖ ≤ K k := by
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  let G : Space n → Matrix (Fin n) (Fin n) ℂ := pullbackMatrix g e
  obtain ⟨hG, hRic, hq⟩ := original_chart_background_smooth g hg e he hei
  obtain ⟨Ci, hCi, hInitial⟩ := fixed_original_chart_backward_schauder hn g hg e he hei
    hball hα hα1 hβ hβ1 hell hUpper hM hTcap hρ hρr hρ1
  obtain ⟨D, hD, hWiden⟩ := exists_relative_sandwich_constant (ι := Fin n) (b := upper) hell
  obtain ⟨Ks, hKs, hSjets⟩ := fixed_compact_backward_coefficient_budgets e.open_source hball hG hRic.neg hTcap hδ1.le
  obtain ⟨Kd, hKd, hDjets⟩ := fixed_compact_initial_coefficient_budgets e.open_source hball hq.neg hq.neg hδ1.le
  let B : ℕ → ℝ := fun j => max (Ks j) (Kd j)
  have hB (j : ℕ) : 0 < B j := (hKs j).trans_le (le_max_left _ _)
  have hCi16 : 0 < 16 * Ci := by positivity
  obtain ⟨K, hK, hJets⟩ := compact_coordinate_backward_spatial_jet_budgets hn hδ hδ1 hD hCi16 B hB
  refine ⟨K, hK, ?_⟩
  intro F T τ hCap hLower hUpperTime hF hF0 hPDE hClock hRange
  let a := ρ * (1 / 4 : ℝ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have haρ : a ≤ ρ := by dsimp only [a]; linarith [hρ.le]
  have har : a ≤ r := haρ.trans hρr
  have ha1 : a ≤ 1 := haρ.trans hρ1
  have haLower : a ^ 2 ≤ τ := by dsimp only [a]; nlinarith [sq_nonneg ρ]
  let Q : Set (Point n) := cylinder (ball 0 1) (-1) 0
  let V := affineParabolicPotential a 0 τ F
  let S : Point n → Matrix (Fin n) (Fin n) ℂ := fun p =>
    G (a • p.1) + (τ + a ^ 2 * p.2) • (-backgroundRicci G (a • p.1))
  let d : Space n → ℝ := fun z => -Real.log (G (a • z)).det.re
  have hτ0 : 0 ≤ τ := (sq_nonneg ρ).trans hLower
  have hτ : |τ| ≤ Tcap := by rw [abs_of_nonneg hτ0]; exact hUpperTime.trans hCap
  have hTime : MapsTo (fun t : ℝ => τ + a ^ 2 * t) (Icc (-1) 0) (Icc 0 T) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, sq_nonneg a]
  have hSpace {z : Space n} (hz : z ∈ ball 0 1) : a • z ∈ ball 0 r :=
    spatialDilation_mem_ball ha har hz
  have hMap {p : Point n} (hp : p ∈ Q) : affineParabolicPoint a 0 τ p ∈ ball 0 r ×ˢ Icc 0 T :=
    ⟨by simpa only [affineParabolicPoint, add_zero] using hSpace hp.1, hTime hp.2⟩
  have hV : ContDiffOn ℝ ∞ V Q := by
    change ContDiffOn ℝ ∞ (fun p => (a ^ 2)⁻¹ * F (affineParabolicPoint a 0 τ p)) Q
    exact contDiffOn_const.mul (hF.comp (by unfold affineParabolicPoint; fun_prop) (fun p hp => hMap hp))
  have hMatrix (p : Point n) (hp : p ∈ Q) :
      chartPotentialMatrix S V p = localNativePotentialMatrix G F (affineParabolicPoint a 0 τ p) := by
    unfold chartPotentialMatrix
    rw [leviC_affineParabolicPotential_slice ha.ne'
      (closed_slab_slice_jets hF isOpen_ball (hMap hp).1 (hMap hp).2).1]
    simp only [S, localNativePotentialMatrix, affineParabolicPoint, add_zero, smul_neg,
      Complex.coe_smul, sub_eq_add_neg]
  have hPos (p : Point n) (hp : p ∈ Q) : (chartPotentialMatrix S V p).PosDef := by
    rw [hMatrix p hp]
    have hh := (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)).add_posSemidef
      (hRange _ (hMap hp)).1
    simpa only [add_sub_cancel] using hh
  have hBounds (p : Point n) (hp : p ∈ Q) :
      (chartPotentialMatrix S V p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((D : ℂ) • 1 - chartPotentialMatrix S V p).PosSemidef := by
    rw [hMatrix p hp]
    exact hWiden 1 _ Matrix.PosSemidef.one (hRange _ (hMap hp)).1 (hRange _ (hMap hp)).2
  have hGρ : ContDiffOn ℝ ∞ (fun z => G (a • z)) (ball 0 1) :=
    hG.comp (by fun_prop) (fun z hz => hball (ball_subset_closedBall (hSpace hz)))
  have hRicρ : ContDiffOn ℝ ∞ (fun z => backgroundRicci G (a • z)) (ball 0 1) :=
    hRic.comp (by fun_prop) (fun z hz => hball (ball_subset_closedBall (hSpace hz)))
  have hSs (t : ℝ) (_ : t ∈ Icc (-1 : ℝ) 0) : ContDiffOn ℝ ∞ (fun z => S (z,t)) (ball 0 1) :=
    hGρ.add (hRicρ.neg.const_smul (τ + a ^ 2 * t))
  have hd : ContDiffOn ℝ ∞ d (ball 0 1) :=
    (hq.comp (by fun_prop) (fun z hz => hball (ball_subset_closedBall (hSpace hz)))).neg
  have hJet (x : Space n) (hx : x ∈ ball 0 1) (t : ℝ) (ht : t ∈ Icc (-1) 0) :
      HasDerivWithinAt (fun s => V (x,s))
        (Real.log (chartPotentialMatrix S V (x,t)).det.re + d x) (Icc (-1) 0) t := by
    have hj := affine_potential_clock_jet ha.ne' ht hTime
      (fun s hs => hPDE (a • x + 0) (by simpa only [add_zero] using hSpace hx) s hs)
    apply hj.congr_deriv
    rw [hMatrix (x,t) ⟨hx,ht⟩]
    simp only [localNativePotentialClock, affineParabolicPoint, add_zero, d, G, sub_eq_add_neg]
  have hEq (i : RIdx n) : PotentialWordEquationsOn Q S V d (realVec i) :=
    smooth_potential_word_equations_on_closed_interval S V d isOpen_ball (by norm_num)
      hV hSs hd hPos hJet (realVec i)
  have hSub : Q ⊆ cylinder (ball (0 : Space n) 1) (-1) 1 :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans zero_le_one⟩
  have hSlope : |a ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg a)]; nlinarith [ha.le]
  have hSj (j : ℕ) : HolderBound δ Q
      (fun p => iteratedFDeriv ℝ j (fun z => S (z,p.2)) p.1) (B j) :=
    holderBound_mono_const (holderBound_restrict
      (hSjets j a τ (a ^ 2) ha har ha1 hτ hSlope) hSub) (le_max_left _ _)
  have hdj (j : ℕ) : HolderBound δ Q (fun p => iteratedFDeriv ℝ j d p.1) (B j) := by
    apply holderBound_mono_const (C := Kd j) (D := B j) ?_ (le_max_right _ _)
    have hh := holderBound_restrict (hDjets j a ha har ha1 0 (by norm_num)) hSub
    simpa only [zero_smul, smul_zero, add_zero] using hh
  have hi := affine_potential_quarter_schauder ρ τ F hδ.le
    (hInitial F T τ hCap hLower hUpperTime hF hF0 hPDE hClock hRange)
  exact fun k p hp => hJets S V d hi hSs (fun t ht => contDiffOn_space_slice hV ht)
    hd hSj hdj hPos hBounds hEq k p hp

theorem inverse_potential_spatial_jet_budgets {a : ℝ} (ha : 0 < a) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k (O : Set (Space n))
      (f : Space n → ℝ) (z : Space n) (B : ℝ),
      IsOpen O → ContDiffOn ℝ ∞ f O → a • z ∈ O →
      ‖iteratedFDeriv ℝ k (fun w => (a ^ 2)⁻¹ * f (a • w)) z‖ ≤ B →
      ‖iteratedFDeriv ℝ k f (a • z)‖ ≤ C k * B := by
  classical
  choose R hR hRecover using fun k : ℕ =>
    inverse_spatial_jet_budget (E := Space n) (F := ℝ) k ha.ne'
  refine ⟨fun k => R k * a ^ 2, fun k => mul_pos (hR k) (sq_pos_of_pos ha), ?_⟩
  intro k O f z B hO hf hz hBound
  have hScaled : ContDiffAt ℝ k (fun w => f (a • w)) z :=
    ((hf.contDiffAt (hO.mem_nhds hz)).comp z (by fun_prop)).of_le (by simp)
  have hDerivative := iteratedFDeriv_const_smul_apply' (a := (a ^ 2)⁻¹) hScaled
  have hDerivative' : iteratedFDeriv ℝ k (fun w => (a ^ 2)⁻¹ * f (a • w)) z =
      (a ^ 2)⁻¹ • iteratedFDeriv ℝ k (fun w => f (a • w)) z := by
    simpa only [smul_eq_mul] using hDerivative
  have hNorm : (a ^ 2)⁻¹ * ‖iteratedFDeriv ℝ k (fun w => f (a • w)) z‖ ≤ B := by
    rw [hDerivative'] at hBound
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (sq_pos_of_pos ha))] using hBound
  have hMult := mul_le_mul_of_nonneg_left hNorm (sq_nonneg a)
  have hCancel : a ^ 2 * ((a ^ 2)⁻¹ * ‖iteratedFDeriv ℝ k (fun w => f (a • w)) z‖) =
      ‖iteratedFDeriv ℝ k (fun w => f (a • w)) z‖ := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'), one_mul]
  rw [hCancel] at hMult
  have hh := hRecover k O f z (a ^ 2 * B) hO hf hz hMult
  simpa only [mul_assoc] using hh

theorem fixed_original_chart_closed_spatial_jets
    (hn : 0 < n) (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r α β ell upper Mclock T ρ : ℝ} (hball : closedBall 0 r ⊆ e.source)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hell : 0 < ell) (hUpper : ell ≤ upper) (hM : 0 ≤ Mclock)
    (hT : 0 < T) (hρ : 0 < ρ) (hρr : 4 * ρ ≤ r)
    (hρ1 : 4 * ρ ≤ 1) (hρT : (4 * ρ) ^ 2 ≤ T) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (F : Point n → ℝ),
      ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T) →
      (∀ x ∈ ball 0 r, F (x,0) = 0) →
      (∀ x ∈ ball 0 r, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => F (x,s))
        (localNativePotentialClock (pullbackMatrix g e) F (x,t)) (Icc 0 T) t) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T, |localNativePotentialClock (pullbackMatrix g e) F p| ≤ Mclock) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T,
        (localNativePotentialMatrix (pullbackMatrix g e) F p - (ell : ℂ) • 1).PosSemidef ∧
        ((upper : ℂ) • 1 - localNativePotentialMatrix (pullbackMatrix g e) F p).PosSemidef) →
      ∀ k z, z ∈ ball 0 (ρ / 8) → ∀ t, t ∈ Icc 0 T →
        ‖iteratedFDeriv ℝ k (fun w => F (w,t)) z‖ ≤ C k := by
  obtain ⟨Ki, hKi, hInitial⟩ := fixed_original_chart_initial_spatial_jets hn g hg e he hei
    hball hα hα1 hβ hβ1 hell hUpper hM
  obtain ⟨Kb, hKb, hBackward⟩ := fixed_original_chart_backward_spatial_jets hn g hg e he hei
    hball hα hα1 hβ hβ1 hell hUpper hM hT.le hρ
      (by linarith [hρ.le] : ρ ≤ r) (by linarith [hρ.le] : ρ ≤ 1)
  have hai : 0 < 2 * ρ := by positivity
  have hab : 0 < ρ * (1 / 4 : ℝ) := by positivity
  obtain ⟨Ri, hRi, hRecoverInitial⟩ := inverse_potential_spatial_jet_budgets (n := n) hai
  obtain ⟨Rb, hRb, hRecoverBackward⟩ := inverse_potential_spatial_jet_budgets (n := n) hab
  let C : ℕ → ℝ := fun k => max (Ri k * Ki k) (Rb k * Kb k)
  have hC (k : ℕ) : 0 < C k := (mul_pos (hRi k) (hKi k)).trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro F hF hF0 hPDE hClock hRange k z hz t ht
  have hzNorm : ‖z‖ < ρ / 8 := by simpa only [mem_ball, dist_zero_right] using hz
  have hzSource : z ∈ ball 0 r := ball_subset_ball (by linarith [hρ.le] : ρ / 8 ≤ r) hz
  have hf := contDiffOn_space_slice hF ht
  by_cases ht0 : t = 0
  · subst t
    have hEq : (fun w => F (w,0)) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hzSource] with w hw using hF0 w hw
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using (hC k).le
  have htPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_cases hNear : t ≤ 2 * ρ ^ 2
  · let a : ℝ := 2 * ρ
    let y : Space n := a⁻¹ • z
    let s : ℝ := t / a ^ 2
    have ha : 0 < a := hai
    have hyEq : a • y = z := by simp only [y, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hy : y ∈ ball 0 (1 / 2) := by
      rw [mem_ball, dist_zero_right]
      calc
        ‖y‖ = a⁻¹ * ‖z‖ := by simp only [y, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
        _ < a⁻¹ * (a / 2) := mul_lt_mul_of_pos_left (by dsimp only [a]; linarith) (inv_pos.mpr ha)
        _ = 1 / 2 := by field_simp
    have hsPos : 0 < s := div_pos htPos (sq_pos_of_pos ha)
    have hsUpper : s ≤ 1 / 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
      dsimp only [a]
      nlinarith
    have hsClock : a ^ 2 * s = t := by dsimp only [s]; field_simp
    have hi := hInitial F T a ha
      (by dsimp only [a]; linarith) (by dsimp only [a]; linarith)
      (by dsimp only [a]; nlinarith) hF hF0 hPDE hClock hRange k (y,s)
      ⟨hy, by linarith [hsPos], hsUpper⟩
    have hFun : (fun w => forwardZeroSpaceTime (parabolicRescalePotential a F) (w,s)) =
        fun w => (a ^ 2)⁻¹ * F (a • w,t) := by
      funext w
      simp only [forwardZeroSpaceTime, forwardZeroExtension, ite_eq_right (not_le.mpr hsPos),
        parabolicRescalePotential, parabolicDilation, hsClock]
    rw [hFun] at hi
    have hh := hRecoverInitial k (ball 0 r) (fun w => F (w,t)) y (Ki k)
      isOpen_ball hf (by change a • y ∈ ball 0 r; rw [hyEq]; exact hzSource) hi
    change ‖iteratedFDeriv ℝ k (fun w => F (w,t)) (a • y)‖ ≤ Ri k * Ki k at hh
    rw [hyEq] at hh
    exact hh.trans (le_max_left _ _)
  · let a : ℝ := ρ * (1 / 4 : ℝ)
    let y : Space n := a⁻¹ • z
    have ha : 0 < a := hab
    have hyEq : a • y = z := by simp only [y, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hy : y ∈ ball 0 (1 / 2) := by
      rw [mem_ball, dist_zero_right]
      calc
        ‖y‖ = a⁻¹ * ‖z‖ := by simp only [y, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
        _ < a⁻¹ * (a / 2) := mul_lt_mul_of_pos_left (by dsimp only [a]; linarith) (inv_pos.mpr ha)
        _ = 1 / 2 := by field_simp
    have hb := hBackward F T t le_rfl (by nlinarith [sq_nonneg ρ]) ht.2
      hF hF0 hPDE hClock hRange k (y,0) ⟨hy, by norm_num, le_rfl⟩
    have hFun : (fun w => affineParabolicPotential a 0 t F (w,0)) =
        fun w => (a ^ 2)⁻¹ * F (a • w,t) := by
      funext w
      simp only [affineParabolicPotential, affineParabolicPullback, affineParabolicPoint,
        add_zero, mul_zero]
    rw [hFun] at hb
    have hh := hRecoverBackward k (ball 0 r) (fun w => F (w,t)) y (Kb k)
      isOpen_ball hf (by change a • y ∈ ball 0 r; rw [hyEq]; exact hzSource) hb
    change ‖iteratedFDeriv ℝ k (fun w => F (w,t)) (a • y)‖ ≤ Rb k * Kb k at hh
    rw [hyEq] at hh
    exact hh.trans (le_max_right _ _)

end Yau.NodeProofs.F01Aux
