import Yau.LeafProofs.L16WeakSourceCalculus
import Yau.LeafProofs.L16WeakCutoff

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- A concrete distributional derivative along one joint space-time direction. -/
def WeakDirectionalDerivativeOn {n : ℕ} (Q : Set (Point n)) (e : Point n)
    (u g : Point n → ℝ) : Prop :=
  ∀ φ : Point n → ℝ, Test Q φ →
    (∫ p, u p*fderiv ℝ φ p e ∂volume.restrict Q) = -(∫ p, g p*φ p ∂volume.restrict Q)

theorem weakGradientOn_directional {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hW : WeakGradientOn Q u G) (i : Yau.RIdx n) :
    WeakDirectionalDerivativeOn Q (Yau.realVec i,0) u (fun p => G p i) := by
  intro φ hφ
  exact hW φ hφ i

theorem weakDivergenceEvolutionOn_timeDerivative {n : ℕ} {Q : Set (Point n)}
    {u R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    {K : Yau.RIdx n → Point n → Yau.RIdx n → ℝ}
    (hEq : WeakDivergenceEvolutionOn Q u P R)
    (hP : ∀ j, WeakGradientOn Q (fun p => P p j) (K j))
    (hK : ∀ j, MemLp (fun p => K j p j) 2 (volume.restrict Q))
    (hR : MemLp R 2 (volume.restrict Q)) :
    MemLp (fun p => (∑ j, K j p j)+R p) 2 (volume.restrict Q) ∧
      WeakDirectionalDerivativeOn Q (0,1) u (fun p => (∑ j, K j p j)+R p) := by
  have hSum := memLp_finsetSum Finset.univ (fun j _ => hK j)
  have hSource : MemLp (fun p => (∑ j, K j p j)+R p) 2 (volume.restrict Q) := by
    convert! hSum.add hR using 1
  refine ⟨hSource,?_⟩
  intro φ hφ
  have h := hEq φ hφ
  have hSpace (j : Yau.RIdx n) := hP j φ hφ j
  have hIntK (j : Yau.RIdx n) : Integrable (fun p => K j p j*φ p) (volume.restrict Q) :=
    (hK j).integrable_mul (test_memLp hφ)
  have hIntR : Integrable (fun p => R p*φ p) (volume.restrict Q) :=
    hR.integrable_mul (test_memLp hφ)
  have hIntSum : Integrable (fun p => (∑ j, K j p j)*φ p) (volume.restrict Q) := by
    have hS := integrable_finsetSum Finset.univ (fun j _ => hIntK j)
    simpa only [Finset.sum_mul] using hS
  have hPair : (∫ p, ((∑ j, K j p j)+R p)*φ p ∂volume.restrict Q) =
      (∑ j, ∫ p, K j p j*φ p ∂volume.restrict Q)+(∫ p, R p*φ p ∂volume.restrict Q) := by
    simp_rw [add_mul]
    rw [integral_add hIntSum hIntR]
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun j _ => hIntK j)]
  change (∫ p, u p*fderiv ℝ φ p (0,1) ∂volume.restrict Q) = _
  rw [hPair]
  simp_rw [hSpace] at h
  rw [Finset.sum_neg_distrib] at h
  linarith


theorem weakDirectionalDerivativeOn_smooth_compact_mul {n : ℕ} {Q : Set (Point n)}
    {u z g : Point n → ℝ} {e : Point n}
    (hu : MemLp u 2 (volume.restrict Q)) (hz : MemLp z 2 (volume.restrict Q))
    (hWeak : WeakDirectionalDerivativeOn Q e u z)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    MemLp (fun p => g p*u p) 2 (volume.restrict Q) ∧
      MemLp (fun p => g p*z p+u p*fderiv ℝ g p e) 2 (volume.restrict Q) ∧
      WeakDirectionalDerivativeOn Q e (fun p => g p*u p)
        (fun p => g p*z p+u p*fderiv ℝ g p e) := by
  obtain ⟨C,_hC,hValNorm,hDerivNorm,_hLip⟩ := smooth_compact_global_bounds hg hcg
  have hVal (p : Point n) : |g p| ≤ C := by simpa only [Real.norm_eq_abs] using hValNorm p
  have hDeriv (p : Point n) : |fderiv ℝ g p e| ≤ C*‖e‖ := by
    have hEval := (fderiv ℝ g p).le_opNorm e
    rw [Real.norm_eq_abs] at hEval
    exact hEval.trans (mul_le_mul_of_nonneg_right (hDerivNorm p) (norm_nonneg e))
  have hgu : MemLp (fun p => g p*u p) 2 (volume.restrict Q) :=
    continuous_bounded_mul_memLp hg.continuous hVal hu
  have hgz : MemLp (fun p => g p*z p) 2 (volume.restrict Q) :=
    continuous_bounded_mul_memLp hg.continuous hVal hz
  have huDg : MemLp (fun p => u p*fderiv ℝ g p e) 2 (volume.restrict Q) := by
    have hDCont : Continuous (fun p => fderiv ℝ g p e) :=
      ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    have h := continuous_bounded_mul_memLp hDCont hDeriv hu
    convert! h using 1
    ext p
    ring
  refine ⟨hgu,hgz.add huDg,?_⟩
  intro φ hφ
  have hφ2 := test_memLp hφ
  have hDφ2 := test_memLp (test_directionalDerivative hφ e)
  have hX : Integrable (fun p => (g p*u p)*fderiv ℝ φ p e) (volume.restrict Q) :=
    hgu.integrable_mul hDφ2
  have hY : Integrable (fun p => (u p*fderiv ℝ g p e)*φ p) (volume.restrict Q) :=
    huDg.integrable_mul hφ2
  have hZ : Integrable (fun p => (g p*z p)*φ p) (volume.restrict Q) :=
    hgz.integrable_mul hφ2
  have h := hWeak (fun p => φ p*g p) (test_mul_smooth hφ hg)
  have hD (p : Point n) : fderiv ℝ (fun q => φ q*g q) p e =
      φ p*fderiv ℝ g p e+g p*fderiv ℝ φ p e := by
    rw [fderiv_fun_mul (hφ.1.differentiable (by simp) p) (hg.differentiable (by simp) p)]
    rfl
  have hLeft : (fun p => u p*fderiv ℝ (fun q => φ q*g q) p e) =
      fun p => (g p*u p)*fderiv ℝ φ p e+(u p*fderiv ℝ g p e)*φ p := by
    funext p
    rw [hD]
    ring
  have hRight : (fun p => z p*(φ p*g p)) = fun p => (g p*z p)*φ p := by
    funext p
    ring
  rw [hLeft,hRight] at h
  have hSplit1 := integral_add hX hY
  rw [hSplit1] at h
  have hGoal : (fun p => (g p*z p+u p*fderiv ℝ g p e)*φ p) =
      fun p => (g p*z p)*φ p+(u p*fderiv ℝ g p e)*φ p := by
    funext p
    ring
  rw [hGoal]
  have hSplit2 := integral_add hZ hY
  rw [hSplit2]
  linarith


theorem weak_time_spatial_derivatives_commute {n : ℕ} {Q : Set (Point n)}
    {u T : Point n → ℝ} {G S : Point n → Yau.RIdx n → ℝ}
    (hWG : WeakGradientOn Q u G)
    (hTime : WeakDirectionalDerivativeOn Q (0,1) u T)
    (hTimeG : ∀ i, WeakDirectionalDerivativeOn Q (0,1) (fun p => G p i) (fun p => S p i)) :
    WeakGradientOn Q T S := by
  intro φ hφ i
  have h1 := hTime (fun p => fderiv ℝ φ p (Yau.realVec i,0))
    (test_directionalDerivative hφ (Yau.realVec i,0))
  have h2 := hWG (fun p => fderiv ℝ φ p (0,1))
    (test_directionalDerivative hφ (0,1)) i
  have h3 := hTimeG i φ hφ
  have hComm : (fun p => u p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (0,1)) =
      fun p => u p*fderiv ℝ (fun q => fderiv ℝ φ q (0,1)) p (Yau.realVec i,0) := by
    funext p
    rw [directional_gradient_commute (hφ.1.of_le (by simp))]
  change (∫ p, u p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (0,1) ∂volume.restrict Q) = _ at h1
  rw [hComm] at h1
  linarith

theorem weakDirectionalDerivativeOn_global_of_support {n : ℕ} {Q K : Set (Point n)}
    (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    {e : Point n} {u z : Point n → ℝ}
    (hWeak : WeakDirectionalDerivativeOn Q e u z)
    (huZero : ∀ p ∉ K, u p = 0) (hzZero : ∀ p ∉ K, z p = 0) :
    WeakDirectionalDerivativeOn Set.univ e u z := by
  obtain ⟨χ,hχ,hNear⟩ := exists_test_eq_one_near_compact hQ hK hKQ
  intro φ hφ
  have hTest := test_mul_smooth hχ hφ.1
  have h := hWeak (fun p => χ p*φ p) hTest
  rw [test_pairing_integral_restrict (test_directionalDerivative hTest e) u,
    test_pairing_integral_restrict hTest z] at h
  have hLeft : (fun p => u p*fderiv ℝ (fun q => χ q*φ q) p e) =
      fun p => u p*fderiv ℝ φ p e := by
    funext p
    by_cases hp : p ∈ K
    · have hEq : (fun q => χ q*φ q) =ᶠ[𝓝 p] φ := by
        filter_upwards [hNear p hp] with q hq
        simp only [hq,one_mul]
      rw [hEq.fderiv_eq]
    · simp only [huZero p hp,zero_mul]
  have hRight : (fun p => z p*(χ p*φ p)) = fun p => z p*φ p := by
    funext p
    by_cases hp : p ∈ K
    · rw [(hNear p hp).eq_of_nhds,one_mul]
    · simp only [hzZero p hp,zero_mul]
  rw [hLeft,hRight] at h
  simpa only [Measure.restrict_univ] using h

theorem weakDirectionalDerivativeOn_cutoff {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u z η : Point n → ℝ} {e : Point n}
    (hu : MemLp u 2 (volume.restrict Q)) (hz : MemLp z 2 (volume.restrict Q))
    (hWeak : WeakDirectionalDerivativeOn Q e u z) (hη : Test Q η) :
    MemLp (fun p => η p*u p) 2 volume ∧ HasCompactSupport (fun p => η p*u p) ∧
      MemLp (fun p => η p*z p+u p*fderiv ℝ η p e) 2 volume ∧
      HasCompactSupport (fun p => η p*z p+u p*fderiv ℝ η p e) ∧
      WeakDirectionalDerivativeOn Set.univ e (fun p => η p*u p)
        (fun p => η p*z p+u p*fderiv ℝ η p e) := by
  have hData := weakDirectionalDerivativeOn_smooth_compact_mul hu hz hWeak hη.1 hη.2.1
  have hZero (p : Point n) (hp : p ∉ tsupport η) : η p = 0 :=
    image_eq_zero_of_notMem_tsupport hp
  have hDZero (p : Point n) (hp : p ∉ tsupport η) : fderiv ℝ η p e = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ η q e)
      (fun h => hp (tsupport_fderiv_apply_subset ℝ e h))
  have hValZero (p : Point n) (hp : p ∉ tsupport η) : η p*u p = 0 := by
    rw [hZero p hp,zero_mul]
  have hGradZero (p : Point n) (hp : p ∉ tsupport η) : η p*z p+u p*fderiv ℝ η p e = 0 := by
    rw [hZero p hp,hDZero p hp,zero_mul,mul_zero,add_zero]
  refine ⟨test_mul_memLp_global hQ hη hu,hη.2.1.mul_right,?_,
    hη.2.1.mul_right.add (hη.2.1.fderiv_apply ℝ e).mul_left,
    weakDirectionalDerivativeOn_global_of_support hQ hη.2.1 hη.2.2 hData.2.2 hValZero hGradZero⟩
  exact memLp_global_of_zero_off hQ hData.2.1 (fun p hp =>
    hGradZero p (fun h => hp (hη.2.2 h)))

end Yau.LeafProofs.L16Aux
