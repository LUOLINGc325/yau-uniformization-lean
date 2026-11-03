import Yau.LeafProofs.L16WeakSobolevCalculus

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- A function supported in an open region has the same global and restricted L² membership. -/
theorem memLp_global_of_zero_off {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {f : Point n → ℝ} (hf : MemLp f 2 (volume.restrict Q))
    (hZero : ∀ p ∉ Q, f p = 0) : MemLp f 2 volume := by
  have hInd := (memLp_indicator_iff_restrict hQ.measurableSet.nullMeasurableSet).2 hf
  convert! hInd using 1
  ext p
  by_cases hp : p ∈ Q
  · simp only [Set.indicator_of_mem hp]
  · simp only [Set.indicator_of_notMem hp,hZero p hp]

/-- Multiplication by an interior smooth cutoff globalizes restricted L² data. -/
theorem test_mul_memLp_global {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {η f : Point n → ℝ} (hη : Test Q η) (hf : MemLp f 2 (volume.restrict Q)) :
    MemLp (fun p => η p*f p) 2 volume := by
  obtain ⟨C,_hC,hVal,_hDeriv⟩ := smooth_compact_spatial_derivative_bound hη.1 hη.2.1
  apply memLp_global_of_zero_off hQ
    (continuous_bounded_mul_memLp hη.1.continuous hVal hf)
  intro p hp
  have hNot : p ∉ tsupport η := fun h => hp (hη.2.2 h)
  rw [image_eq_zero_of_notMem_tsupport hNot,zero_mul]

/-- The weak derivative identity after cutoff, tested against a global compact smooth function. -/
theorem weakGradientOn_cutoff_integral {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict Q))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict Q))
    (hWeak : WeakGradientOn Q u G) {η φ : Point n → ℝ}
    (hη : Test Q η) (hφ : Test Set.univ φ) (i : Yau.RIdx n) :
    (∫ p, (η p*u p)*fderiv ℝ φ p (Yau.realVec i,0)) =
      -(∫ p, (η p*G p i+u p*fderiv ℝ η p (Yau.realVec i,0))*φ p) := by
  obtain ⟨C,_hC,hVal,hDeriv⟩ := smooth_compact_spatial_derivative_bound hη.1 hη.2.1
  have hηu : MemLp (fun p => η p*u p) 2 (volume.restrict Q) :=
    continuous_bounded_mul_memLp hη.1.continuous hVal hu
  have hηG : MemLp (fun p => η p*G p i) 2 (volume.restrict Q) :=
    continuous_bounded_mul_memLp hη.1.continuous hVal (hG i)
  have huDη : MemLp (fun p => u p*fderiv ℝ η p (Yau.realVec i,0)) 2 (volume.restrict Q) := by
    have hD := test_directionalDerivative hη (Yau.realVec i,0)
    have h := continuous_bounded_mul_memLp hD.1.continuous (fun p => hDeriv p i) hu
    simpa only [mul_comm] using h
  have hφ2 : MemLp φ 2 (volume.restrict Q) :=
    (by simpa only [Measure.restrict_univ] using test_memLp hφ : MemLp φ 2 volume).mono_measure
      Measure.restrict_le_self
  have hDφ2 : MemLp (fun p => fderiv ℝ φ p (Yau.realVec i,0)) 2 (volume.restrict Q) :=
    (by simpa only [Measure.restrict_univ] using test_memLp (test_directionalDerivative hφ (Yau.realVec i,0)) :
      MemLp (fun p => fderiv ℝ φ p (Yau.realVec i,0)) 2 volume).mono_measure Measure.restrict_le_self
  let X : Point n → ℝ := fun p => (η p*u p)*fderiv ℝ φ p (Yau.realVec i,0)
  let Y : Point n → ℝ := fun p => (u p*fderiv ℝ η p (Yau.realVec i,0))*φ p
  let Z : Point n → ℝ := fun p => (η p*G p i)*φ p
  have hX : Integrable X (volume.restrict Q) := hηu.integrable_mul hDφ2
  have hY : Integrable Y (volume.restrict Q) := huDη.integrable_mul hφ2
  have hZ : Integrable Z (volume.restrict Q) := hηG.integrable_mul hφ2
  have hW := hWeak (fun p => η p*φ p) (test_mul_smooth hη hφ.1) i
  have hD (p : Point n) : fderiv ℝ (fun q => η q*φ q) p (Yau.realVec i,0) =
      η p*fderiv ℝ φ p (Yau.realVec i,0)+φ p*fderiv ℝ η p (Yau.realVec i,0) := by
    rw [fderiv_fun_mul (hη.1.differentiable (by simp) p) (hφ.1.differentiable (by simp) p)]
    rfl
  have hLeft : (fun p => u p*fderiv ℝ (fun q => η q*φ q) p (Yau.realVec i,0)) =
      fun p => X p+Y p := by
    funext p
    rw [hD]
    dsimp only [X,Y]
    ring
  have hRight : (fun p => G p i*(η p*φ p)) = Z := by
    funext p
    dsimp only [Z]
    ring
  rw [hLeft,hRight,integral_add hX hY] at hW
  have hZeroη (p : Point n) (hp : p ∉ Q) : η p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (hη.2.2 h))
  have hZeroDη (p : Point n) (hp : p ∉ Q) : fderiv ℝ η p (Yau.realVec i,0) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ η q (Yau.realVec i,0))
      (fun h => hp ((test_directionalDerivative hη (Yau.realVec i,0)).2.2 h))
  have hXGlobal : (∫ p, X p ∂volume.restrict Q) = ∫ p, X p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [X,hZeroη p hp,zero_mul]
  have hGoal : (fun p => (η p*G p i+u p*fderiv ℝ η p (Yau.realVec i,0))*φ p) =
      fun p => Z p+Y p := by
    funext p
    dsimp only [Z,Y]
    ring
  have hSumGlobal : (∫ p, Z p+Y p ∂volume.restrict Q) = ∫ p, Z p+Y p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [Z,Y,hZeroη p hp,hZeroDη p hp,zero_mul,mul_zero,add_zero]
  change (∫ p, X p) = _
  rw [hGoal,← hSumGlobal,integral_add hZ hY,← hXGlobal]
  linarith

/-- Interior cutoff of genuine restricted H¹ data is genuine global compactly supported H¹ data. -/
theorem weakGradientOn_cutoff_weakH1 {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict Q))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict Q))
    (hWeak : WeakGradientOn Q u G) {η : Point n → ℝ} (hη : Test Q η) :
    MemLp (fun p => η p*u p) 2 volume ∧ HasCompactSupport (fun p => η p*u p) ∧
      (∀ i, MemLp (fun p => η p*G p i+u p*fderiv ℝ η p (Yau.realVec i,0)) 2 volume ∧
        HasCompactSupport (fun p => η p*G p i+u p*fderiv ℝ η p (Yau.realVec i,0))) ∧
      WeakGradient Set.univ Set.univ (fun p => η p*u p)
        (fun p i => η p*G p i+u p*fderiv ℝ η p (Yau.realVec i,0)) := by
  refine ⟨test_mul_memLp_global hQ hη hu,hη.2.1.mul_right,?_,?_⟩
  · intro i
    have huDη : MemLp (fun p => u p*fderiv ℝ η p (Yau.realVec i,0)) 2 volume := by
      simpa only [mul_comm] using
        test_mul_memLp_global hQ (test_directionalDerivative hη (Yau.realVec i,0)) hu
    exact ⟨(test_mul_memLp_global hQ hη (hG i)).add huDη,
      hη.2.1.mul_right.add (hη.2.1.fderiv_apply ℝ (Yau.realVec i,0)).mul_left⟩
  · apply (weakGradientOn_prod_iff Set.univ Set.univ _ _).mp
    simp only [Set.univ_prod_univ]
    intro φ hφ i
    simp only [Measure.restrict_univ]
    exact weakGradientOn_cutoff_integral hu hG hWeak hη hφ i

/-- The cutoff function and its actual weak gradient agree with the original data on a plateau. -/
theorem weakGradientOn_cutoff_eq_on_open_plateau {n : ℕ} {U : Set (Point n)}
    (hU : IsOpen U) {η : Point n → ℝ} (hOne : ∀ p ∈ U, η p = 1)
    (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ) {p : Point n} (hp : p ∈ U) :
    η p*u p = u p ∧
      ∀ i, η p*G p i+u p*fderiv ℝ η p (Yau.realVec i,0) = G p i := by
  have hD := fderiv_cutoff_eq_zero_on_open_plateau hU hOne hp
  simp only [hOne p hp,hD,one_mul,zero_apply,mul_zero,add_zero,
    and_self,implies_true]

end Yau.LeafProofs.L16Aux
