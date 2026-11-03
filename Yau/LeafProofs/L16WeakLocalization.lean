import Yau.LeafProofs.L16LocalEnergy

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem d_eq_joint_fderiv {n : ℕ} {φ : Point n → ℝ} {p : Point n}
    (hφ : DifferentiableAt ℝ φ p) (i : Yau.RIdx n) :
    d (fun x => φ (x,p.2)) p.1 i = fderiv ℝ φ p (Yau.realVec i,0) := by
  have hMap : HasFDerivAt (fun x : Space n => (x,p.2))
      ((ContinuousLinearMap.id ℝ (Space n)).prod 0) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hSlice := hφ.hasFDerivAt.comp p.1 hMap
  change fderiv ℝ (φ ∘ (fun x : Space n => (x,p.2))) p.1 (Yau.realVec i) = _
  rw [hSlice.fderiv]
  rfl

theorem test_directionalDerivative {n : ℕ} {Q : Set (Point n)} {φ : Point n → ℝ}
    (hφ : Test Q φ) (e : Point n) : Test Q (fun p => fderiv ℝ φ p e) := by
  refine ⟨(hφ.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    hφ.2.1.fderiv_apply ℝ e,?_⟩
  exact (tsupport_fderiv_apply_subset ℝ e).trans hφ.2.2

theorem test_spatialDerivative {n : ℕ} {Q : Set (Point n)} {φ : Point n → ℝ}
    (hφ : Test Q φ) (i : Yau.RIdx n) :
    Test Q (fun p => d (fun x => φ (x,p.2)) p.1 i) := by
  have hEq : (fun p => d (fun x => φ (x,p.2)) p.1 i) =
      (fun p => fderiv ℝ φ p (Yau.realVec i,0)) := by
    funext p
    exact d_eq_joint_fderiv (hφ.1.differentiable (by simp) p) i
  rw [hEq]
  exact test_directionalDerivative hφ _

theorem test_mul_smooth {n : ℕ} {Q : Set (Point n)} {η φ : Point n → ℝ}
    (hη : Test Q η) (hφ : ContDiff ℝ ∞ φ) : Test Q (fun p => η p*φ p) := by
  refine ⟨hη.1.mul hφ,hη.2.1.mul_right,?_⟩
  exact tsupport_mul_subset_left.trans hη.2.2

theorem test_spatialDerivative_mul {n : ℕ} {η φ : Point n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hφ : ContDiff ℝ ∞ φ) (p : Point n) (i : Yau.RIdx n) :
    d (fun x => η (x,p.2)*φ (x,p.2)) p.1 i =
      η p * d (fun x => φ (x,p.2)) p.1 i +
      φ p * d (fun x => η (x,p.2)) p.1 i := by
  rw [d_eq_joint_fderiv ((hη.mul hφ).differentiable (by simp) p),
    d_eq_joint_fderiv (hη.differentiable (by simp) p),
    d_eq_joint_fderiv (hφ.differentiable (by simp) p)]
  rw [fderiv_fun_mul (hη.differentiable (by simp) p) (hφ.differentiable (by simp) p)]
  rfl

theorem contDiff_spatialDerivative {n : ℕ} {φ : Point n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : Yau.RIdx n) :
    ContDiff ℝ ∞ (fun p : Point n => d (fun x => φ (x,p.2)) p.1 i) := by
  have h : ContDiff ℝ ∞ (fun p : Point n => fderiv ℝ φ p (Yau.realVec i,0)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_const (c := (Yau.realVec i,0)))
  convert! h using 1
  ext p
  exact d_eq_joint_fderiv (hφ.differentiable (by simp) p) i

theorem integral_mul_test_eq {n : ℕ} {Q : Set (Point n)} {η : Point n → ℝ}
    (hη : Test Q η) (z : Point n → ℝ) :
    (∫ p, z p*η p ∂volume.restrict Q) = ∫ p, z p*η p := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hNot : p ∉ tsupport η := fun h => hp (hη.2.2 h)
  rw [image_eq_zero_of_notMem_tsupport hNot,mul_zero]

theorem localEnergy_weakGradient_cutoff {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η φ : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) (hφ : ContDiff ℝ ∞ φ) (i : Yau.RIdx n) :
    (∫ p, (η p*u p)*d (fun x => φ (x,p.2)) p.1 i) =
      -(∫ p, (η p*G p i + u p*d (fun x => η (x,p.2)) p.1 i)*φ p) := by
  have hTest := test_mul_smooth hη hφ
  have hW := hE.1 (fun p => η p*φ p) hTest i
  rw [productVolume_eq_restrict,
    integral_mul_test_eq (test_spatialDerivative hTest i) u,
    integral_mul_test_eq hTest (fun p => G p i)] at hW
  let X : Point n → ℝ := fun p => (η p*u p)*d (fun x => φ (x,p.2)) p.1 i
  let Y : Point n → ℝ := fun p => u p*d (fun x => η (x,p.2)) p.1 i*φ p
  let Z : Point n → ℝ := fun p => η p*G p i*φ p
  have hX : Integrable X volume := by
    have hT := test_mul_smooth hη (contDiff_spatialDerivative hφ i)
    have h := (localEnergy_cutoff_integrable hO hE hT.1.continuous hT.2.1 hT.2.2).1
    convert! h using 1
    ext p
    dsimp only [X]
    ring
  have hY : Integrable Y volume := by
    have hT := test_mul_smooth (test_spatialDerivative hη i) hφ
    have h := (localEnergy_cutoff_integrable hO hE hT.1.continuous hT.2.1 hT.2.2).1
    convert! h using 1
    ext p
    dsimp only [Y]
    ring
  have hZ : Integrable Z volume := by
    have h := (localEnergy_cutoff_integrable hO hE hTest.1.continuous hTest.2.1 hTest.2.2).2 i
    convert! h using 1
    ext p
    dsimp only [Z]
    ring
  have hLeft : (fun p => u p*d (fun x => η (x,p.2)*φ (x,p.2)) p.1 i) =
      fun p => X p+Y p := by
    funext p
    rw [test_spatialDerivative_mul hη.1 hφ]
    dsimp only [X,Y]
    ring
  have hRight : (fun p => G p i*(η p*φ p)) = Z := by
    funext p
    dsimp only [Z]
    ring
  rw [hLeft,hRight,integral_add hX hY] at hW
  have hGoal : (fun p => (η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i)*φ p) =
      fun p => Z p+Y p := by
    funext p
    dsimp only [Z,Y]
    ring
  change (∫ p, X p) = _
  rw [hGoal,integral_add hZ hY]
  linarith

theorem localEnergy_cutoff_weakH1 {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) :
    MemLp (fun p => η p*u p) 2 volume ∧
      (∀ i, MemLp (fun p => η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i) 2 volume) ∧
      WeakGradient Set.univ Set.univ (fun p => η p*u p)
        (fun p i => η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i) := by
  obtain ⟨hu,hG⟩ := localEnergy_cutoff_memLp hO hE hη.1.continuous hη.2.1 hη.2.2
  refine ⟨hu,?_,?_⟩
  · intro i
    have hT := test_spatialDerivative hη i
    have hU := (localEnergy_cutoff_memLp hO hE hT.1.continuous hT.2.1 hT.2.2).1
    have hU' : MemLp (fun p => u p*d (fun x => η (x,p.2)) p.1 i) 2 volume := by
      simpa only [mul_comm] using hU
    exact (hG i).add hU'
  · intro φ hφ i
    rw [productVolume_eq_restrict]
    simp only [Set.univ_prod_univ,Measure.restrict_univ]
    exact localEnergy_weakGradient_cutoff hO hE hη hφ.1 i

theorem test_mul_contDiffOn {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {η g : Point n → ℝ} (hη : Test Q η) (hg : ContDiffOn ℝ ∞ g Q) :
    Test Q (fun p => η p*g p) := by
  have hSmooth : ContDiff ℝ ∞ (fun p => η p*g p) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ tsupport η
    · exact hη.1.contDiffAt.mul ((hg p (hη.2.2 hp)).contDiffAt (hQ.mem_nhds (hη.2.2 hp)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hZero : η =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
      filter_upwards [hZero] with q hq
      simp only [Pi.zero_apply] at hq
      simp only [hq,zero_mul]
  exact ⟨hSmooth,hη.2.1.mul_right,tsupport_mul_subset_left.trans hη.2.2⟩

theorem contDiffOn_spatialDerivative_of_isOpen {n : ℕ} {Q : Set (Point n)}
    (hQ : IsOpen Q) {g : Point n → ℝ} (hg : ContDiffOn ℝ ∞ g Q) (i : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (fun p : Point n => d (fun x => g (x,p.2)) p.1 i) Q := by
  have h : ContDiffOn ℝ ∞ (fun p : Point n => fderiv ℝ g p (Yau.realVec i,0)) Q :=
    (hg.fderiv_of_isOpen hQ (by simp)).clm_apply contDiffOn_const
  apply h.congr
  intro p hp
  exact d_eq_joint_fderiv (((hg p hp).contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp)) i

end Yau.LeafProofs.L16Aux
