import Yau.Proofs.P06CylinderRegularityHeatBounds
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A single compact smooth profile supplies all small-time cutoffs by
linear time dilation, with quantitative bounds for every finite derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ}

def timeScale (τ : ℝ) (hτ : τ ≠ 0) : Point n ≃L[ℝ] Point n where
  toFun p := (p.1, τ * p.2)
  invFun p := (p.1, p.2 / τ)
  left_inv p := by ext <;> simp [hτ]
  right_inv p := by
    change (p.1, τ * (p.2 / τ)) = p
    apply Prod.ext
    · rfl
    · field_simp [hτ]
  map_add' p q := by ext <;> simp [mul_add]
  map_smul' r p := by ext <;> simp [smul_eq_mul, mul_left_comm]
  continuous_toFun := continuous_fst.prodMk (continuous_const.mul continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.div_const τ)

@[simp] theorem timeScale_apply (τ : ℝ) (hτ : τ ≠ 0) (p : Point n) :
    timeScale τ hτ p = (p.1, τ * p.2) := rfl

@[simp] theorem timeScale_symm_apply (τ : ℝ) (hτ : τ ≠ 0) (p : Point n) :
    (timeScale τ hτ).symm p = (p.1, p.2 / τ) := rfl

theorem timeScale_symm_norm_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ‖(timeScale (n := n) τ hτ.ne').symm.toContinuousLinearMap‖ ≤ 1 / τ := by
  have hInv : 1 ≤ 1 / τ := (one_le_div hτ).mpr hτ1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 1 / τ)
  intro p
  change max ‖p.1‖ ‖p.2 / τ‖ ≤ (1 / τ) * max ‖p.1‖ ‖p.2‖
  apply max_le
  · calc
      _ ≤ max ‖p.1‖ ‖p.2‖ := le_max_left _ _
      _ ≤ (1 / τ) * max ‖p.1‖ ‖p.2‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hInv
          (le_trans (norm_nonneg _) (le_max_left _ _))
  · rw [norm_div, Real.norm_of_nonneg hτ.le]
    calc
      _ = (1 / τ) * ‖p.2‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

def rescaleProfile (τ : ℝ) (hτ : τ ≠ 0) (η : Point n → ℝ) : Point n → ℝ :=
  η ∘ (timeScale τ hτ).symm

theorem rescaleProfile_contDiff (τ : ℝ) (hτ : τ ≠ 0) {η : Point n → ℝ}
    (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (rescaleProfile τ hτ η) :=
  hη.comp (timeScale τ hτ).symm.contDiff

theorem rescaleProfile_compact (τ : ℝ) (hτ : τ ≠ 0) {η : Point n → ℝ}
    (hcη : HasCompactSupport η) : HasCompactSupport (rescaleProfile τ hτ η) :=
  hcη.comp_homeomorph (timeScale τ hτ).symm.toHomeomorph

theorem rescaleProfile_test (τ : ℝ) (hτ : τ ≠ 0)
    {Q : Set (Point n)} {η : Point n → ℝ} (hη : Test Q η) :
    Test (timeScale τ hτ '' Q) (rescaleProfile τ hτ η) := by
  refine ⟨rescaleProfile_contDiff τ hτ hη.1, rescaleProfile_compact τ hτ hη.2.1, ?_⟩
  change tsupport (η ∘ (timeScale τ hτ).symm.toHomeomorph) ⊆ _
  rw [tsupport_comp_eq_preimage]
  intro p hp
  exact ⟨(timeScale τ hτ).symm p, hη.2.2 hp, (timeScale τ hτ).apply_symm_apply p⟩

theorem rescaleProfile_tsupport (τ : ℝ) (hτ : τ ≠ 0) (η : Point n → ℝ) :
    tsupport (rescaleProfile τ hτ η) = timeScale τ hτ '' tsupport η := by
  change tsupport (η ∘ (timeScale τ hτ).symm.toHomeomorph) = _
  rw [tsupport_comp_eq_preimage]
  ext p
  constructor
  · intro hp
    exact ⟨(timeScale τ hτ).symm p, hp, (timeScale τ hτ).apply_symm_apply p⟩
  · rintro ⟨q, hq, rfl⟩
    change (timeScale τ hτ).symm (timeScale τ hτ q) ∈ tsupport η
    rwa [(timeScale τ hτ).symm_apply_apply]

theorem rescaleProfile_bound (τ : ℝ) (hτ : τ ≠ 0) {η : Point n → ℝ}
    (hηB : ∀ p, |η p| ≤ 1) : ∀ p, |rescaleProfile τ hτ η p| ≤ 1 :=
  fun p => hηB _

theorem rescaleProfile_germ (τ : ℝ) (hτ : τ ≠ 0)
    {η : Point n → ℝ} {p : Point n} (hη : η =ᶠ[𝓝 p] (fun _ => 1)) :
    rescaleProfile τ hτ η =ᶠ[𝓝 (timeScale τ hτ p)] (fun _ => 1) := by
  have ht : Tendsto (timeScale τ hτ).symm
      (𝓝 (timeScale τ hτ p)) (𝓝 p) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (timeScale τ hτ).symm.continuousAt.tendsto (x := timeScale τ hτ p)
  exact hη.comp_tendsto ht

/-- All orders through a fixed finite budget have a common profile constant,
chosen before the dilation parameter. -/
theorem exists_rescaleProfile_derivative_bound {η : Point n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ j ≤ J, ∀ p, ‖iteratedFDeriv ℝ j (rescaleProfile τ hτ.ne' η) p‖ ≤ C / τ ^ j := by
  obtain ⟨C, hC, hb⟩ := hcη.exists_bound_iteratedFDeriv hη J
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 j hj p
  let T := (timeScale (n := n) τ hτ.ne').symm.toContinuousLinearMap
  have he := T.iteratedFDeriv_comp_right hη p (i := j) (by simp)
  change ‖iteratedFDeriv ℝ j (η ∘ T) p‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j η (T p)‖ * ‖T‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ j η (T p)).norm_compContinuousLinearMap_le (fun _ : Fin j => T)
    _ ≤ C * (1 / τ) ^ j := mul_le_mul (hb j hj _)
      (pow_le_pow_left₀ (norm_nonneg _) (timeScale_symm_norm_le hτ hτ1) j)
      (pow_nonneg (norm_nonneg _) _) hC
    _ = _ := by simp only [div_eq_mul_inv, one_mul, inv_pow]

theorem exists_rescaleProfile_firstDerivative_bound {η : Point n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      (∀ p, |fderiv ℝ (rescaleProfile τ hτ.ne' η) p (0,1)| ≤ M / τ) ∧
      ∀ p i, |fderiv ℝ (rescaleProfile τ hτ.ne' η) p (Yau.realVec i,0)| ≤ M / τ := by
  obtain ⟨C, hC, hb⟩ := exists_rescaleProfile_derivative_bound hη hcη 1
  let V : ℝ := 1 + ∑ i : Yau.RIdx n, ‖(Yau.realVec i, (0 : ℝ))‖
  have hV : 1 ≤ V := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨C * V, mul_nonneg hC (zero_le_one.trans hV), ?_⟩
  intro τ hτ hτ1
  have hOp (p : Point n) : ‖fderiv ℝ (rescaleProfile τ hτ.ne' η) p‖ ≤ C / τ := by
    simpa only [norm_iteratedFDeriv_one, pow_one] using hb τ hτ hτ1 1 le_rfl p
  have hDir (p v : Point n) (hv : ‖v‖ ≤ V) :
      |fderiv ℝ (rescaleProfile τ hτ.ne' η) p v| ≤ C * V / τ := by
    calc
      _ = ‖fderiv ℝ (rescaleProfile τ hτ.ne' η) p v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (rescaleProfile τ hτ.ne' η) p‖ * ‖v‖ :=
        (fderiv ℝ (rescaleProfile τ hτ.ne' η) p).le_opNorm v
      _ ≤ (C / τ) * V := mul_le_mul (hOp p) hv (norm_nonneg _) (div_nonneg hC hτ.le)
      _ = _ := by ring
  refine ⟨fun p => hDir p (0,1) (by simpa using hV), ?_⟩
  intro p i
  apply hDir
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (Yau.realVec j, (0 : ℝ)))
    (Finset.mem_univ i)).trans (by dsimp only [V]; linarith)

end Yau.NodeProofs.P06Aux.SmallTimeCylinder
