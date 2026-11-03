import Yau.LeafProofs.L16Caccioppoli
import Yau.LeafProofs.L16SmoothEnergy

/-! Compact extensions and the actual residual energy identity used by the
local finite-system parabolic estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

section Cutoffs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_sum {ι : Type*} [Fintype ι] (f : ι → E → ℝ)
    (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun p => ∑ i, f i p) := by
  classical
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (f := f) (fun i _ => hf i)
  convert h using 1
  funext p
  simp only [Finset.sum_apply]

theorem compact_square {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun p => f p^2) := by
  rw [show (fun p => f p^2) = f*f by funext p; rw [Pi.mul_apply,pow_two]]
  exact hf.mul_right

theorem cutoff_contDiff {O : Set E} (hO : IsOpen O)
    {χ f : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ O) (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun p => χ p * f p) ∧
      HasCompactSupport (fun p => χ p * f p) := by
  have hs : tsupport (fun p => χ p * f p) ⊆ tsupport χ := tsupport_mul_subset_left
  refine ⟨?_, hcχ.of_isClosed_subset (isClosed_tsupport _) hs⟩
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds (hχO hp)))
  · have heq : (fun q => χ q * f q) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport χ).compl_mem_nhds hp] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem cutoff_eq_germ {χ f : E → ℝ} {p : E}
    (hχ : χ =ᶠ[𝓝 p] (fun _ => 1)) :
    (fun q => χ q * f q) =ᶠ[𝓝 p] f := by
  filter_upwards [hχ] with q hq
  simp only [hq, one_mul]

end Cutoffs

theorem exists_bounded_test_eq_one_near_compact {n : ℕ} {Q K : Set (Point n)}
    (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q) :
    ∃ η : Point n → ℝ, Test Q η ∧ (∀ p, |η p| ≤ 1) ∧
      ∀ p ∈ K, η =ᶠ[𝓝 p] (fun _ => 1) := by
  obtain ⟨V,hV,hKV,hVQ,hVC⟩ := exists_open_between_and_isCompact_closure hK hQ hKQ
  obtain ⟨W,hW,hVW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
  obtain ⟨η,hη,hRange,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW
      (isClosed_closure : IsClosed (closure V)) hVW
  have hcη : HasCompactSupport η := by
    change IsCompact (tsupport η)
    simpa only [tsupport,hSupport] using hWC
  have hηQ : tsupport η ⊆ Q := by simpa only [tsupport,hSupport] using hWQ
  refine ⟨η,⟨hη,hcη,hηQ⟩,?_,?_⟩
  · intro p
    have hp := hRange (Set.mem_range_self p)
    exact abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
  · intro p hp
    filter_upwards [hV.mem_nhds (hKV hp)] with q hq
    exact (hOne q).mp (subset_closure hq)

def spatialGradient {n : ℕ} (w : Point n → ℝ) (p : Point n) (i : Yau.RIdx n) : ℝ :=
  fderiv ℝ w p (Yau.realVec i, 0)

def divergenceResidual {n : ℕ} (w : Point n → ℝ)
    (P : Point n → Yau.RIdx n → ℝ) (p : Point n) : ℝ :=
  fderiv ℝ w p (0,1) - ∑ i, fderiv ℝ (fun q => P q i) p (Yau.realVec i,0)

theorem gradient_contDiff {n : ℕ} {w : Point n → ℝ}
    (hw : ContDiff ℝ ∞ w) (i : Yau.RIdx n) :
    ContDiff ℝ ∞ (fun p => spatialGradient w p i) :=
  (hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem residual_contDiff {n : ℕ} {w : Point n → ℝ}
    {P : Point n → Yau.RIdx n → ℝ}
    (hw : ContDiff ℝ ∞ w) (hP : ∀ i, ContDiff ℝ ∞ (fun p => P p i)) :
    ContDiff ℝ ∞ (divergenceResidual w P) := by
  exact ((hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).sub
    (ContDiff.sum fun i _ =>
      ((hP i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem residual_compact {n : ℕ} {w : Point n → ℝ}
    {P : Point n → Yau.RIdx n → ℝ}
    (hw : HasCompactSupport w) (hP : ∀ i, HasCompactSupport (fun p => P p i)) :
    HasCompactSupport (divergenceResidual w P) := by
  have hs : HasCompactSupport (fun p => ∑ i, fderiv ℝ (fun q => P q i) p
      (Yau.realVec i,0)) := by
    have h := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i p => fderiv ℝ (fun q => P q i) p (Yau.realVec i,0))
      (fun i (_ : i ∈ Finset.univ) => (hP i).fderiv_apply ℝ (Yau.realVec i,0))
    convert h using 1
    funext p
    simp only [Finset.sum_apply]
  exact (hw.fderiv_apply ℝ (0,1)).sub hs

/-- The equation for the global residual is an identity everywhere. In
particular, no equation outside the local PDE region is required. -/
theorem residual_energy_zero {n : ℕ} {w η : Point n → ℝ}
    {P : Point n → Yau.RIdx n → ℝ}
    (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w)
    (hP : ∀ i, ContDiff ℝ ∞ (fun p => P p i))
    (hcP : ∀ i, HasCompactSupport (fun p => P p i))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    compactEnergyFunctional (fun p => η p ^ 2) w (spatialGradient w) P
      (divergenceResidual w P) = 0 := by
  have hψ : ContDiff ℝ ∞ (fun p => η p ^ 2) := hη.pow 2
  have hcψ : HasCompactSupport (fun p => η p ^ 2) := by
    rw [show (fun p => η p ^ 2) = η * η by funext p; rw [Pi.mul_apply,pow_two]]
    exact hcη.mul_right
  have hwL : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hcw
  have hHL (i : Yau.RIdx n) : MemLp (fun p => spatialGradient w p i) 2 volume :=
    (gradient_contDiff hw i).continuous.memLp_of_hasCompactSupport
      (hcw.fderiv_apply ℝ (Yau.realVec i,0))
  have hPL (i : Yau.RIdx n) : MemLp (fun p => P p i) 2 volume :=
    (hP i).continuous.memLp_of_hasCompactSupport (hcP i)
  have hRL : MemLp (divergenceResidual w P) 2 volume :=
    (residual_contDiff hw hP).continuous.memLp_of_hasCompactSupport
      (residual_compact hcw hcP)
  rw [← integral_energy_eq_compactEnergyFunctional hψ hcψ hwL hHL hPL hRL]
  exact smooth_divergence_energy_identity hw hP hψ hcψ (fun p => by
    simp only [divergenceResidual]
    ring)

end Yau.NodeProofs.P06Aux.CylinderReg
