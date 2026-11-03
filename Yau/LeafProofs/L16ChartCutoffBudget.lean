import Yau.LeafProofs.L16RelativeCutoffExtension
import Yau.LeafProofs.L16HalfSpaceLowInterpolation

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartCutoffBudget_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartCutoffBudget_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance chartCutoffBudget_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance chartCutoffBudget_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Continuous compactly supported functions have a genuine uniform norm bound. -/
theorem compactSupport_continuous_norm_bound {E G : Type*} [TopologicalSpace E]
    [NormedAddCommGroup G] {f : E → G} (hc : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨1+|C|,by positivity,?_⟩
  intro x
  by_cases hx : x ∈ tsupport f
  · exact (hC x hx).trans (by linarith [le_abs_self C])
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    positivity

/-- Actual smooth compact spatial cutoffs have one uniform bound for all
    jets used in the raw parabolic product rule. -/
theorem compact_cutoff_actual_jet_bound {n : ℕ} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ E : ℝ, 0 < E ∧ ∀ x, |φ x| ≤ E ∧ ‖fderiv ℝ φ x‖ ≤ E ∧ ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ E := by
  obtain ⟨E0,hE0,h0⟩ := compactSupport_continuous_norm_bound hφ.continuous hc
  obtain ⟨E1,hE1,h1⟩ := compactSupport_continuous_norm_bound (hφ.continuous_fderiv (by simp)) (hc.fderiv (𝕜 := ℝ))
  obtain ⟨E2,hE2,h2⟩ := compactSupport_continuous_norm_bound
    ((hφ.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)) ((hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  refine ⟨E0+E1+E2,by positivity,?_⟩
  intro x
  have hh0 : |φ x| ≤ E0 := h0 x
  exact ⟨by linarith [hh0],by linarith [h1 x],by linarith [h2 x]⟩

/-- Honest raw four-jet bounds for a cutoff product extended only across
    artificial spatial edges; the actual model boundary is retained. -/
theorem cutoff_relative_raw_jet_bound {n : ℕ} {S V : Set (Space n)} {l r E K : ℝ}
    (hE : 0 ≤ E) (hK : 0 ≤ K) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ V)
    (hφBound : ∀ x, |φ x| ≤ E ∧ ‖fderiv ℝ φ x‖ ≤ E ∧ ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ E)
    {u : Point n → ℝ} (hu : C2 (cylinder (S∩V) l r) u)
    (hBound : ∀ p ∈ cylinder (S∩V) l r, |u p| ≤ K ∧ ‖spatialD u p‖ ≤ K ∧
      ‖spatialDD u p‖ ≤ K ∧ |timeD (cylinder (S∩V) l r) u p| ≤ K)
    {p : Point n} (hp : p ∈ cylinder S l r) :
    let w := fun p : Point n => φ p.1*u p
    |w p| ≤ 4*E*K ∧ ‖spatialD w p‖ ≤ 4*E*K ∧ ‖spatialDD w p‖ ≤ 4*E*K ∧
      |timeD (cylinder S l r) w p| ≤ 4*E*K := by
  dsimp only
  by_cases hpSupport : p.1 ∈ tsupport φ
  · have hpLocal : p ∈ cylinder (S∩V) l r := ⟨⟨hp.1,hSupport hpSupport⟩,hp.2⟩
    obtain ⟨hu0,hu1,hu2,hut⟩ := hBound p hpLocal
    obtain ⟨hφ0,hφ1,hφ2⟩ := hφBound p.1
    have hφAt := hφ.contDiffAt (x := p.1)
    have huAt := hu.2.2.2.2.1 p hpLocal
    refine ⟨?_,?_,?_,?_⟩
    · rw [abs_mul]
      exact (mul_le_mul hφ0 hu0 (abs_nonneg _) hE).trans (by nlinarith [mul_nonneg hE hK])
    · change ‖fderiv ℝ (fun x => φ x*u (x,p.2)) p.1‖ ≤ _
      rw [fderiv_fun_mul (hφAt.differentiableAt (by norm_num)) (huAt.differentiableAt (by norm_num))]
      change ‖φ p.1 • spatialD u p+u p • fderiv ℝ φ p.1‖ ≤ _
      have ha : ‖φ p.1 • spatialD u p‖ ≤ E*K := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul hφ0 hu1 (norm_nonneg _) hE
      have hb : ‖u p • fderiv ℝ φ p.1‖ ≤ K*E := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul hu0 hφ1 (norm_nonneg _) hK
      exact (norm_add_le _ _).trans (by nlinarith [ha,hb,mul_nonneg hE hK])
    · change ‖fderiv ℝ (fderiv ℝ (fun x => φ x*u (x,p.2))) p.1‖ ≤ _
      rw [secondFDeriv_mul hφAt huAt]
      let A := φ p.1 • spatialDD u p
      let B := (fderiv ℝ φ p.1).smulRight (spatialD u p)
      let C := (spatialD u p).smulRight (fderiv ℝ φ p.1)
      let D := u p • fderiv ℝ (fderiv ℝ φ) p.1
      have ha : ‖A‖ ≤ E*K := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul hφ0 hu2 (norm_nonneg _) hE
      have hb : ‖B‖ ≤ E*K := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul hφ1 hu1 (norm_nonneg _) hE
      have hc : ‖C‖ ≤ K*E := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul hu1 hφ1 (norm_nonneg _) hK
      have hd : ‖D‖ ≤ K*E := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul hu0 hφ2 (norm_nonneg _) hK
      change ‖A+B+C+D‖ ≤ _
      have hn3 : ‖A+B+C‖ ≤ ‖A‖+‖B‖+‖C‖ := norm_add₃_le
      have hNorm : ‖A+B+C+D‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖ :=
        (norm_add_le (A+B+C) D).trans (add_le_add hn3 le_rfl)
      exact hNorm.trans (by nlinarith [ha,hb,hc,hd])
    · rw [timeD_spatial_mul,abs_mul,timeD_cylinder_change_space u hp.1 hpLocal.1]
      exact (mul_le_mul hφ0 hut (abs_nonneg _) hE).trans (by nlinarith [mul_nonneg hE hK])
  · obtain ⟨h0,h1,h2,ht⟩ := spatial_cutoff_jets_zero_of_notMem_tsupport (cylinder S l r) φ u hpSupport
    change φ p.1*u p = 0 at h0
    have hPos : 0 ≤ 4*E*K := by positivity
    simpa only [h0,h1,h2,ht,norm_zero,abs_zero] using And.intro hPos (And.intro hPos (And.intro hPos hPos))

/-- For a fixed genuine chart and smooth compact cutoff, the original data
    Schauder budget supplies a one-sided low-jet Holder budget with a constant
    chosen before the data. No lower-jet Holder input is used. -/
theorem chart_cutoff_lowPair_holder {n : ℕ} {α T C : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hC : 0 ≤ C)
    {e : Space n} (he : ‖e‖ = 1) {X V : Set (Space n)} (hV : IsOpen V)
    {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V)
    (hMap : MapsTo ψ ({x | 0 ≤ inner ℝ e x}∩V) X)
    (hChart : ∀ x ∈ {x | 0 ≤ inner ℝ e x}∩V,
      ‖fderiv ℝ ψ x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ C)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hSupport : tsupport φ ⊆ V) :
    ∃ A : ℝ, 0 < A ∧ ∀ (u : Point n → ℝ) P,
      SchauderBound α (cylinder X 0 T) u P →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
        (fun p => (φ p.1*u (ψ p.1,p.2),spatialD (fun q => φ q.1*u (ψ q.1,q.2)) p)) (A*P) := by
  obtain ⟨E,hE,hφBound⟩ := compact_cutoff_actual_jet_bound hφ hcφ
  refine ⟨32000*E*(1+C)^2,by positivity,?_⟩
  intro u P hu
  let v := chartSpaceTimePullback ψ u
  let K := (1+C)^2*P
  have hP : 0 ≤ P := hu.2.1
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hP
  have hCoeff0 : 1 ≤ (1+C)^2 := by nlinarith [sq_nonneg C]
  have hCoeff1 : C ≤ (1+C)^2 := by nlinarith [sq_nonneg C]
  have hCoeff2 : C^2+C ≤ (1+C)^2 := by nlinarith
  have hv : C2 (cylinder ({x | 0 ≤ inner ℝ e x}∩V) 0 T) v :=
    c2_chartSpaceTimePullback hV inter_subset_right hψ hMap hu.1
  have hRaw : ∀ p ∈ cylinder ({x | 0 ≤ inner ℝ e x}∩V) 0 T,
      |v p| ≤ K ∧ ‖spatialD v p‖ ≤ K ∧ ‖spatialDD v p‖ ≤ K ∧
        |timeD (cylinder ({x | 0 ≤ inner ℝ e x}∩V) 0 T) v p| ≤ K := by
    intro p hp
    obtain ⟨h0,h1,h2,ht⟩ := schauder_chart_raw_jet_bound hV inter_subset_right hψ hMap hChart hu hp
    have hPK : P ≤ K := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCoeff0 hP
    exact ⟨h0.trans hPK,h1.trans (mul_le_mul_of_nonneg_right hCoeff1 hP),
      h2.trans (mul_le_mul_of_nonneg_right hCoeff2 hP),ht.trans hPK⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hw : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => φ p.1*v p) :=
    c2_spatial_cutoff_relative_extension hV hφ2 hSupport hv
  have hwBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      |φ p.1*v p| ≤ 4*E*K ∧ ‖spatialD (fun p => φ p.1*v p) p‖ ≤ 4*E*K ∧
      ‖spatialDD (fun p => φ p.1*v p) p‖ ≤ 4*E*K ∧
      |timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => φ p.1*v p) p| ≤ 4*E*K :=
    fun p hp => cutoff_relative_raw_jet_bound hE.le hK hφ2 hSupport hφBound hv hRaw hp
  have hh := c2_halfSpace_lowPair_holder hα hα1 hT (by positivity : 0 ≤ 4*E*K) he hw hwBound
  change HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
    (fun p => (φ p.1*v p,spatialD (fun q => φ q.1*v q) p)) ((32000*E*(1+C)^2)*P)
  have hBudget : (32000*E*(1+C)^2)*P = 8000*(4*E*K) := by
    dsimp only [K]
    ring
  rw [hBudget]
  exact hh

end Yau.LeafProofs.L16Aux
