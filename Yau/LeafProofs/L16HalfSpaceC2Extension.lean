import Yau.Blueprint.ParabolicSpaces
import Mathlib.Analysis.Calculus.FDeriv.Extend

open Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- The normal sampling map of the second order reflection formula. -/
def normalSample {n : ℕ} (e : Space n) (j : ℝ) (x : Space n) : Space n :=
  x - ((j + 1) * inner ℝ e x) • e

def normalSampleL {n : ℕ} (e : Space n) (j : ℝ) : Space n →L[ℝ] Space n :=
  ContinuousLinearMap.id ℝ _ - (j + 1) • (innerSL ℝ e).smulRight e

@[simp] theorem normalSampleL_apply {n : ℕ} (e : Space n) (j : ℝ) (x : Space n) :
    normalSampleL e j x = normalSample e j x := by
  simp [normalSampleL, normalSample, mul_smul]

@[simp] theorem normalSample_normal {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (j : ℝ) (x : Space n) : inner ℝ e (normalSample e j x) = -j * inner ℝ e x := by
  simp only [normalSample, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he]
  ring

@[simp] theorem normalSample_boundary {n : ℕ} (e : Space n) (j : ℝ)
    {x : Space n} (hx : inner ℝ e x = 0) : normalSample e j x = x := by
  simp [normalSample, hx]

/-- Literal three point reflection, preserving derivatives through order two. -/
def halfSpaceSecondOrderExtension {n : ℕ} (e : Space n) (v : Point n → ℝ) : Point n → ℝ :=
  fun p => if 0 ≤ inner ℝ e p.1 then v p else
    6 * v (normalSample e 1 p.1, p.2) - 8 * v (normalSample e 2 p.1, p.2) +
      3 * v (normalSample e 3 p.1, p.2)

private def halfGlue {n : ℕ} {F : Type*} (e : Space n) (f g : Point n → F) : Point n → F :=
  fun p => if 0 ≤ inner ℝ e p.1 then f p else g p

private theorem halfGlue_pos {n : ℕ} {F : Type*} (e : Space n) (f g : Point n → F)
    {p : Point n} (hp : 0 ≤ inner ℝ e p.1) : halfGlue e f g p = f p := ite_eq_left hp

private theorem halfGlue_neg {n : ℕ} {F : Type*} (e : Space n) (f g : Point n → F)
    (hfg : ∀ p, inner ℝ e p.1 = 0 → f p = g p)
    {p : Point n} (hp : inner ℝ e p.1 ≤ 0) : halfGlue e f g p = g p := by
  by_cases h : 0 ≤ inner ℝ e p.1
  · rw [halfGlue_pos e f g h, hfg p (le_antisymm hp h)]
  · exact ite_eq_right h

private theorem halfGlue_continuousOn {n : ℕ} {F : Type*} [TopologicalSpace F]
    (e : Space n) {T : ℝ} (f g : Point n → F)
    (hfg : ∀ p, inner ℝ e p.1 = 0 → f p = g p)
    (hf : ContinuousOn f (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hg : ContinuousOn g (cylinder {x | inner ℝ e x ≤ 0} 0 T)) :
    ContinuousOn (halfGlue e f g) (cylinder univ 0 T) := by
  have h₁ : ContinuousOn (halfGlue e f g) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) :=
    hf.congr fun p hp => halfGlue_pos e f g hp.1
  have h₂ : ContinuousOn (halfGlue e f g) (cylinder {x | inner ℝ e x ≤ 0} 0 T) :=
    hg.congr fun p hp => halfGlue_neg e f g hfg hp.1
  have hclosed₁ : IsClosed (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) :=
    (isClosed_le continuous_const (innerSL ℝ e).continuous).prod isClosed_Icc
  have hclosed₂ : IsClosed (cylinder {x : Space n | inner ℝ e x ≤ 0} 0 T) :=
    (isClosed_le (innerSL ℝ e).continuous continuous_const).prod isClosed_Icc
  have hu : cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T ∪
      cylinder {x : Space n | inner ℝ e x ≤ 0} 0 T = cylinder univ 0 T := by
    ext p
    simp only [cylinder, mem_union, mem_prod, mem_ofPred_eq, mem_univ, true_and]
    constructor
    · rintro (h | h) <;> exact h.2
    · intro h
      rcases le_total 0 (inner ℝ e p.1) with h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr ⟨h', h⟩
  simpa only [hu] using h₁.union_of_isClosed h₂ hclosed₁ hclosed₂

private theorem halfGlue_hasFDerivAt {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : Space n) (f g : Point n → F)
    (A B : Point n → Space n →L[ℝ] F)
    (hfg : ∀ p, inner ℝ e p.1 = 0 → f p = g p)
    (hAB : ∀ p, inner ℝ e p.1 = 0 → A p = B p)
    {p : Point n}
    (hf : 0 ≤ inner ℝ e p.1 → HasFDerivWithinAt (fun x => f (x,p.2)) (A p)
      {x | 0 ≤ inner ℝ e x} p.1)
    (hg : inner ℝ e p.1 ≤ 0 → HasFDerivWithinAt (fun x => g (x,p.2)) (B p)
      {x | inner ℝ e x ≤ 0} p.1) :
    HasFDerivAt (fun x => halfGlue e f g (x,p.2)) (halfGlue e A B p) p.1 := by
  have hclosed₁ : IsClosed {x : Space n | 0 ≤ inner ℝ e x} :=
    isClosed_le continuous_const (innerSL ℝ e).continuous
  have hclosed₂ : IsClosed {x : Space n | inner ℝ e x ≤ 0} :=
    isClosed_le (innerSL ℝ e).continuous continuous_const
  have h₁ : HasFDerivWithinAt (fun x => halfGlue e f g (x,p.2)) (halfGlue e A B p)
      {x | 0 ≤ inner ℝ e x} p.1 := by
    by_cases hp : 0 ≤ inner ℝ e p.1
    · rw [halfGlue_pos e A B hp]
      exact (hf hp).congr (fun x hx => halfGlue_pos e f g hx) (halfGlue_pos e f g hp)
    · exact .of_notMem_closure (by simpa only [hclosed₁.closure_eq, mem_ofPred_eq] using hp)
  have h₂ : HasFDerivWithinAt (fun x => halfGlue e f g (x,p.2)) (halfGlue e A B p)
      {x | inner ℝ e x ≤ 0} p.1 := by
    by_cases hp : inner ℝ e p.1 ≤ 0
    · rw [halfGlue_neg e A B hAB hp]
      exact (hg hp).congr (fun x hx => halfGlue_neg e f g hfg hx) (halfGlue_neg e f g hfg hp)
    · exact .of_notMem_closure (by simpa only [hclosed₂.closure_eq, mem_ofPred_eq] using hp)
  have hu : {x : Space n | 0 ≤ inner ℝ e x} ∪ {x | inner ℝ e x ≤ 0} = univ := by
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total _ _
  exact hasFDerivWithinAt_univ.mp (hu ▸ h₁.union h₂)

private theorem closure_positiveHalfSpace {n : ℕ} {e : Space n} (he : ‖e‖ = 1) :
    closure {x : Space n | 0 < inner ℝ e x} = {x | 0 ≤ inner ℝ e x} := by
  have hsurj : Function.Surjective (innerSL ℝ e : Space n →L[ℝ] ℝ) := by
    intro r
    refine ⟨r • e, ?_⟩
    simp [he]
  have h := ((innerSL ℝ e).isOpenMap hsurj).preimage_closure_eq_closure_preimage
    (innerSL ℝ e).continuous (Ioi 0)
  simpa only [closure_Ioi, preimage, mem_Ioi, mem_Ici, innerSL_apply_apply] using h.symm

/-- Continuous genuine interior jets determine the spatial jets on the closed halfspace. -/
theorem halfSpace_hasFDerivWithinAt_of_interior {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {e : Space n} (he : ‖e‖ = 1)
    {f : Space n → F} {A : Space n → Space n →L[ℝ] F}
    (hf : ContinuousOn f {x | 0 ≤ inner ℝ e x})
    (hA : ContinuousOn A {x | 0 ≤ inner ℝ e x})
    (hd : ∀ x, 0 < inner ℝ e x → HasFDerivAt f (A x) x)
    {x : Space n} (hx : 0 ≤ inner ℝ e x) :
    HasFDerivWithinAt f (A x) {x | 0 ≤ inner ℝ e x} x := by
  have hsub : {x : Space n | 0 < inner ℝ e x} ⊆ {x | 0 ≤ inner ℝ e x} :=
    fun y h => (show 0 < inner ℝ e y from h).le
  rw [← closure_positiveHalfSpace he]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv (s := {y : Space n | 0 < inner ℝ e y})
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (convex_halfSpace_gt (innerSL ℝ e).toLinearMap.isLinear 0)
    (isOpen_lt continuous_const (innerSL ℝ e).continuous)
  · intro y hy
    rw [closure_positiveHalfSpace he] at hy
    exact (hf y hy).mono hsub
  · apply ((hA x hx).mono hsub).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).fderiv.symm


private def samplePoint {n : ℕ} (e : Space n) (j : ℝ) (p : Point n) : Point n :=
  (normalSample e j p.1, p.2)

private theorem samplePoint_continuous {n : ℕ} (e : Space n) (j : ℝ) :
    Continuous (samplePoint e j) := by
  change Continuous (fun p : Point n => (normalSample e j p.1, p.2))
  simpa only [Function.comp_def, normalSampleL_apply] using
    ((normalSampleL e j).continuous.comp continuous_fst).prodMk continuous_snd

private theorem samplePoint_mapsTo {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T j : ℝ} (hj : 0 ≤ j) :
    MapsTo (samplePoint e j) (cylinder {x | inner ℝ e x ≤ 0} 0 T)
      (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  intro p hp
  refine ⟨?_, hp.2⟩
  change 0 ≤ inner ℝ e (normalSample e j p.1)
  rw [normalSample_normal he]
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) hp.1

private def reflectedValue {n : ℕ} {F : Type*} [AddCommGroup F] [Module ℝ F]
    (e : Space n) (f : Point n → F) (p : Point n) : F :=
  (6 : ℝ) • f (samplePoint e 1 p) - (8 : ℝ) • f (samplePoint e 2 p) +
    (3 : ℝ) • f (samplePoint e 3 p)

private def reflectedD {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Space n) (A : Point n → Space n →L[ℝ] F) (p : Point n) : Space n →L[ℝ] F :=
  (6 : ℝ) • (A (samplePoint e 1 p)).comp (normalSampleL e 1) -
    (8 : ℝ) • (A (samplePoint e 2 p)).comp (normalSampleL e 2) +
    (3 : ℝ) • (A (samplePoint e 3 p)).comp (normalSampleL e 3)

private def reflectedDD {n : ℕ} (e : Space n)
    (B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) (p : Point n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  (6 : ℝ) • ((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip
      (normalSampleL e 1)).comp ((B (samplePoint e 1 p)).comp (normalSampleL e 1)) -
  (8 : ℝ) • ((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip
      (normalSampleL e 2)).comp ((B (samplePoint e 2 p)).comp (normalSampleL e 2)) +
  (3 : ℝ) • ((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip
      (normalSampleL e 3)).comp ((B (samplePoint e 3 p)).comp (normalSampleL e 3))

private theorem reflectedValue_boundary {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : Space n) (f : Point n → F) (p : Point n)
    (hp : inner ℝ e p.1 = 0) : f p = reflectedValue e f p := by
  simp only [reflectedValue, samplePoint, normalSample_boundary e _ hp, Prod.eta]
  module

private theorem reflectedD_boundary {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : Space n) (A : Point n → Space n →L[ℝ] F) (p : Point n)
    (hp : inner ℝ e p.1 = 0) : A p = reflectedD e A p := by
  ext z
  simp only [reflectedD, samplePoint, normalSample, hp, mul_zero, zero_smul, sub_zero, Prod.eta]
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.comp_apply, normalSampleL_apply,
    normalSample, map_sub, map_smul]
  module

private theorem reflectedDD_boundary {n : ℕ} (e : Space n)
    (B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) (p : Point n)
    (hp : inner ℝ e p.1 = 0) : B p = reflectedDD e B p := by
  ext z w
  simp only [reflectedDD, samplePoint, normalSample, hp, mul_zero, zero_smul, sub_zero, Prod.eta]
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, normalSampleL_apply,
    normalSample, map_sub, map_smul, smul_eq_mul]
  ring

private theorem reflectedValue_continuousOn {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {e : Space n} (he : ‖e‖ = 1) {T : ℝ} {f : Point n → F}
    (hf : ContinuousOn f (cylinder {x | 0 ≤ inner ℝ e x} 0 T)) :
    ContinuousOn (reflectedValue e f) (cylinder {x | inner ℝ e x ≤ 0} 0 T) := by
  have h (j : ℝ) (hj : 0 ≤ j) := hf.comp (samplePoint_continuous e j).continuousOn
    (samplePoint_mapsTo he hj)
  exact ((h 1 (by norm_num)).const_smul (6 : ℝ) |>.sub ((h 2 (by norm_num)).const_smul (8 : ℝ))).add
    ((h 3 (by norm_num)).const_smul (3 : ℝ))

private theorem reflectedD_continuousOn {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {e : Space n} (he : ‖e‖ = 1) {T : ℝ}
    {A : Point n → Space n →L[ℝ] F}
    (hA : ContinuousOn A (cylinder {x | 0 ≤ inner ℝ e x} 0 T)) :
    ContinuousOn (reflectedD e A) (cylinder {x | inner ℝ e x ≤ 0} 0 T) := by
  have h (j : ℝ) (hj : 0 ≤ j) := (hA.comp (samplePoint_continuous e j).continuousOn
    (samplePoint_mapsTo he hj)).clm_comp (continuousOn_const (c := normalSampleL e j))
  exact ((h 1 (by norm_num)).const_smul (6 : ℝ) |>.sub ((h 2 (by norm_num)).const_smul (8 : ℝ))).add
    ((h 3 (by norm_num)).const_smul (3 : ℝ))

private theorem reflectedDD_continuousOn {n : ℕ} {e : Space n} (he : ‖e‖ = 1) {T : ℝ}
    {B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hB : ContinuousOn B (cylinder {x | 0 ≤ inner ℝ e x} 0 T)) :
    ContinuousOn (reflectedDD e B) (cylinder {x | inner ℝ e x ≤ 0} 0 T) := by
  have h (j : ℝ) (hj : 0 ≤ j) :=
    (continuousOn_const (c := (ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip
      (normalSampleL e j))).clm_comp
      ((hB.comp (samplePoint_continuous e j).continuousOn (samplePoint_mapsTo he hj)).clm_comp
        (continuousOn_const (c := normalSampleL e j)))
  exact ((h 1 (by norm_num)).const_smul (6 : ℝ) |>.sub ((h 2 (by norm_num)).const_smul (8 : ℝ))).add
    ((h 3 (by norm_num)).const_smul (3 : ℝ))


private theorem reflectedValue_hasFDerivWithinAt {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {e : Space n} (he : ‖e‖ = 1)
    (f : Point n → F) (A : Point n → Space n →L[ℝ] F) {p : Point n}
    (hp : inner ℝ e p.1 ≤ 0)
    (hd : ∀ x, 0 ≤ inner ℝ e x → HasFDerivWithinAt (fun y => f (y,p.2)) (A (x,p.2))
      {y | 0 ≤ inner ℝ e y} x) :
    HasFDerivWithinAt (fun x => reflectedValue e f (x,p.2)) (reflectedD e A p)
      {x | inner ℝ e x ≤ 0} p.1 := by
  have h (j : ℝ) (hj : 0 ≤ j) :
      HasFDerivWithinAt (fun x => f (normalSample e j x,p.2))
        ((A (samplePoint e j p)).comp (normalSampleL e j))
        {x | inner ℝ e x ≤ 0} p.1 := by
    have hm : MapsTo (normalSampleL e j) {x : Space n | inner ℝ e x ≤ 0}
        {x | 0 ≤ inner ℝ e x} := by
      intro x hx
      simp only [mem_ofPred_eq, normalSampleL_apply, normalSample_normal he]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) hx
    change HasFDerivWithinAt _ ((A (normalSample e j p.1,p.2)).comp (normalSampleL e j)) _ _
    simpa only [Function.comp_def, normalSampleL_apply] using
      (hd (normalSampleL e j p.1) (hm hp)).comp p.1
        (normalSampleL e j).hasFDerivWithinAt hm
  exact ((h 1 (by norm_num)).const_smul (6 : ℝ) |>.sub
    ((h 2 (by norm_num)).const_smul (8 : ℝ))).add
      ((h 3 (by norm_num)).const_smul (3 : ℝ))

private theorem reflectedD_hasFDerivWithinAt {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (A : Point n → Space n →L[ℝ] ℝ)
    (B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) {p : Point n}
    (hp : inner ℝ e p.1 ≤ 0)
    (hd : ∀ x, 0 ≤ inner ℝ e x → HasFDerivWithinAt (fun y => A (y,p.2)) (B (x,p.2))
      {y | 0 ≤ inner ℝ e y} x) :
    HasFDerivWithinAt (fun x => reflectedD e A (x,p.2)) (reflectedDD e B p)
      {x | inner ℝ e x ≤ 0} p.1 := by
  have h (j : ℝ) (hj : 0 ≤ j) :
      HasFDerivWithinAt (fun x => (A (normalSample e j x,p.2)).comp (normalSampleL e j))
        (((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip (normalSampleL e j)).comp
          ((B (samplePoint e j p)).comp (normalSampleL e j)))
        {x | inner ℝ e x ≤ 0} p.1 := by
    have hm : MapsTo (normalSampleL e j) {x : Space n | inner ℝ e x ≤ 0}
        {x | 0 ≤ inner ℝ e x} := by
      intro x hx
      simp only [mem_ofPred_eq, normalSampleL_apply, normalSample_normal he]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) hx
    change HasFDerivWithinAt _ (((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip
      (normalSampleL e j)).comp ((B (normalSample e j p.1,p.2)).comp (normalSampleL e j))) _ _
    simpa only [Function.comp_def, normalSampleL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply] using
      (((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip
        (normalSampleL e j)).hasFDerivAt.comp_hasFDerivWithinAt p.1
          ((hd (normalSampleL e j p.1) (hm hp)).comp p.1
            (normalSampleL e j).hasFDerivWithinAt hm))
  exact ((h 1 (by norm_num)).const_smul (6 : ℝ) |>.sub
    ((h 2 (by norm_num)).const_smul (8 : ℝ))).add
      ((h 3 (by norm_num)).const_smul (3 : ℝ))

private theorem continuousOn_spatialSlice {n : ℕ} {F : Type*} [TopologicalSpace F]
    {f : Point n → F} {S : Set (Space n)} {T t : ℝ}
    (hf : ContinuousOn f (cylinder S 0 T)) (ht : t ∈ Icc 0 T) :
    ContinuousOn (fun x => f (x,t)) S :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hx => ⟨hx,ht⟩)

/-- Three normal reflections extend genuine one-sided jets to ambient parabolic C².
No regularity of a proposed extension is assumed. -/
theorem halfSpaceSecondOrderExtension_jets
    {n : ℕ} {e : Space n} (he : ‖e‖ = 1) {T : ℝ} (hT : 0 < T)
    (v : Point n → ℝ)
    (J₁ : Point n → Space n →L[ℝ] ℝ)
    (J₂ : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (Jt : Point n → ℝ)
    (hv : ContinuousOn v (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hJ₁ : ContinuousOn J₁ (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hJ₂ : ContinuousOn J₂ (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hJt : ContinuousOn Jt (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => v (x,p.2)) (J₁ p) p.1)
    (hDD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => J₁ (x,p.2)) (J₂ p) p.1)
    (ht : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      HasDerivWithinAt (fun t => v (p.1,t)) (Jt p) (Icc 0 T) p.2) :
    let U := halfSpaceSecondOrderExtension e v
    C2 (cylinder univ 0 T) U ∧
      EqOn U v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialD U) J₁ (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialDD U) J₂ (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) U) Jt (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  let U := halfGlue e v (reflectedValue e v)
  let A := halfGlue e J₁ (reflectedD e J₁)
  let B := halfGlue e J₂ (reflectedDD e J₂)
  let C := halfGlue e Jt (reflectedValue e Jt)
  have hU : U = halfSpaceSecondOrderExtension e v := rfl
  have hUc : ContinuousOn U (cylinder univ 0 T) :=
    halfGlue_continuousOn e v _ (reflectedValue_boundary e v) hv (reflectedValue_continuousOn he hv)
  have hAc : ContinuousOn A (cylinder univ 0 T) :=
    halfGlue_continuousOn e J₁ _ (reflectedD_boundary e J₁) hJ₁ (reflectedD_continuousOn he hJ₁)
  have hBc : ContinuousOn B (cylinder univ 0 T) :=
    halfGlue_continuousOn e J₂ _ (reflectedDD_boundary e J₂) hJ₂ (reflectedDD_continuousOn he hJ₂)
  have hCc : ContinuousOn C (cylinder univ 0 T) :=
    halfGlue_continuousOn e Jt _ (reflectedValue_boundary e Jt) hJt (reflectedValue_continuousOn he hJt)
  have hDw (t : ℝ) (ht' : t ∈ Icc 0 T) (x : Space n) (hx : 0 ≤ inner ℝ e x) :
      HasFDerivWithinAt (fun y => v (y,t)) (J₁ (x,t)) {y | 0 ≤ inner ℝ e y} x :=
    halfSpace_hasFDerivWithinAt_of_interior he (continuousOn_spatialSlice hv ht')
      (continuousOn_spatialSlice hJ₁ ht') (fun y hy => hD (y,t) ⟨hy,ht'⟩) hx
  have hDDw (t : ℝ) (ht' : t ∈ Icc 0 T) (x : Space n) (hx : 0 ≤ inner ℝ e x) :
      HasFDerivWithinAt (fun y => J₁ (y,t)) (J₂ (x,t)) {y | 0 ≤ inner ℝ e y} x :=
    halfSpace_hasFDerivWithinAt_of_interior he (continuousOn_spatialSlice hJ₁ ht')
      (continuousOn_spatialSlice hJ₂ ht') (fun y hy => hDD (y,t) ⟨hy,ht'⟩) hx
  have hDa (p : Point n) (hp : p.2 ∈ Icc 0 T) :
      HasFDerivAt (fun x => U (x,p.2)) (A p) p.1 :=
    halfGlue_hasFDerivAt e v _ J₁ _ (reflectedValue_boundary e v) (reflectedD_boundary e J₁)
      (hDw p.2 hp p.1) (fun hn => reflectedValue_hasFDerivWithinAt he v J₁ hn (hDw p.2 hp))
  have hDDa (p : Point n) (hp : p.2 ∈ Icc 0 T) :
      HasFDerivAt (fun x => A (x,p.2)) (B p) p.1 :=
    halfGlue_hasFDerivAt e J₁ _ J₂ _ (reflectedD_boundary e J₁) (reflectedDD_boundary e J₂)
      (hDDw p.2 hp p.1) (fun hn => reflectedD_hasFDerivWithinAt he J₁ J₂ hn (hDDw p.2 hp))
  have hSD (p : Point n) (hp : p.2 ∈ Icc 0 T) : spatialD U p = A p := (hDa p hp).fderiv
  have hSDD (p : Point n) (hp : p.2 ∈ Icc 0 T) : spatialDD U p = B p := by
    have hf : (fun x => fderiv ℝ (fun y => U (y,p.2)) x) = fun x => A (x,p.2) :=
      funext fun x => hSD (x,p.2) hp
    unfold spatialDD
    rw [hf]
    exact (hDDa p hp).fderiv
  have htime (p : Point n) (hp : p.2 ∈ Icc 0 T) :
      HasDerivWithinAt (fun t => U (p.1,t)) (C p) (Icc 0 T) p.2 := by
    by_cases hn : 0 ≤ inner ℝ e p.1
    · change HasDerivWithinAt _ (halfGlue e Jt _ p) _ _
      rw [halfGlue_pos e Jt _ hn]
      exact (ht p ⟨hn,hp⟩).congr (fun t _ => halfGlue_pos e v _ hn) (halfGlue_pos e v _ hn)
    · have hnp : inner ℝ e p.1 ≤ 0 := (lt_of_not_ge hn).le
      have hs (j : ℝ) (hj : 0 ≤ j) :
          HasDerivWithinAt (fun t => v (normalSample e j p.1,t))
            (Jt (samplePoint e j p)) (Icc 0 T) p.2 :=
        ht (samplePoint e j p) (samplePoint_mapsTo he hj ⟨hnp,hp⟩)
      have hneg := ((hs 1 (by norm_num)).const_smul (6 : ℝ) |>.sub
        ((hs 2 (by norm_num)).const_smul (8 : ℝ))).add
          ((hs 3 (by norm_num)).const_smul (3 : ℝ))
      change HasDerivWithinAt _ (halfGlue e Jt _ p) _ _
      rw [halfGlue, ite_eq_right hn]
      exact hneg.congr (fun t _ => by simp only [U, halfGlue, ite_eq_right hn, reflectedValue, samplePoint]; rfl)
        (by simp only [U, halfGlue, ite_eq_right hn, reflectedValue, samplePoint]; rfl)
  have hfiber (x : Space n) : {t | (x,t) ∈ cylinder (univ : Set (Space n)) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder]
  have hTD (p : Point n) (hp : p.2 ∈ Icc 0 T) :
      timeD (cylinder univ 0 T) U p = C p := by
    unfold timeD
    rw [hfiber]
    exact (htime p hp).derivWithin (uniqueDiffOn_Icc hT p.2 hp)
  have hC2 : C2 (cylinder univ 0 T) U := by
    refine ⟨hUc, hAc.congr (fun p hp => hSD p hp.2), hBc.congr (fun p hp => hSDD p hp.2),
      hCc.congr (fun p hp => hTD p hp.2), ?_, ?_⟩
    · intro p hp
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => A (x,p.2), ⟨univ, univ_mem, fun x _ => hDa (x,p.2) hp.2⟩, ?_⟩
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => B (x,p.2), ⟨univ, univ_mem, fun x _ => hDDa (x,p.2) hp.2⟩, ?_⟩
      apply contDiffAt_zero.mpr
      exact ⟨univ, univ_mem, continuousOn_spatialSlice hBc hp.2⟩
    · intro p hp
      rw [hfiber]
      exact (htime p hp.2).differentiableWithinAt
  rw [← hU]
  refine ⟨hC2, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact halfGlue_pos e v _ hp.1
  · intro p hp
    rw [hSD p hp.2]
    exact halfGlue_pos e J₁ _ hp.1
  · intro p hp
    rw [hSDD p hp.2]
    exact halfGlue_pos e J₂ _ hp.1
  · intro p hp
    rw [hTD p hp.2]
    exact halfGlue_pos e Jt _ hp.1

end Yau.LeafProofs.L16Aux
