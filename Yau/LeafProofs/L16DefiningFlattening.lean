import Yau.LeafProofs.L16HalfSpaceHeatSolver
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- Finite-order inverse charts obtained from the real inverse function theorem
    can be buffered so that both directions are genuinely C³ throughout them. -/
theorem local_smooth_inverse_chart {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {x : E} {L : E ≃L[ℝ] G}
    (hf : ContDiffAt ℝ 4 f x) (hD : HasFDerivAt f (L : E →L[ℝ] G) x)
    {V : Set E} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ c : OpenPartialHomeomorph E G, x ∈ c.source ∧ c.source ⊆ V ∧
      (c : E → G) = f ∧ ContDiffOn ℝ 3 c c.source ∧ ContDiffOn ℝ 3 c.symm c.target := by
  let c0 := hf.toOpenPartialHomeomorph f hD (by norm_num)
  have hx0 : x ∈ c0.source := hf.mem_toOpenPartialHomeomorph_source hD (by norm_num)
  have hInv : ContDiffAt ℝ 4 c0.symm (f x) := hf.to_localInverse hD (by norm_num)
  obtain ⟨W,hWo,hxW,hW⟩ := (hf : ContDiffWithinAt ℝ 4 f univ x).contDiffOn' (m := 3) (by norm_num) (by norm_num)
  obtain ⟨Z,hZo,hxZ,hZ⟩ := (hInv : ContDiffWithinAt ℝ 4 c0.symm univ (f x)).contDiffOn' (m := 3) (by norm_num) (by norm_num)
  have hW' : ContDiffOn ℝ 3 f W := by simpa using hW
  have hZ' : ContDiffOn ℝ 3 c0.symm Z := by simpa using hZ
  let c1 := c0.restrOpen (V∩W) (hV.inter hWo)
  let c := (c1.symm.restrOpen Z hZo).symm
  have hxs : x ∈ c.source := by
    change x ∈ c1.source ∩ c1 ⁻¹' Z
    exact ⟨⟨hx0,hxV,hxW⟩,hxZ⟩
  have hsV : c.source ⊆ V := fun y hy => hy.1.2.1
  have hsW : c.source ⊆ W := fun y hy => hy.1.2.2
  have htZ : c.target ⊆ Z := fun y hy => hy.2
  refine ⟨c,hxs,hsV,rfl,?_,?_⟩
  · exact hW'.mono hsW
  · exact hZ'.mono htZ

/-- A defining function is straightened by an explicit map whose derivative at
    the base point is the identity. -/
def definingFlatten {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) (ρ : E → ℝ) (y : E) : E :=
  (y-x)+(ρ y-fderiv ℝ ρ x (y-x)) • v

/-- The normal scalar coordinate of the explicit flattening is exactly the
    original defining function, throughout its domain of definition. -/
theorem definingFlatten_level {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) (ρ : E → ℝ) (hv : fderiv ℝ ρ x v = 1) (y : E) :
    fderiv ℝ ρ x (definingFlatten x v ρ y) = ρ y := by
  simp only [definingFlatten,map_add,map_smul,hv,smul_eq_mul,mul_one]
  ring

theorem definingFlatten_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) {ρ : E → ℝ} (hρ : DifferentiableAt ℝ ρ x) :
    HasFDerivAt (definingFlatten x v ρ) (ContinuousLinearMap.id ℝ E) x := by
  change HasFDerivAt (fun y : E => (y-x)+(ρ y-fderiv ℝ ρ x (y-x)) • v)
    (ContinuousLinearMap.id ℝ E) x
  have hShift : HasFDerivAt (fun y : E => y-x) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const x
  have hLinear := (fderiv ℝ ρ x).hasFDerivAt.comp x hShift
  have h := hShift.add ((hρ.hasFDerivAt.sub hLinear).smul_const v)
  simpa only [Pi.add_def,Pi.add_apply,Pi.sub_apply,Function.comp_def,
    ContinuousLinearMap.comp_id,sub_self,ContinuousLinearMap.zero_smulRight,add_zero] using h

/-- An actual noncritical C⁴ defining function admits a buffered C³ local
    diffeomorphism with the exact original scalar level coordinate. -/
theorem defining_function_local_flattening {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ρ : E → ℝ} {x : E} (hρ : ContDiffAt ℝ 4 ρ x)
    (hρx : ρ x = 0) (hD : fderiv ℝ ρ x ≠ 0) {V : Set E} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ (v : E) (c : OpenPartialHomeomorph E E), fderiv ℝ ρ x v = 1 ∧
      x ∈ c.source ∧ c.source ⊆ V ∧ c x = 0 ∧
      ContDiffOn ℝ 3 c c.source ∧ ContDiffOn ℝ 3 c.symm c.target ∧
      ∀ y, fderiv ℝ ρ x (c y) = ρ y := by
  have hNonzero : ∃ w, fderiv ℝ ρ x w ≠ 0 := by
    by_contra! hh
    apply hD
    ext w
    exact hh w
  obtain ⟨w,hw⟩ := hNonzero
  let v := (fderiv ℝ ρ x w)⁻¹ • w
  have hv : fderiv ℝ ρ x v = 1 := by simp only [v,map_smul,smul_eq_mul,inv_mul_cancel₀ hw]
  have hShift : ContDiffAt ℝ 4 (fun y : E => y-x) x := by fun_prop
  have hPhi : ContDiffAt ℝ 4 (definingFlatten x v ρ) x :=
    hShift.add ((hρ.sub ((fderiv ℝ ρ x).contDiff.contDiffAt.comp x hShift)).smul contDiffAt_const)
  obtain ⟨c,hxc,hcV,hcf,hc,hci⟩ := local_smooth_inverse_chart hPhi
    (L := ContinuousLinearEquiv.refl ℝ E) (definingFlatten_hasFDerivAt x v (hρ.differentiableAt (by norm_num))) hV hxV
  refine ⟨v,c,hv,hxc,hcV,?_,hc,hci,?_⟩
  · rw [hcf]
    simp only [definingFlatten,sub_self,hρx,map_zero,zero_smul,add_zero]
  · intro y
    rw [hcf]
    exact definingFlatten_level x v ρ hv y

/-- Every nonzero real covector is a strictly positive multiple of the
    inward unit normal functional. -/
theorem nonzero_covector_inward_unit_normal {n : ℕ} (L : Space n →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ (e : Space n) (κ : ℝ), ‖e‖ = 1 ∧ 0 < κ ∧ ∀ y, inner ℝ e y = -κ*L y := by
  let g := (InnerProductSpace.toDual ℝ (Space n)).symm L
  have hg : g ≠ 0 := by
    intro hh
    apply hL
    have ht := (InnerProductSpace.toDual ℝ (Space n)).apply_symm_apply L
    change InnerProductSpace.toDual ℝ (Space n) g = L at ht
    rw [hh,map_zero] at ht
    exact ht.symm
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  let e := -(‖g‖⁻¹ • g)
  refine ⟨e,‖g‖⁻¹,?_,inv_pos.mpr hn,?_⟩
  · simp only [e,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · intro y
    simp only [e,inner_neg_left,real_inner_smul_left,neg_mul]
    dsimp only [g]
    rw [InnerProductSpace.toDual_symm_apply]

/-- The actual defining-function hypothesis of SmoothDomain gives a genuine
    buffered C³ chart carrying the domain to the positive unit-normal half space. -/
theorem smoothDomain_boundary_flat_chart {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O)
    {x : Space n} (hx : x ∈ frontier O) :
    ∃ (e : Space n) (c : OpenPartialHomeomorph (Space n) (Space n)),
      ‖e‖ = 1 ∧ x ∈ c.source ∧ c x = 0 ∧
      ContDiffOn ℝ 3 c c.source ∧ ContDiffOn ℝ 3 c.symm c.target ∧
      ∀ y ∈ c.source, y ∈ O ↔ 0 < inner ℝ e (c y) := by
  obtain ⟨V,ρ,hV,hxV,hρ,hρx,hD,hSet⟩ := hO.2.2.2 x hx
  have hρAt : ContDiffAt ℝ 4 ρ x :=
    (hρ.contDiffAt (hV.mem_nhds hxV)).of_le (by norm_num)
  obtain ⟨v,c,hv,hxc,hcV,hcx,hc,hci,hLevel⟩ :=
    defining_function_local_flattening hρAt hρx hD hV hxV
  obtain ⟨e,κ,he,hκ,hNormal⟩ := nonzero_covector_inward_unit_normal (fderiv ℝ ρ x) hD
  refine ⟨e,c,he,hxc,hcx,hc,hci,?_⟩
  intro y hy
  have hDomain : y ∈ O ↔ ρ y < 0 := by
    have hyV := hcV hy
    constructor
    · intro hyO
      have hh : y ∈ O∩V := ⟨hyO,hyV⟩
      rw [hSet] at hh
      exact hh.2
    · intro hh
      have hh' : y ∈ {y | y∈V ∧ ρ y<0} := ⟨hyV,hh⟩
      rw [← hSet] at hh'
      exact hh'.1
  rw [hDomain,hNormal,hLevel,neg_mul,neg_pos]
  constructor
  · exact mul_neg_of_pos_of_neg hκ
  · intro hh
    by_contra! hh'
    exact (not_lt_of_ge (mul_nonneg hκ.le hh')) hh

/-- The positive unit-normal half space has precisely the expected closed face. -/
theorem unitNormal_halfSpace_closure {n : ℕ} {e : Space n} (he : ‖e‖ = 1) :
    closure {y : Space n | 0 < inner ℝ e y} = {y | 0 ≤ inner ℝ e y} := by
  have hs : Function.Surjective (innerSL ℝ e : Space n →L[ℝ] ℝ) := by
    intro r
    refine ⟨r • e,?_⟩
    simp [he]
  have h := ((innerSL ℝ e).isOpenMap hs).preimage_closure_eq_closure_preimage
    (innerSL ℝ e).continuous (Ioi 0)
  simpa only [closure_Ioi,preimage,mem_Ioi,mem_Ici,innerSL_apply_apply] using h.symm

/-- The actual frontier of the positive unit-normal half space is its zero plane. -/
theorem unitNormal_halfSpace_frontier {n : ℕ} {e : Space n} (he : ‖e‖ = 1) :
    frontier {y : Space n | 0 < inner ℝ e y} = {y | inner ℝ e y = 0} := by
  have ho : IsOpen {y : Space n | 0 < inner ℝ e y} := isOpen_lt continuous_const (innerSL ℝ e).continuous
  rw [frontier,unitNormal_halfSpace_closure he,ho.interior_eq]
  ext y
  simp only [Set.mem_sdiff,mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => by simp [h]⟩

/-- The defining-function chart transports the domain, its actual closure,
    and its actual frontier to the corresponding three half-space faces. -/
theorem smoothDomain_boundary_closed_flat_chart {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O)
    {x : Space n} (hx : x ∈ frontier O) :
    ∃ (e : Space n) (c : OpenPartialHomeomorph (Space n) (Space n)),
      ‖e‖ = 1 ∧ x ∈ c.source ∧ c x = 0 ∧
      ContDiffOn ℝ 3 c c.source ∧ ContDiffOn ℝ 3 c.symm c.target ∧
      ∀ y ∈ c.source,
        (y ∈ O ↔ 0 < inner ℝ e (c y)) ∧
        (y ∈ closure O ↔ 0 ≤ inner ℝ e (c y)) ∧
        (y ∈ frontier O ↔ inner ℝ e (c y) = 0) := by
  obtain ⟨e,c,he,hxS,hcx,hc,hci,hInside⟩ := smoothDomain_boundary_flat_chart hO hx
  have hImage : c.IsImage O {y : Space n | 0 < inner ℝ e y} := fun y hy => (hInside y hy).symm
  refine ⟨e,c,he,hxS,hcx,hc,hci,?_⟩
  intro y hy
  refine ⟨hInside y hy,?_,?_⟩
  · simpa only [unitNormal_halfSpace_closure he,mem_ofPred_eq] using (hImage.closure.apply_mem_iff hy).symm
  · simpa only [unitNormal_halfSpace_frontier he,mem_ofPred_eq] using (hImage.frontier.apply_mem_iff hy).symm

end Yau.LeafProofs.L16Aux
