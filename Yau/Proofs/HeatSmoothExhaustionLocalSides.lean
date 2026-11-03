import spec.CHAIN.HeatConcreteBindings
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.SmoothExhaustionAux

/-- A regular zero has a preconnected negative side in the original coordinates. -/
theorem regular_negative_local_preconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : E → ℝ} {V : Set E} (hV : IsOpen V) (hρ : ContDiffOn ℝ ∞ ρ V)
    {z₀ : E} (hz₀ : z₀ ∈ V) (hzero : ρ z₀=0) (hD : fderiv ℝ ρ z₀ ≠ 0) :
    ∃ W : Set E, IsOpen W ∧ z₀ ∈ W ∧ W ⊆ V ∧
      IsPreconnected (W ∩ {z | ρ z < 0}) := by
  let L := fderiv ℝ ρ z₀
  obtain ⟨w,hw⟩ := ContinuousLinearMap.exists_ne_zero hD
  let v := (L w)⁻¹ • w
  have hLv : L v=1 := by simp only [v,map_smul,smul_eq_mul]; exact inv_mul_cancel₀ hw
  let Φ : E → E := fun z => (z-z₀)+(ρ z-L (z-z₀)) • v
  have hLΦ (z : E) : L (Φ z)=ρ z := by
    simp only [Φ,map_add,map_smul,hLv,smul_eq_mul,mul_one]
    ring
  have hΦ0 : Φ z₀=0 := by simp only [Φ,sub_self,hzero,map_zero,sub_zero,zero_smul,zero_add]
  have hρAt : ContDiffAt ℝ ∞ ρ z₀ := hρ.contDiffAt (hV.mem_nhds hz₀)
  have hshift : HasFDerivAt (fun z : E => z-z₀) (ContinuousLinearMap.id ℝ E) z₀ :=
    (hasFDerivAt_id z₀).sub_const z₀
  have H : HasFDerivAt ρ (fderiv ℝ ρ z₀) z₀ :=
    (hρAt.differentiableAt (by simp)).hasFDerivAt
  have hrem := H.sub (L.hasFDerivAt.comp z₀ hshift)
  have hΦD : HasFDerivAt Φ (ContinuousLinearMap.id ℝ E) z₀ := by
    convert hshift.add (hrem.smul_const v) using 1
    · rfl
    · simp only [ContinuousLinearMap.comp_id,L,sub_self,
        ContinuousLinearMap.zero_smulRight,add_zero]
  have hΦAt : ContDiffAt ℝ ∞ Φ z₀ :=
    (contDiffAt_id.sub contDiffAt_const).add
      ((hρAt.sub (L.contDiff.contDiffAt.comp z₀
        (contDiffAt_id.sub contDiffAt_const))).smul contDiffAt_const)
  let c₀ := hΦAt.toOpenPartialHomeomorph Φ
    (f' := ContinuousLinearEquiv.refl ℝ E) hΦD (by simp)
  let c := c₀.restrOpen V hV
  have hc0 : z₀ ∈ c.source :=
    ⟨hΦAt.mem_toOpenPartialHomeomorph_source (f' := ContinuousLinearEquiv.refl ℝ E) hΦD (by simp),hz₀⟩
  have hcΦ (z : E) : c z=Φ z := rfl
  have hczero : c z₀=0 := hΦ0
  have hct : (0 : E) ∈ c.target := hczero ▸ c.map_source hc0
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hct)
  let W := c.source ∩ c ⁻¹' Metric.ball 0 r
  let A : Set E := Metric.ball 0 r ∩ {y | L y < 0}
  have hWo : IsOpen W := c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hW0 : z₀ ∈ W := ⟨hc0,by rw [Set.mem_preimage,hczero];exact Metric.mem_ball_self hr⟩
  have hAt : A ⊆ c.target := fun y hy => hball hy.1
  have hAc : Convex ℝ A := (convex_ball (0 : E) r).inter
    ((convex_Iio (0 : ℝ)).linear_preimage L.toLinearMap)
  have heq : W ∩ {z | ρ z < 0} = c.symm '' A := by
    ext z
    constructor
    · rintro ⟨⟨hzs,hzb⟩,hzρ⟩
      refine ⟨c z,⟨hzb,?_⟩,c.left_inv hzs⟩
      change L (c z)<0
      rw [hcΦ,hLΦ]
      exact hzρ
    · rintro ⟨y,hy,rfl⟩
      have hys : c.symm y ∈ c.source := c.map_target (hAt hy)
      have hρy : ρ (c.symm y)=L y := by
        rw [← hLΦ,← hcΦ,c.right_inv (hAt hy)]
      refine ⟨⟨hys,?_⟩,?_⟩
      · change c (c.symm y) ∈ Metric.ball 0 r
        rw [c.right_inv (hAt hy)]
        exact hy.1
      · change ρ (c.symm y) < 0
        rw [hρy]
        exact hy.2
  refine ⟨W,hWo,hW0,fun z hz => hz.1.2,?_⟩
  rw [heq]
  exact hAc.isPreconnected.image c.symm (c.continuousOn_symm.mono hAt)

end Yau.Proofs.SmoothExhaustionAux
