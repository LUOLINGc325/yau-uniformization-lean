import Yau.LeafProofs.L23FieldMetricLinearODEGlobal

/-! Actual fundamental solutions on arbitrary nondegenerate compact time intervals. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 800000

theorem exists_interval_fundamental_solution
    (A : ℝ → E →L[ℝ] E) (J : Set ℝ) (hJ : IsOpen J) (hA : ContDiffOn ℝ 2 A J)
    (a b : ℝ) (hab : a < b) (hsegment : Set.Icc a b ⊆ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → E →L[ℝ] E,
      W a = ContinuousLinearMap.id ℝ E ∧ ContDiffOn ℝ 3 W (Set.Ioo (a-δ) (b+δ)) ∧
      ∀ t ∈ Set.Ioo (a-δ) (b+δ), t ∈ J ∧ HasDerivAt W ((A t).comp (W t)) t := by
  let c := b-a
  have hc : 0 < c := sub_pos.mpr hab
  let Jhat := (fun s : ℝ => a+c*s) ⁻¹' J
  have hJhat : IsOpen Jhat := hJ.preimage (by fun_prop)
  let B : ℝ → E →L[ℝ] E := fun s => c • A (a+c*s)
  have hB : ContDiffOn ℝ 2 B Jhat :=
    (hA.comp (contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id)) (fun _ hs => hs)).const_smul c
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Jhat := by
    intro s hs
    apply hsegment
    have Hlo := mul_nonneg hc.le hs.1
    have Hhi := mul_le_mul_of_nonneg_left hs.2 hc.le
    dsimp only [c] at Hlo Hhi ⊢
    constructor <;> nlinarith
  obtain ⟨ε,hε,Z,hZ₀,hZ,hsolZ⟩ := exists_unit_fundamental_solution B Jhat hJhat hB hunit
  let δ := c*ε
  have hδ : 0 < δ := mul_pos hc hε
  let W : ℝ → E →L[ℝ] E := fun t => Z ((t-a)/c)
  have hmap (t : ℝ) (ht : t ∈ Set.Ioo (a-δ) (b+δ)) : (t-a)/c ∈ Set.Ioo (-ε) (1+ε) := by
    constructor
    · apply (lt_div_iff₀ hc).mpr
      dsimp only [δ] at ht
      nlinarith [ht.1]
    · apply (div_lt_iff₀ hc).mpr
      have Hc : c = b-a := rfl
      dsimp only [δ] at ht
      nlinarith [ht.2]
  have htime (t : ℝ) : a+c*((t-a)/c) = t := by field_simp [hc.ne']; ring
  refine ⟨δ,hδ,W,?_,hZ.comp (contDiffOn_id.sub contDiffOn_const |>.div_const c) hmap,?_⟩
  · simpa only [W,sub_self,zero_div] using hZ₀
  · intro t ht
    have HZ := hsolZ ((t-a)/c) (hmap t ht)
    have hJt : t ∈ J := by
      have H : a+c*((t-a)/c) ∈ J := HZ.1
      rwa [htime t] at H
    refine ⟨hJt,?_⟩
    have HD := HZ.2.scomp t (((hasDerivAt_id t).sub_const a).div_const c)
    change HasDerivAt W ((1/c) • ((c • A (a+c*((t-a)/c))).comp (W t))) t at HD
    rw [htime t] at HD
    convert! HD using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,smul_smul]
    rw [div_mul_cancel₀ 1 hc.ne']
    simp

theorem exists_interval_linear_solution
    (A : ℝ → E →L[ℝ] E) (J : Set ℝ) (hJ : IsOpen J) (hA : ContDiffOn ℝ 2 A J)
    (a b : ℝ) (hab : a < b) (hsegment : Set.Icc a b ⊆ J) (C : E →L[ℝ] E) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → E →L[ℝ] E,
      W a = C ∧ ContDiffOn ℝ 3 W (Set.Ioo (a-δ) (b+δ)) ∧
      ∀ t ∈ Set.Ioo (a-δ) (b+δ), t ∈ J ∧ HasDerivAt W ((A t).comp (W t)) t := by
  obtain ⟨δ,hδ,Z,hZ₀,hZ,hsolZ⟩ := exists_interval_fundamental_solution A J hJ hA a b hab hsegment
  let W : ℝ → E →L[ℝ] E := fun t => (Z t).comp C
  refine ⟨δ,hδ,W,?_,hZ.clm_comp contDiffOn_const,?_⟩
  · simp only [W,hZ₀,ContinuousLinearMap.id_comp]
  · intro t ht
    refine ⟨(hsolZ t ht).1,?_⟩
    have H := ((hsolZ t ht).2).clm_comp (hasDerivAt_const t C)
    simpa only [ContinuousLinearMap.comp_zero,add_zero,ContinuousLinearMap.comp_assoc] using H

end Yau.LeafProofs.L23Aux
