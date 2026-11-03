import Yau.Proofs.F05BootstrapGoodCongruence

/-! Two-sided tangential rectangles stay on the physical side and below
the original chart rim. Their parameter derivative is the actual computed
good derivative at the translated point. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_tangent_rectangle_maps {ν : Option (RIdx n)} {k : RIdx n}
    (hd : F05GoodLetter ν (some k)) {r η : ℝ} (hη : 0 ≤ η) (hMargin : r+η < 2)
    {x : Space n} (hx : x ∈ region ν r) {a : ℝ} (ha : a ∈ Icc (-η) η) :
    x+a • realVec k ∈ F05PosSpace ν := by
  have hAbs : |a| ≤ η := abs_le.mpr ha
  have hNorm : ‖x+a • realVec k‖ < 2 := by
    calc
      _ ≤ ‖x‖+‖a • realVec k‖ := norm_add_le _ _
      _ = ‖x‖+|a| := by rw [norm_smul,Real.norm_eq_abs,realVec_norm,mul_one]
      _ ≤ r+η := add_le_add hx.1 hAbs
      _ < 2 := hMargin
  refine ⟨?_,by simpa only [Metric.mem_ball,dist_zero_right] using hNorm⟩
  have hFlat : x+a • realVec k ∈ region ν 2 := by
    refine ⟨hNorm.le,?_⟩
    cases ν with
    | none => trivial
    | some j =>
      have hkj : k ≠ j := hd
      have hVec : realCoord (realVec k) j = 0 := by
        rw [← real_inner_realVec,realVec_inner,if_neg hkj]
      change realCoord (x+a • realVec k) j ≤ 0
      rw [← realCoordLinear_apply,map_add,map_smul]
      simpa only [realCoordLinear_apply,smul_eq_mul,hVec,mul_zero,add_zero] using hx.2
  exact F05_region_mem_flat hFlat

theorem F05_tangent_parameter_derivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ν : Option (RIdx n)} {k : RIdx n} {T : ℝ} {u : Point n → V}
    (hGood : F05GoodDiffOn T (some k) u (F05PosPatch ν T))
    {x : Space n} {t a : ℝ} (hPoint : (x+a • realVec k,t) ∈ F05PosPatch ν T) :
    HasDerivAt (fun s => u (x+s • realVec k,t))
      (F05GoodPartial T (some k) u (x+a • realVec k,t)) a := by
  have hDiff := hGood (x+a • realVec k,t) hPoint
  have hAffine : HasDerivAt (fun s : ℝ => s-a) 1 a := by
    simpa only [id_eq] using (hasDerivAt_id a).sub_const a
  have hComp := hDiff.hasDerivAt.scomp_of_eq a hAffine (by simp)
  have hShift (s : ℝ) : (x+a • realVec k)+(s-a) • realVec k = x+s • realVec k := by
    rw [add_assoc,← add_smul]
    congr 2
    ring
  simpa only [Function.comp_def,F05GoodPartial,hShift,one_smul] using hComp

end Yau.Proofs.F05Aux
