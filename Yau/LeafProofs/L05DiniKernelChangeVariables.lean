import Yau.LeafProofs.L05DiniKernelBudget

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem dini_square_div_hasDerivAt {c : ℝ} (hc : 0 < c) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (x/c)^2) (2*s/c^2) s := by
  have hf : HasDerivAt (fun x : ℝ => x/c) (1/c) s := by
    simpa only [id_eq] using (hasDerivAt_id s).div_const c
  have he : (1/c)*(s/c)+(s/c)*(1/c)=2*s/c^2 := by field_simp <;> ring
  have hh := hf.mul hf
  rw [he] at hh
  convert! hh using 1 <;> simp only [Pi.mul_apply,pow_two] <;> rfl

theorem dini_square_div_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun s : ℝ => (s/c)^2) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hleft : 0 ≤ x/c := div_nonneg hx.le hc.le
  have hright : x/c < y/c := div_lt_div_of_pos_right hxy hc
  simpa only [pow_two] using mul_self_lt_mul_self hleft hright

theorem dini_square_div_recent_image {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (fun s : ℝ => (s/c)^2) '' Set.Ioc 0 (c*R)=Set.Ioc 0 (R^2) := by
  ext a
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hs0 : 0 < s/c := div_pos hs.1 hc
    have hsR : s/c ≤ R := (div_le_iff₀ hc).mpr (by nlinarith only [hs.2])
    exact ⟨sq_pos_of_pos hs0,by nlinarith only [mul_self_le_mul_self hs0.le hsR]⟩
  · intro ha
    refine ⟨c*Real.sqrt a,?_,?_⟩
    · refine ⟨mul_pos hc (Real.sqrt_pos.mpr ha.1),?_⟩
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR.le,ha.2⟩) hc.le
    · have he : c*Real.sqrt a/c=Real.sqrt a := by field_simp
      change (c*Real.sqrt a/c)^2=a
      rw [he,Real.sq_sqrt ha.1.le]

theorem dini_square_div_old_image {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (fun s : ℝ => (s/c)^2) '' Set.Ioi (c*R)=Set.Ioi (R^2) := by
  ext a
  constructor
  · rintro ⟨s,hs,rfl⟩
    change c*R < s at hs
    have hsR : R < s/c := (lt_div_iff₀ hc).mpr (by nlinarith only [hs])
    change R^2 < (s/c)^2
    exact by nlinarith only [mul_self_lt_mul_self hR.le hsR]
  · intro ha
    change R^2 < a at ha
    have ha0 : 0 < a := (sq_nonneg R).trans_lt ha
    have hsR : R < Real.sqrt a := by
      nlinarith only [ha,Real.sq_sqrt ha0.le,Real.sqrt_nonneg a,hR]
    refine ⟨c*Real.sqrt a,mul_lt_mul_of_pos_left hsR hc,?_⟩
    have he : c*Real.sqrt a/c=Real.sqrt a := by field_simp
    change (c*Real.sqrt a/c)^2=a
    rw [he,Real.sq_sqrt ha0.le]

end Yau.LeafProofs.L05Aux
