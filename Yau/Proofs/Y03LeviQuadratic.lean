import Yau.Proofs.Y03Levi

/-! A positive Levi matrix controls its actual directional quadratic form. -/

open scoped ComplexOrder Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wirt_complex_smul_dir (f : V → ℂ) (z v : V) (c : ℂ) :
    wirt f z (c • v) = c * wirt f z v := by
  have hc : c • v = c.re • v + c.im • (Complex.I • v) := by
    rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    simp
  rw [hc, wirt_add_dir, wirt_real_smul_dir, wirt_real_smul_dir, wirt_I_dir]
  calc
    _ = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * wirt f z v := by ring
    _ = _ := by rw [Complex.re_add_im]

theorem wirtBar_complex_smul_dir (f : V → ℂ) (z v : V) (c : ℂ) :
    wirtBar f z (c • v) = star c * wirtBar f z v := by
  have hc : c • v = c.re • v + c.im • (Complex.I • v) := by
    rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    simp
  rw [hc, wirtBar_add_dir, wirtBar_real_smul_dir, wirtBar_real_smul_dir, wirtBar_I_dir]
  have hconj : (c.re : ℂ) - (c.im : ℂ) * Complex.I = star c := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  calc
    _ = ((c.re : ℂ) - (c.im : ℂ) * Complex.I) * wirtBar f z v := by ring
    _ = _ := by rw [hconj]

theorem wirt_sum_dir {ι : Type*} (s : Finset ι) (f : V → ℂ) (z : V) (v : ι → V) :
    wirt f z (∑ i ∈ s, v i) = ∑ i ∈ s, wirt f z (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirt]
  | @insert i s hi ih => rw [Finset.sum_insert hi, wirt_add_dir, ih, Finset.sum_insert hi]

theorem wirtBar_sum_dir {ι : Type*} (s : Finset ι) (f : V → ℂ) (z : V) (v : ι → V) :
    wirtBar f z (∑ i ∈ s, v i) = ∑ i ∈ s, wirtBar f z (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirtBar]
  | @insert i s hi ih => rw [Finset.sum_insert hi, wirtBar_add_dir, ih, Finset.sum_insert hi]

theorem wirt_const_mul_fn {f : V → ℂ} {z : V} (hf : DifferentiableAt ℝ f z) (v : V) (c : ℂ) :
    wirt (fun x => c * f x) z v = c * wirt f z v := by
  unfold wirt
  rw [fderiv_const_mul hf]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem wirt_add_fn {f g : V → ℂ} {z : V}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : V) :
    wirt (fun x => f x + g x) z v = wirt f z v + wirt g z v := by
  unfold wirt
  rw [fderiv_fun_add hf hg]
  simp only [add_apply]
  ring

theorem wirt_sum_fn {ι : Type*} (s : Finset ι) (f : ι → V → ℂ) {z : V}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (v : V) :
    wirt (fun x => ∑ i ∈ s, f i x) z v = ∑ i ∈ s, wirt (f i) z v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirt]
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, DifferentiableAt ℝ (f j) z :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsum : DifferentiableAt ℝ (fun x => ∑ j ∈ s, f j x) z := by
      exact DifferentiableAt.fun_sum hfs
    simp only [Finset.sum_insert hi]
    rw [wirt_add_fn hfi hsum, ih hfs]

theorem levi_quadratic_eq_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : V → ℝ} {z : V} (hf : ContDiffAt ℝ 2 f z) (dir : ι → V) (c : ι → ℂ) :
    wirt (fun x => wirtBar (fun y => (f y : ℂ)) x (∑ i, c i • dir i)) z
      (∑ i, c i • dir i) =
        star c ⬝ᵥ (leviMatrix f z dir *ᵥ c) := by
  let fc : V → ℂ := fun x => (f x : ℂ)
  have hfc : ContDiffAt ℝ 2 fc z := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hfun : (fun x => wirtBar fc x (∑ i, c i • dir i)) =
      fun x => ∑ i, star (c i) * wirtBar fc x (dir i) := by
    funext x
    rw [wirtBar_sum_dir]
    exact Finset.sum_congr rfl fun i _ => wirtBar_complex_smul_dir fc x (dir i) (c i)
  change wirt (fun x => wirtBar fc x (∑ i, c i • dir i)) z _ = _
  rw [hfun, wirt_sum_fn]
  · simp only [wirt_const_mul_fn ((wirtBar_contDiffAt hfc _).differentiableAt (by norm_num)),
      wirt_sum_dir, wirt_complex_smul_dir]
    unfold Matrix.mulVec dotProduct leviMatrix
    simp only [Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro i _
    exact ((wirtBar_contDiffAt hfc (dir i)).differentiableAt (by norm_num)).const_mul _

theorem levi_direction_nonneg_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : V → ℝ} {z : V} (hf : ContDiffAt ℝ 2 f z) (dir : ι → V) (c : ι → ℂ)
    (hpos : (leviMatrix f z dir).PosSemidef) :
    0 ≤ (wirt (fun x => wirtBar (fun y => (f y : ℂ)) x (∑ i, c i • dir i)) z
      (∑ i, c i • dir i)).re := by
  rw [levi_quadratic_eq_matrix hf dir c]
  exact (Complex.nonneg_iff.1 (hpos.dotProduct_mulVec_nonneg c)).1

end Yau.Blueprint.Alignment.Y03Proof
