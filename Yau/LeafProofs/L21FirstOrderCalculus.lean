import Yau.LeafProofs.L21FlatEnergy

/-! Exact product and commutator calculus for the original complex
first-order rows on the real tangent space. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def rowApply {ι : Type*} [Fintype ι] (v : ι → X n) (p : ι → X n → ℂ)
    (f : X n → ℂ) (x : X n) : ℂ :=
  ∑ a, p a x * fderiv ℝ f x (v a)

theorem rowApply_mul {ι : Type*} [Fintype ι]
    (v : ι → X n) (p : ι → X n → ℂ) {f g : X n → ℂ} {x : X n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    rowApply v p (fun y => f y * g y) x =
      f x * rowApply v p g x + g x * rowApply v p f x := by
  simp only [rowApply, fderiv_fun_mul hf hg, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring

theorem fderiv_rowApply {ι : Type*} [Fintype ι]
    (v : ι → X n) (p : ι → X n → ℂ) {f : X n → ℂ} {x : X n}
    (hp : ∀ a, DifferentiableAt ℝ (p a) x)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (w : X n) :
    fderiv ℝ (rowApply v p f) x w =
      ∑ a, (fderiv ℝ (p a) x w * fderiv ℝ f x (v a) +
        p a x * fderiv ℝ (fderiv ℝ f) x w (v a)) := by
  have hd (a : ι) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (v a)) x :=
    hf.clm_apply (differentiableAt_const (v a))
  change fderiv ℝ (fun y => ∑ a, p a y * fderiv ℝ f y (v a)) x w = _
  rw [fderiv_fun_sum (A := fun a y => p a y * fderiv ℝ f y (v a))
    (fun a _ => (hp a).mul (hd a)), ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_fun_mul (c := p a) (d := fun y => fderiv ℝ f y (v a)) (hp a) (hd a)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, fderiv_directional hf]
  ring

theorem rowApply_commutator {ι : Type*} [Fintype ι]
    (v : ι → X n) (p q : ι → X n → ℂ) {f : X n → ℂ} {x : X n}
    (hp : ∀ a, DifferentiableAt ℝ (p a) x)
    (hq : ∀ a, DifferentiableAt ℝ (q a) x) (hf : ContDiffAt ℝ ∞ f x) :
    rowApply v p (rowApply v q f) x - rowApply v q (rowApply v p f) x =
      ∑ b, (rowApply v p (q b) x - rowApply v q (p b) x) * fderiv ℝ f x (v b) := by
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsym (a b : ι) :
      fderiv ℝ (fderiv ℝ f) x (v a) (v b) =
        fderiv ℝ (fderiv ℝ f) x (v b) (v a) :=
    (hf.isSymmSndFDerivAt (by simp)).eq _ _
  have hsecond : (∑ a, ∑ b, p a x * (q b x * fderiv ℝ (fderiv ℝ f) x (v a) (v b))) =
      ∑ a, ∑ b, q a x * (p b x * fderiv ℝ (fderiv ℝ f) x (v a) (v b)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    rw [hsym]
    ring
  change (∑ a, p a x * fderiv ℝ (rowApply v q f) x (v a)) -
    (∑ a, q a x * fderiv ℝ (rowApply v p f) x (v a)) = _
  simp only [fderiv_rowApply v q hq hdf, fderiv_rowApply v p hp hdf,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [hsecond]
  simp only [rowApply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (f := fun b a => p a x * (fderiv ℝ (q b) x (v a) * fderiv ℝ f x (v b))),
    Finset.sum_comm (f := fun b a => q a x * (fderiv ℝ (p b) x (v a) * fderiv ℝ f x (v b)))]
  ring

theorem dbarA_mul (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    {f g : X n → ℂ} {x : X n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbarA A i (fun y => f y * g y) x =
      f x * dbarA A i g x + g x * dbarA A i f x := by
  simpa only [rowApply, ← dbarA_eq_real_rows] using
    rowApply_mul Yau.realVec (dbarRealCoefficient A i) hf hg

end Yau.LeafProofs.L21Aux
