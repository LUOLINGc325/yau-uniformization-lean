import Yau.LeafProofs.L21ClassicalEquation
import Yau.LeafProofs.L21Normalization

/-! Unit real coordinate directions bound actual coordinate words by the
finite Fréchet jets used in the original normalization. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem norm_realVec (a : Yau.RIdx n) : ‖Yau.realVec a‖ = 1 := by
  rw [← realBasis_apply n a]
  exact (realBasis n).norm_eq_one a

theorem wordDerivative_append_singleton (f : X n → ℂ) (w : List (Yau.RIdx n)) (a : Yau.RIdx n) :
    wordDerivative f (w ++ [a]) = wordDerivative (fun x => fderiv ℝ f x (Yau.realVec a)) w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [List.cons_append, wordDerivative, ih]

theorem norm_wordDerivative_le_iteratedFDeriv (w : List (Yau.RIdx n))
    (f : X n → ℂ) (x : X n) (hf : ContDiffAt ℝ ∞ f x) :
    ‖wordDerivative f w x‖ ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  induction w using List.reverseRecOn generalizing f with
  | nil => simpa only [wordDerivative, List.length_nil, norm_iteratedFDeriv_zero] using le_refl ‖f x‖
  | append_singleton w a ih =>
    have hdf := hf.fderiv_right (m := ∞) (by simp)
    have hg : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y (Yau.realVec a)) x :=
      hdf.clm_apply contDiffAt_const
    rw [wordDerivative_append_singleton, List.length_append, List.length_singleton]
    apply (ih _ hg).trans
    have hh := norm_iteratedFDeriv_clm_apply_const (c := Yau.realVec a) (n := w.length) hdf (by simp)
    simpa only [norm_realVec, one_mul, norm_iteratedFDeriv_fderiv] using hh

theorem jetBound_wordDerivative {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} {b : ℝ} (hJet : JetBound q b A O)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (x : X n) (hx : x ∈ O) (i j : Fin n) :
    ‖wordDerivative (fun y => A y i j) w x‖ ≤ b :=
  (norm_wordDerivative_le_iteratedFDeriv w _ x ((hA i j).contDiffAt (hO.mem_nhds hx))).trans
    (hJet w.length hw x hx i j)

end Yau.LeafProofs.L21Aux
