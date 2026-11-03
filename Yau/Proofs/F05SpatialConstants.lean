import Yau.Geometry.Calculus
import Mathlib

/-! Spatial constants leave the computed Levi form and Laplacian unchanged. -/

noncomputable section

namespace Yau.Proofs.F05Aux

theorem wirtBar_real_add_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℝ) (c : ℝ) (z v : V) :
    wirtBar (fun u => ((f u + c : ℝ) : ℂ)) z v =
      wirtBar (fun u => (f u : ℂ)) z v := by
  simp only [Complex.ofReal_add, wirtBar, fderiv_add_const]

theorem leviMatrix_add_const {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℝ) (c : ℝ) (z : V) (dir : ι → V) :
    leviMatrix (fun u => f u + c) z dir = leviMatrix f z dir := by
  funext a b
  change wirt (fun w => wirtBar (fun u => ((f u + c : ℝ) : ℂ)) w (dir a)) z (dir b) = _
  have heq : (fun w => wirtBar (fun u => ((f u + c : ℝ) : ℂ)) w (dir a)) =
      (fun w => wirtBar (fun u => (f u : ℂ)) w (dir a)) := by
    funext w
    exact wirtBar_real_add_const f c w (dir a)
  rw [heq]
  rfl

theorem levi_add_const {n : ℕ} {M : ComplexManifold n}
    (f : M.Carrier → ℝ) (c : ℝ) (x : M.Carrier) :
    levi (fun y => f y + c) x = levi f x := by
  exact leviMatrix_add_const (inChart x f) c (chartPt x x) stdVec

theorem laplacian_add_const {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (f : M.Carrier → ℝ) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun y => f y + c) x = laplacian h f x := by
  simp only [laplacian, levi_add_const]

end Yau.Proofs.F05Aux
