import Yau.Proofs.V04WallErrorQuadratic

/-! Horizontal, mixed, and vertical blocks of the actual fiber
quadratic Hessian, in one valid fixed cotangent chart. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n : ℕ}

theorem wirt_zero_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z : E) : wirt f z 0 = 0 := by simp [wirt]

theorem wirtBar_zero_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z : E) : wirtBar f z 0 = 0 := by simp [wirtBar]

theorem complexQuadratic_eq_ofReal_re
    {A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {p : CotangentCoord n}
    (hA : (A p.1).IsHermitian) : ((complexQuadratic A p).re : ℂ) = complexQuadratic A p := by
  have hq : complexQuadratic A p =
      star (WithLp.ofLp p.2) ⬝ᵥ (A p.1 *ᵥ WithLp.ofLp p.2) := by
    simp only [complexQuadratic, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hi := hA.im_star_dotProduct_mulVec_self (WithLp.ofLp p.2)
  rw [← hq] at hi
  apply Complex.ext
  · rfl
  · exact hi.symm

theorem leviMatrix_re_complexQuadratic_entry
    {A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexVector n)}
    (hU : IsOpen U) (hHerm : ∀ z ∈ U, (A z).IsHermitian)
    {p : CotangentCoord n} (hp : p.1 ∈ U) (i j : CotangentIndex n) :
    leviMatrix (fun z => (complexQuadratic A z).re) p cotangentDir i j =
      wirt (fun y => wirtBar (complexQuadratic A) y (cotangentDir i)) p (cotangentDir j) := by
  have heq : (fun z => ((complexQuadratic A z).re : ℂ)) =ᶠ[𝓝 p] complexQuadratic A := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hp] with z hz
    exact complexQuadratic_eq_ofReal_re (hHerm z.1 hz)
  exact mixedWirt_congr_of_eventuallyEq heq (cotangentDir i) (cotangentDir j)

theorem quadraticHessian_horizontal
    {A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {p : CotangentCoord n}
    (hA : ∀ a b, ContDiffAt ℝ 2 (fun z => A z a b) p.1) (i j : Fin n) :
    wirt (fun y => wirtBar (complexQuadratic A) y (cotangentDir (Sum.inl i)))
      p (cotangentDir (Sum.inl j)) =
      ∑ a, ∑ b, star (p.2 a) *
        wirt (fun z => wirtBar (fun u => A u a b) z (stdVec i)) p.1 (stdVec j) * p.2 b := by
  rw [mixedWirt_complexQuadratic hA]
  simp only [cotangentDir, Sum.elim_inl, Prod.fst, Prod.snd, WithLp.ofLp_zero, Pi.zero_apply,
    star_zero, zero_mul, zero_add, mul_zero, add_zero, mul_assoc]

theorem quadraticHessian_vertical
    {A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {p : CotangentCoord n}
    (hA : ∀ a b, ContDiffAt ℝ 2 (fun z => A z a b) p.1) (i j : Fin n) :
    wirt (fun y => wirtBar (complexQuadratic A) y (cotangentDir (Sum.inr i)))
      p (cotangentDir (Sum.inr j)) = A p.1 i j := by
  rw [mixedWirt_complexQuadratic hA]
  simp [cotangentDir, stdVec, wirt_zero_direction, wirtBar_zero_direction]

theorem quadraticHessian_mixed
    {A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {p : CotangentCoord n}
    (hA : ∀ a b, ContDiffAt ℝ 2 (fun z => A z a b) p.1) (i j : Fin n) :
    wirt (fun y => wirtBar (complexQuadratic A) y (cotangentDir (Sum.inl i)))
      p (cotangentDir (Sum.inr j)) =
      ∑ a, star (p.2 a) * wirtBar (fun z => A z a j) p.1 (stdVec i) := by
  rw [mixedWirt_complexQuadratic hA]
  simp [cotangentDir, stdVec, wirt_zero_direction, mul_assoc]

end Yau.Blueprint.V04Proof.WallErrorAux
