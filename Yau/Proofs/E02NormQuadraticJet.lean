import Yau.Proofs.E02PeanoJet

open Set Filter Asymptotics
open scoped Topology Asymptotics InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem realSecondJet_sub {f g : E → ℝ} {x : E} {p q : E →L[ℝ] ℝ}
    {A B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : RealSecondJet f x p A) (hg : RealSecondJet g x q B) :
    RealSecondJet (fun y => f y-g y) x (p-q) (A-B) := by
  refine ⟨?_,?_⟩
  · intro v w
    simp only [sub_apply]
    rw [hf.1 v w,hg.1 v w]
  · convert hf.2.sub hg.2 using 1
    funext y
    simp only [sub_apply]
    ring

/-- Exact Euclidean quadratic jet, with its actual coefficient 1/kappa.
This fixes the normalization of the lower quadratic viscosity tests. -/
theorem realSecondJet_norm_sq_div_two (κ : ℝ) (x : E) :
    RealSecondJet (fun y : E => ‖y‖^2/(2*κ)) x
      (κ⁻¹ • innerSL ℝ x) (κ⁻¹ • innerSL ℝ (E := E)) := by
  refine ⟨?_,?_⟩
  · intro v w
    change κ⁻¹ * ⟪v,w⟫_ℝ = κ⁻¹ * ⟪w,v⟫_ℝ
    rw [real_inner_comm]
  · have hZero : (fun y : E => ‖y‖^2/(2*κ)-‖x‖^2/(2*κ)-
        (κ⁻¹ • innerSL ℝ x) (y-x)-
        (1/2)*(κ⁻¹ • innerSL ℝ (E := E)) (y-x) (y-x)) = fun _ => 0 := by
      funext y
      change ‖y‖^2/(2*κ)-‖x‖^2/(2*κ)-κ⁻¹*⟪x,y-x⟫_ℝ-
        (1/2)*(κ⁻¹*⟪y-x,y-x⟫_ℝ) = 0
      rw [real_inner_self_eq_norm_sq,norm_sub_sq_real,inner_sub_right,
        real_inner_self_eq_norm_sq,real_inner_comm y x]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hZero]
    exact isLittleO_zero _ _

end Yau.NodeProofs.E02Aux
