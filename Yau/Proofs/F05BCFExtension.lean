import Mathlib

/-! Total values of a bounded continuous function on a closed physical set.
Continuity is asserted exactly on that set. -/

open Set
noncomputable section

namespace Yau.Proofs.F05Aux

variable {Z V : Type*} [TopologicalSpace Z] [NormedAddCommGroup V] {Q : Set Z}

def F05BCFFun (f : BoundedContinuousFunction Q V) (p : Z) : V := by
  classical
  exact if hp : p ∈ Q then f ⟨p,hp⟩ else 0

theorem F05BCFFun_apply (f : BoundedContinuousFunction Q V) (p : Q) :
    F05BCFFun f p.val = f p := by
  simp [F05BCFFun,p.property]

theorem F05BCFFun_norm_le (f : BoundedContinuousFunction Q V) (p : Z) :
    ‖F05BCFFun f p‖ ≤ ‖f‖ := by
  classical
  by_cases hp : p ∈ Q
  · rw [F05BCFFun_apply f ⟨p,hp⟩]
    exact f.norm_coe_le_norm ⟨p,hp⟩
  · simp only [F05BCFFun,dite_eq_right hp,norm_zero]
    exact norm_nonneg f

theorem F05BCFFun_continuousOn (f : BoundedContinuousFunction Q V) :
    ContinuousOn (F05BCFFun f) Q := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (fun p : Q => F05BCFFun f p.val) = (f : Q → V) :=
    funext (F05BCFFun_apply f)
  change Continuous (fun p : Q => F05BCFFun f p.val)
  rw [heq]
  exact f.continuous

theorem F05BCFFun_add (f g : BoundedContinuousFunction Q V) (p : Z) :
    F05BCFFun (f+g) p = F05BCFFun f p + F05BCFFun g p := by
  classical
  by_cases hp : p ∈ Q <;> simp [F05BCFFun,hp]

theorem F05BCFFun_smul [NormedSpace ℝ V] (a : ℝ)
    (f : BoundedContinuousFunction Q V) (p : Z) :
    F05BCFFun (a • f) p = a • F05BCFFun f p := by
  classical
  by_cases hp : p ∈ Q <;> simp [F05BCFFun,hp]

end Yau.Proofs.F05Aux
