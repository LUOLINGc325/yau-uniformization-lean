import Yau.Proofs.F03ScalarL2

/-! Degree-zero actual alternating forms associated to scalar functions. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem sum_fin_one_eval {α : Type*} [Fintype α] (F : α → ℝ) :
    (∑ I : Fin 1 → α, F (I 0)) = ∑ a, F a := by
  simpa using (Equiv.funUnique (Fin 1) α).sum_comp F

theorem scalarZeroForm_components (f : M.Carrier → ℝ) (x : M.Carrier)
    (z : ComplexVector n) (I : Fin 0 → RIdx n) :
    formComponents (scalarZeroForm f) x z I = inChart x f z := by
  simp [formComponents, scalarZeroForm, inChart]

theorem scalarZeroForm_smooth {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    SmoothRealForm (scalarZeroForm f) := by
  intro x I
  simpa only [scalarZeroForm_components] using hf x

theorem scalarZeroForm_eq_zero_iff (f : M.Carrier → ℝ) (x : M.Carrier) :
    scalarZeroForm f x = 0 ↔ f x = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun A => A (fun i : Fin 0 => Fin.elim0 i)) h
    simpa [scalarZeroForm] using hh
  · intro h
    apply ContinuousAlternatingMap.ext
    intro v
    simp [scalarZeroForm, h]

theorem scalarZeroForm_tsupport (f : M.Carrier → ℝ) :
    closure {x | scalarZeroForm f x ≠ 0} = tsupport f := by
  congr 1
  ext x
  exact not_congr (scalarZeroForm_eq_zero_iff f x)

theorem scalarZeroForm_add (f k : M.Carrier → ℝ) :
    scalarZeroForm (f + k) = scalarZeroForm f + scalarZeroForm k := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  simp [scalarZeroForm]

theorem scalarZeroForm_smul (c : ℝ) (f : M.Carrier → ℝ) :
    scalarZeroForm (c • f) = c • scalarZeroForm f := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  simp [scalarZeroForm]

end Yau.Proofs.F03Aux
