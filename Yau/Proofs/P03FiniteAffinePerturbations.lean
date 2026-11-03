import Yau.Proofs.P03CompactGoodSets

open scoped Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {A : Type*} [AddCommGroup A] [Module ℂ A] {m L : ℕ}

/-- A finite-dimensional affine family inside the original function or
section space, with one independent coefficient row for each output. -/
def finiteAffinePerturbation (base : Fin m → A) (h : Fin L → A)
    (T : Fin m → Fin L → ℂ) : Fin m → A :=
  fun j => base j + ∑ l, T j l • h l

@[simp]
theorem finiteAffinePerturbation_zero (base : Fin m → A) (h : Fin L → A) :
    finiteAffinePerturbation base h 0 = base := by
  funext j
  simp [finiteAffinePerturbation]

theorem finiteAffinePerturbation_continuous [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousSMul ℂ A] (base : Fin m → A) (h : Fin L → A) :
    Continuous (finiteAffinePerturbation base h) := by
  apply continuous_pi
  intro j
  apply continuous_const.add
  apply continuous_finset_sum
  intro l _
  have ht : Continuous (fun T : Fin m → Fin L → ℂ => T j l) := by fun_prop
  exact ht.smul continuous_const

theorem finiteAffinePerturbation_linearMap {F : Type*} [AddCommGroup F] [Module ℂ F]
    (e : A →ₗ[ℂ] F) (base : Fin m → A) (h : Fin L → A)
    (T : Fin m → Fin L → ℂ) (j : Fin m) :
    e (finiteAffinePerturbation base h T j) = e (base j) + ∑ l, T j l • e (h l) := by
  simp only [finiteAffinePerturbation, map_add, map_sum, map_smul]

theorem finiteAffinePerturbation_mem_closure [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousSMul ℂ A] (base : Fin m → A) (h : Fin L → A)
    {G : Set (Fin m → A)} (hd : Dense ((finiteAffinePerturbation base h) ⁻¹' G)) :
    base ∈ closure G := by
  simpa only [finiteAffinePerturbation_zero] using
    mem_closure_of_dense_parameters (finiteAffinePerturbation base h)
      (finiteAffinePerturbation_continuous base h) hd 0

end Yau.NodeProofs.P03Aux
