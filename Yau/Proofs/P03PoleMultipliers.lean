import Yau.Proofs.P03FinitePoleWeights
import Yau.LeafProofs.L22Uniform
import Mathlib.Analysis.Normed.Group.Bounded

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

def poleMultiplier (p : M.Carrier → ℝ) (x : M.Carrier) : ℝ := Real.exp (-p x / 2)

theorem poleMultiplier_smooth (p : M.Carrier → ℝ) (hp : SmoothFn p) :
    SmoothFn (poleMultiplier p) := by
  intro a
  exact ((hp a).neg.div_const 2).exp

theorem poleMultiplier_ge_one (p : M.Carrier → ℝ) (hp : ∀ x, p x ≤ 0) (x : M.Carrier) :
    1 ≤ poleMultiplier p x := by
  apply Real.one_le_exp_iff.mpr
  have h := hp x
  linarith

theorem poleMultiplier_sq_weight (Φ p : M.Carrier → ℝ) (x : M.Carrier) :
    poleMultiplier p x ^ 2 * Real.exp (-Φ x) = Real.exp (-(Φ x + p x)) := by
  unfold poleMultiplier
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem exists_poleMultiplier_bound (p : M.Carrier → ℝ) (hp : SmoothFn p)
    (hc : HasCompactSupport p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, poleMultiplier p x ^ 2 ≤ C ^ 2 := by
  obtain ⟨A, hA⟩ := (L18Aux.continuous_of_smoothFn hp).bounded_above_of_compact_support hc
  refine ⟨Real.exp (A / 2), (Real.exp_pos _).le, ?_⟩
  intro x
  have ha := hA x
  change |p x| ≤ A at ha
  have harg : -p x / 2 ≤ A / 2 := by have hh := (abs_le.mp ha).1; linarith
  exact (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr (Real.exp_le_exp.mpr harg)

theorem finitePolePerturbation_compactSupport {ι : Type*} [Fintype ι]
    (a : ι → M.Carrier) (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (c : ℝ) (j : ℕ) : HasCompactSupport (finitePolePerturbation a b c j) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun i => manifoldCutoffPole c (b i) (poleEpsilon j))
    (fun i _ => manifoldCutoffPole_compactSupport c (b i) (poleEpsilon j))
  have he : finitePolePerturbation a b c j =
      ∑ i, manifoldCutoffPole c (b i) (poleEpsilon j) := by
    funext x
    simp only [finitePolePerturbation, Finset.sum_apply]
  exact he.symm ▸ h

end Yau.NodeProofs.P03Aux
