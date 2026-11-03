import Yau.Proofs.P03PoleSequence
import Yau.Proofs.P03LeviFiniteSums

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]

def finitePolePerturbation (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (c : ℝ) (j : ℕ) (x : M.Carrier) : ℝ :=
  ∑ i, manifoldCutoffPole c (b i) (poleEpsilon j) x

def finitePoleWeight (ψ : M.Carrier → ℝ) (k c : ℝ) (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (j : ℕ) (x : M.Carrier) : ℝ := k * ψ x + finitePolePerturbation a b c j x

theorem finitePolePerturbation_smooth (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i)) (c : ℝ) (j : ℕ) :
    SmoothFn (finitePolePerturbation a b c j) :=
  smoothFn_finset_sum Finset.univ _ fun i _ =>
    manifoldCutoffPole_smooth c (b i) (poleEpsilon_pos j)

theorem finitePoleWeight_smooth (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ)
    (k c : ℝ) (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i)) (j : ℕ) :
    SmoothFn (finitePoleWeight ψ k c a b j) := by
  intro x
  exact (contDiffOn_const.mul (hψ x)).add (finitePolePerturbation_smooth a b c j x)

theorem finitePolePerturbation_antitone (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (c : ℝ) (hc : 0 ≤ c) (x : M.Carrier) :
    Antitone (fun j => finitePolePerturbation a b c j x) := by
  intro i j hij
  exact Finset.sum_le_sum fun l _ => manifoldCutoffPole_antitone c hc (b l) x hij

theorem finitePolePerturbation_nonpos (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (hR : ∀ i, (b i).rOut ≤ 1 / 2) (c : ℝ) (hc : 0 ≤ c) (j : ℕ) (x : M.Carrier) :
    finitePolePerturbation a b c j x ≤ 0 :=
  Finset.sum_nonpos fun i _ => manifoldCutoffPole_nonpos c hc (b i) (hR i) j x

theorem finitePoleWeight_antitone (ψ : M.Carrier → ℝ) (k c : ℝ) (hc : 0 ≤ c)
    (a : ι → M.Carrier) (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (x : M.Carrier) : Antitone (fun j => finitePoleWeight ψ k c a b j x) :=
  fun _ _ hij => add_le_add (le_refl (k * ψ x))
    (finitePolePerturbation_antitone a b c hc x hij)

theorem finitePoleWeight_le_background (ψ : M.Carrier → ℝ) (k c : ℝ) (hc : 0 ≤ c)
    (a : ι → M.Carrier) (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (hR : ∀ i, (b i).rOut ≤ 1 / 2) (j : ℕ) (x : M.Carrier) :
    finitePoleWeight ψ k c a b j x ≤ k * ψ x :=
  add_le_of_nonpos_right (finitePolePerturbation_nonpos a b hR c hc j x)

end Yau.NodeProofs.P03Aux
