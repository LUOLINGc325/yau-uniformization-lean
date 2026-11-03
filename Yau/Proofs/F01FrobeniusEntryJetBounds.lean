import Yau.Proofs.F01ScalarSymbolSmooth

/-! Native entry evaluation is an actual bounded real linear map
from the original Frobenius matrix space. Its finite common budget
controls every spatial derivative order without replacing the norm. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance frobeniusEntryJetOpNorm (n : ℕ) :
    Norm (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ) := ContinuousLinearMap.hasOpNorm

theorem frobenius_entry_common_budget (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : Fin n, ‖frobeniusComplexEntryCLM i j‖ ≤ C := by
  classical
  let C := 1 + ∑ i : Fin n, ∑ j : Fin n, ‖frobeniusComplexEntryCLM i j‖
  have hSum : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, ‖frobeniusComplexEntryCLM i j‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ContinuousLinearMap.opNorm_nonneg _))
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro i j
  have hJ := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun j _ => ContinuousLinearMap.opNorm_nonneg (frobeniusComplexEntryCLM i j)) (Finset.mem_univ j)
  have hI : (∑ j : Fin n, ‖frobeniusComplexEntryCLM i j‖) ≤
      ∑ i : Fin n, ∑ j : Fin n, ‖frobeniusComplexEntryCLM i j‖ :=
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => Finset.sum_nonneg (fun j _ => ContinuousLinearMap.opNorm_nonneg (frobeniusComplexEntryCLM i j)))
    (Finset.mem_univ i)
  exact hJ.trans (hI.trans (by dsimp only [C]; linarith))

theorem frobenius_entry_iteratedFDeriv_norm_le
    {O : Set E} {f : E → Matrix (Fin n) (Fin n) ℂ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {x : E} (hx : x ∈ O) (k : ℕ) (i j : Fin n) :
    ‖iteratedFDeriv ℝ k (fun y => f y i j) x‖ ≤
      ‖frobeniusComplexEntryCLM i j‖ * ‖iteratedFDeriv ℝ k f x‖ := by
  let L := frobeniusComplexEntryCLM i j
  change ‖iteratedFDeriv ℝ k (fun y => L (f y)) x‖ ≤ _
  have he : iteratedFDeriv ℝ k (fun y => L (f y)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) :=
    L.iteratedFDeriv_comp_left (hf.contDiffAt (hO.mem_nhds hx)) (by simp)
  rw [he]
  exact L.norm_compContinuousMultilinearMap_le _

end Yau.NodeProofs.F01Aux
