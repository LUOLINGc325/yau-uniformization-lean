import Yau.Proofs.P06HodgeRegularityWeakProducts
import Yau.Proofs.P06HodgeRegularityLocalization

/-! Actual L² and weak-derivative finite-list sums, with multiplicities. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularityMemLp_list_sum (xs : List γ) (F : γ → E → ℝ)
    (hF : ∀ a ∈ xs, MemLp (F a) 2 ν) :
    MemLp (fun z => (xs.map (fun a => F a z)).sum) 2 ν := by
  induction xs with
  | nil => exact MemLp.zero'
  | cons a xs ih =>
    have ht := ih (fun b hb => hF b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    have hfun : (fun z => F a z + (xs.map (fun b => F b z)).sum) =
        F a + fun z => (xs.map (fun b => F b z)).sum := rfl
    rw [hfun]
    exact (hF a List.mem_cons_self).add ht

theorem regularityWeakDeriv_list_sum {O : Set E} (e : E) (xs : List γ) (F D : γ → E → ℝ)
    (hF : ∀ a ∈ xs, MemLp (F a) 2 (ν.restrict O))
    (hD : ∀ a ∈ xs, MemLp (D a) 2 (ν.restrict O))
    (hW : ∀ a ∈ xs, regularityWeakDeriv ν O e (F a) (D a)) :
    regularityWeakDeriv ν O e (fun z => (xs.map (fun a => F a z)).sum)
      (fun z => (xs.map (fun a => D a z)).sum) := by
  induction xs with
  | nil => exact regularityWeakDeriv_zero ν O e
  | cons a xs ih =>
    have hFt := fun b hb => hF b (List.mem_cons_of_mem _ hb)
    have hDt := fun b hb => hD b (List.mem_cons_of_mem _ hb)
    have hWt := fun b hb => hW b (List.mem_cons_of_mem _ hb)
    have htail := ih hFt hDt hWt
    have hFsum := regularityMemLp_list_sum (ν.restrict O) xs F hFt
    have hDsum := regularityMemLp_list_sum (ν.restrict O) xs D hDt
    simpa only [List.map_cons, List.sum_cons] using regularityWeakDeriv_add ν
      (hF a List.mem_cons_self) hFsum (hD a List.mem_cons_self) hDsum
      (hW a List.mem_cons_self) htail

theorem regularityCompact_mul_memLp {O : Set E} (hO : IsOpen O) {a u : E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) (haO : tsupport a ⊆ O)
    (hu : MemLp u 2 (ν.restrict O)) : MemLp (fun z => a z * u z) 2 ν := by
  have htop : MemLp a (⊤ : ENNReal) (ν.restrict O) :=
    (ha.continuous.memLp_top_of_hasCompactSupport hca ν).restrict O
  apply regularityMemLp_zero_off ν hO.measurableSet (htop.mul hu)
  intro z hz
  change a z * u z = 0
  rw [image_eq_zero_of_notMem_tsupport (fun h => hz (haO h)), zero_mul]

end Yau.NodeProofs.P06Aux
