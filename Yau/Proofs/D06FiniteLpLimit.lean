import Yau.Proofs.D06HardyRadial

/-! A common almost-everywhere subsequence for finitely many actual L² limits. -/

open scoped Topology
open Filter MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem finiteLp_ae_subsequence {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [Fintype ι] (f : ℕ → ι → Lp ℂ 2 μ) (g : ι → Lp ℂ 2 μ)
    (hlim : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun n => f (ns n) i x) atTop (𝓝 (g i x)) := by
  classical
  have hfin (s : Finset ι) : ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, ∀ i ∈ s,
      Tendsto (fun n => f (ns n) i x) atTop (𝓝 (g i x)) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨id, strictMono_id, Eventually.of_forall (by simp)⟩
    | @insert i s _ ih =>
      obtain ⟨ns, hns, hnlim⟩ := ih
      have hi := (hlim i).comp hns.tendsto_atTop
      obtain ⟨ks, hks, hklim⟩ := (tendstoInMeasure_of_tendsto_Lp hi).exists_seq_tendsto_ae
      refine ⟨ns ∘ ks, hns.comp hks, ?_⟩
      filter_upwards [hnlim, hklim] with x hx hi
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact (hx j hj).comp hks.tendsto_atTop
  obtain ⟨ns, hns, hnlim⟩ := hfin Finset.univ
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hnlim] with x hx
  intro i
  exact hx i (Finset.mem_univ i)

end Yau.NodeProofs.D06Aux
