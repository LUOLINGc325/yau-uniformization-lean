import Yau.Proofs.F05BootstrapCompactHolder

/-! One actual subsequence works simultaneously for every chart in the
finite supplied atlas. No simultaneous limiting-jet selection is assumed. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_finite_holder_compact_subsequence {n : ℕ} {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [ProperSpace V] {α C : ℝ} (hα : 0 < α)
    (Q : ι → Set (Point n)) (hQ : ∀ i, IsCompact (Q i))
    (f : ℕ → ι → Point n → V) (hf : ∀ k i, HolderBound α (Q i) (f k i) C) :
    ∃ (φ : ℕ → ℕ) (g : ι → Point n → V), StrictMono φ ∧
      ∀ i, TendstoUniformlyOn (fun k => f (φ k) i) (g i) atTop (Q i) := by
  classical
  have hFinite (s : Finset ι) :
      ∃ (φ : ℕ → ℕ) (g : ι → Point n → V), StrictMono φ ∧
        ∀ i ∈ s, TendstoUniformlyOn (fun k => f (φ k) i) (g i) atTop (Q i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id,fun _ _ => 0,strictMono_id,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨φ,g,hφ,hOld⟩ := ih
      obtain ⟨ψ,G,hψ,hNew⟩ := F05_holder_compact_subsequence hα (hQ i) (fun k => hf (φ k) i)
      refine ⟨φ ∘ ψ,fun j => if j = i then G else g j,hφ.comp hψ,?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa only [Function.comp_apply,ite_true] using hNew
      · have hjS : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hji
        have hConv := hOld j hjS
        simp only [if_neg hji]
        exact fun U hU => hψ.tendsto_atTop.eventually (hConv U hU)
  obtain ⟨φ,g,hφ,hg⟩ := hFinite Finset.univ
  exact ⟨φ,g,hφ,fun i => hg i (Finset.mem_univ i)⟩

end Yau.Proofs.F05Aux
