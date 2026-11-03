import Yau.Proofs.C07InverseCompatibility

/-! Agreeing actual inverse branches glue on their open union. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

def openBranchGlue (V : ι → Set M.Carrier)
    (b : ι → M.Carrier → ComplexVector n) (x : M.Carrier) : ComplexVector n := by
  classical
  exact if hx : ∃ i, x ∈ V i then b (Classical.choose hx) x else 0

theorem openBranchGlue_eq (V : ι → Set M.Carrier)
    (b : ι → M.Carrier → ComplexVector n)
    (heq : ∀ i j x, x ∈ V i → x ∈ V j → b i x = b j x)
    {i : ι} {x : M.Carrier} (hx : x ∈ V i) : openBranchGlue V b x = b i x := by
  classical
  have hex : ∃ i, x ∈ V i := ⟨i, hx⟩
  rw [openBranchGlue, dif_pos hex]
  exact heq _ i x (Classical.choose_spec hex) hx

theorem openBranchGlue_continuousOn (V : ι → Set M.Carrier)
    (b : ι → M.Carrier → ComplexVector n) (hV : ∀ i, IsOpen (V i))
    (hb : ∀ i, ContinuousOn (b i) (V i))
    (heq : ∀ i j x, x ∈ V i → x ∈ V j → b i x = b j x) :
    ContinuousOn (openBranchGlue V b) (⋃ i, V i) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hnear : openBranchGlue V b =ᶠ[nhds x] b i := by
    filter_upwards [(hV i).mem_nhds hi] with y hy
    exact openBranchGlue_eq V b heq hy
  exact ((hb i).continuousAt ((hV i).mem_nhds hi)).congr_of_eventuallyEq hnear
    |>.continuousWithinAt

theorem openBranchGlue_point (V : ι → Set M.Carrier)
    (b : ι → M.Carrier → ComplexVector n)
    (heq : ∀ i j x, x ∈ V i → x ∈ V j → b i x = b j x)
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hp : ∀ i x, x ∈ V i → b i x ∈ Metric.ball 0 r ∧ Φ (b i x) = x)
    {x : M.Carrier} (hx : x ∈ ⋃ i, V i) :
    openBranchGlue V b x ∈ Metric.ball 0 r ∧ Φ (openBranchGlue V b x) = x := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [openBranchGlue_eq V b heq hi]
  exact hp i x hi

theorem openBranchGlue_mdifferentiable (V : ι → Set M.Carrier)
    (b : ι → M.Carrier → ComplexVector n) (hV : ∀ i, IsOpen (V i))
    (hb : ∀ i, ContinuousOn (b i) (V i))
    (heq : ∀ i j x, x ∈ V i → x ∈ V j → b i x = b j x)
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    (hp : ∀ i x, x ∈ V i → b i x ∈ Metric.ball 0 r ∧ Φ (b i x) = x) :
    MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n)
      (openBranchGlue V b) (⋃ i, V i) :=
  continuous_manifold_inverse_mdifferentiable hΦ (isOpen_iUnion hV)
    (openBranchGlue_continuousOn V b hV hb heq)
    (fun _ hx => (openBranchGlue_point V b heq hp hx).1)
    (fun _ hx => (openBranchGlue_point V b heq hp hx).2)

end Yau.Proofs.C07Aux
