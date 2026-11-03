import Yau.Proofs.F01CountableSmoothSubsequence

/-! Local limits of one sequence agree on every chart overlap by
uniqueness of genuine limits. Choosing representatives therefore constructs
one global value function, rather than assuming a gluing realization. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {A : Type*} {B : ℕ → Type*} {F : Type*}
  [TopologicalSpace F] [T2Space F] [Zero F]

theorem pointwise_chart_limit_glue (T : Set A)
    (e : ∀ j, B j → A) (hinto : ∀ j x, e j x ∈ T)
    (hcover : ∀ y ∈ T, ∃ j x, e j x = y)
    (f : ℕ → A → F) (v : ∀ j, B j → F)
    (hconv : ∀ j x, Tendsto (fun m => f m (e j x)) atTop (𝓝 (v j x))) :
    ∃ g : A → F,
      (∀ y ∈ T, Tendsto (fun m => f m y) atTop (𝓝 (g y))) ∧
      ∀ j x, g (e j x) = v j x := by
  classical
  have hrepresent (y : A) (hy : y ∈ T) : ∃ p : Sigma B, e p.1 p.2 = y := by
    obtain ⟨j, x, h⟩ := hcover y hy
    exact ⟨⟨j, x⟩, h⟩
  let choose (y : A) (hy : y ∈ T) : Sigma B := Classical.choose (hrepresent y hy)
  have hchoose (y : A) (hy : y ∈ T) : e (choose y hy).1 (choose y hy).2 = y :=
    Classical.choose_spec (hrepresent y hy)
  let g : A → F := fun y => if hy : y ∈ T then v (choose y hy).1 (choose y hy).2 else 0
  have hpoint (y : A) (hy : y ∈ T) : Tendsto (fun m => f m y) atTop (𝓝 (g y)) := by
    have h := hconv (choose y hy).1 (choose y hy).2
    rw [hchoose y hy] at h
    simpa only [g, dif_pos hy] using h
  refine ⟨g, hpoint, ?_⟩
  intro j x
  exact tendsto_nhds_unique (hpoint (e j x) (hinto j x)) (hconv j x)

end Yau.NodeProofs.F01Aux
