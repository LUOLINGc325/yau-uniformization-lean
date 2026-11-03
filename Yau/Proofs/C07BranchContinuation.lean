import Yau.Proofs.C07InverseCompatibility
import Mathlib.Topology.Connected.LocallyConnected

/-! Agreement at one point propagates through a fixed connected overlap and then uniformly on compacts. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_branches_eq_on_connected
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    {V : Set M.Carrier} (hV : IsPreconnected V)
    {f g : M.Carrier → ComplexVector n} (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (hfball : ∀ x ∈ V, f x ∈ Metric.ball 0 r)
    (hgball : ∀ x ∈ V, g x ∈ Metric.ball 0 r)
    (hproj : ∀ x ∈ V, Φ (f x) = Φ (g x))
    (x : M.Carrier) (hx : x ∈ V) (heq : f x = g x) : EqOn f g V := by
  letI : PreconnectedSpace V := Subtype.preconnectedSpace hV
  have hfc : Continuous (fun y : V => f y) := continuousOn_iff_continuous_domRestrict.mp hf
  have hgc : Continuous (fun y : V => g y) := continuousOn_iff_continuous_domRestrict.mp hg
  have hcomp : Φ ∘ (fun y : V => f y) = Φ ∘ (fun y : V => g y) := by
    funext y
    exact hproj y y.2
  have h := chart_lifts_unique hΦ hfc hgc
    (fun y => hfball y y.2) (fun y => hgball y y.2) hcomp (⟨x, hx⟩ : V) heq
  exact fun y hy => congrFun h ⟨y, hy⟩

theorem uniform_eventual_branch_agreement
    {U V K : Set M.Carrier} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKUV : K ⊆ U ∩ V)
    (Φ : ℝ → ComplexVector n → M.Carrier)
    (f g : ℝ → M.Carrier → ComplexVector n) {r T₀ : ℝ}
    (hΦ : ∀ t, T₀ ≤ t → IsLocalBiholomorphism (Φ t) r)
    (hf : ∀ t, T₀ ≤ t → ContinuousOn (f t) U)
    (hg : ∀ t, T₀ ≤ t → ContinuousOn (g t) V)
    (hfball : ∀ t, T₀ ≤ t → ∀ x ∈ U, f t x ∈ Metric.ball 0 r)
    (hgball : ∀ t, T₀ ≤ t → ∀ x ∈ V, g t x ∈ Metric.ball 0 r)
    (hproj : ∀ t, T₀ ≤ t → ∀ x ∈ U ∩ V, Φ t (f t x) = Φ t (g t x))
    (hpoint : ∀ x ∈ U ∩ V, ∃ S : ℝ, ∀ t, S ≤ t → f t x = g t x) :
    ∃ S : ℝ, T₀ ≤ S ∧ ∀ t, S ≤ t → EqOn (f t) (g t) K := by
  classical
  letI : LocallyConnectedSpace M.Carrier :=
    ChartedSpace.locallyConnectedSpace (ComplexVector n) M.Carrier
  let N : K → Set M.Carrier := fun x => connectedComponentIn (U ∩ V) x.1
  have hNo (x : K) : IsOpen (N x) := (hU.inter hV).connectedComponentIn
  have hNs (x : K) : N x ⊆ U ∩ V := connectedComponentIn_subset _ _
  have hNx (x : K) : x.1 ∈ N x := mem_connectedComponentIn (hKUV x.2)
  choose S hS using (fun x : K => hpoint x.1 (hKUV x.2))
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover N hNo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hNx ⟨x, hx⟩⟩)
  let T := max T₀ (∑ i ∈ I, max 0 (S i))
  have hT₀ : T₀ ≤ T := le_max_left _ _
  have hTi (i : K) (hi : i ∈ I) : S i ≤ T := by
    exact (le_max_right 0 (S i)).trans
      ((Finset.single_le_sum (fun j _ => le_max_left 0 (S j)) hi).trans (le_max_right _ _))
  refine ⟨T, hT₀, ?_⟩
  intro t ht x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hI hx)
  have hEq : EqOn (f t) (g t) (N i) := by
    apply chart_branches_eq_on_connected (x := i.1)
      (hΦ t (hT₀.trans ht)) isPreconnected_connectedComponentIn
      ((hf t (hT₀.trans ht)).mono (fun y hy => (hNs i hy).1))
      ((hg t (hT₀.trans ht)).mono (fun y hy => (hNs i hy).2))
    · exact fun y hy => hfball t (hT₀.trans ht) y (hNs i hy).1
    · exact fun y hy => hgball t (hT₀.trans ht) y (hNs i hy).2
    · exact fun y hy => hproj t (hT₀.trans ht) y (hNs i hy)
    · exact hNx i
    · exact hS i t ((hTi i hi).trans ht)
  exact hEq hxi

end Yau.Proofs.C07Aux
