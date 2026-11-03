import Yau.Proofs.P04WeightedInterpolation
import Yau.Proofs.P04CanonicalGrowth
import Yau.Proofs.P04CountableSections
import Yau.Proofs.P04CanonicalMajorant

noncomputable section
open MeasureTheory
open scoped Topology Manifold ContDiff ENNReal ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

/-- The same actual weight and volume produce the entire nonvanishing
family with its actual norm and logarithmic distance bounds. -/
theorem canonical_sections_of_actual_inputs (X : KahlerManifold n) (o : Yau.Blueprint.Pt X)
    (ψ : Yau.Blueprint.Pt X → ℝ) (hψ : IsSmoothStrictPsh ψ) (Cψ : ℝ)
    (hψupper : ∀ y, ψ y ≤ Cψ*(1+distFrom X.metric.form o y))
    (μ : Measure (Yau.Blueprint.Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (hRic : ∀ x, (ricci X.metric.form x).PosSemidef) :
    ∀ p : Yau.Blueprint.Pt X, ∃ S : CanonicalSection X.manifold, IsHolomorphicCanonical S ∧ S p ≠ 0 ∧
      ∃ C : ℝ, ∀ y, canonicalNormSq X.metric.form S y ≤ Real.exp (C*(1+distFrom X.metric.form o y)) ∧
        Real.log (canonicalNormSq X.metric.form S y) ≤ C*(1+distFrom X.metric.form o y) := by
  intro p
  obtain ⟨k,hk,S,hS,hSp,hfinite⟩ := canonical_weighted_interpolation X.metric hψ μ hμ p
  obtain ⟨C,_hC,hgrowth⟩ := canonical_growth_of_weighted_norm X.metric hRic
    μ hμ o S hS ψ Cψ hψupper hk.le hfinite
  exact ⟨S,hS,hSp,C,hgrowth⟩

/-- Conditional internal assembly only: the explicit inputs below are
discharged by the actual canonical ancestor proofs in the final wrapper. -/
theorem canonical_initial_data_of_actual_inputs (X : KahlerManifold n) (o : Yau.Blueprint.Pt X)
    (ψ : Yau.Blueprint.Pt X → ℝ) (hψ : IsSmoothStrictPsh ψ) (Cψ : ℝ)
    (hψupper : ∀ y, ψ y ≤ Cψ*(1+distFrom X.metric.form o y))
    (μ : Measure (Yau.Blueprint.Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (hRic : ∀ x, (ricci X.metric.form x).PosSemidef) :
    Yau.Blueprint.CanonicalInitialData X o := by
  have hsections := canonical_sections_of_actual_inputs X o ψ hψ Cψ hψupper μ hμ hRic
  constructor
  · intro p
    obtain ⟨S,hS,hSp,C,hgrowth⟩ := hsections p
    exact ⟨S,hS,hSp,C,fun y => (hgrowth y).2⟩
  · let P : CanonicalSection X.manifold → Prop := fun S =>
      ∃ C : ℝ, ∀ y, canonicalNormSq X.metric.form S y ≤ Real.exp (C*(1+distFrom X.metric.form o y))
    have hex (p : Yau.Blueprint.Pt X) : ∃ S : CanonicalSection X.manifold,
        P S ∧ IsHolomorphicCanonical S ∧ S p ≠ 0 := by
      obtain ⟨S,hS,hSp,C,hgrowth⟩ := hsections p
      exact ⟨S,⟨C,fun y => (hgrowth y).1⟩,hS,hSp⟩
    obtain ⟨S,hS,hcover⟩ := countable_nonvanishing_sections X.metric P hex
    choose C hC using fun i => (hS i).1
    exact canonical_family_ricci_majorant X.metric o S (fun i => (hS i).2) hcover C hC

end Yau.Proofs.P04Aux
