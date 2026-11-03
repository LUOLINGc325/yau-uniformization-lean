import Yau.Proofs.C07LocalInversion

open scoped Manifold Topology

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- The original chart is locally one-to-one throughout its ball, with no
global injectivity assumption. -/
theorem localBiholomorphism_locallyInjectiveOn
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r) :
    IsLocallyInjective (fun z : Metric.ball (0 : ComplexVector n) r => Φ z) := by
  intro z
  obtain ⟨e, hez, _, heq⟩ := local_homeomorph_of_localBiholomorphism hΦ z.property
  refine ⟨Subtype.val ⁻¹' e.source, e.open_source.preimage continuous_subtype_val, hez, ?_⟩
  intro a ha b hb hab
  apply Subtype.ext
  apply e.injOn ha hb
  rw [heq ha, heq hb]
  exact hab

/-- Continuous lifts on a connected parameter space agree everywhere as
soon as they agree once.  This applies both to paths and to overlaps in the
inverse-branch construction. -/
theorem chart_lifts_unique {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r)
    {g₁ g₂ : A → ComplexVector n} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (hb₁ : ∀ a, g₁ a ∈ Metric.ball 0 r) (hb₂ : ∀ a, g₂ a ∈ Metric.ball 0 r)
    (hcomp : Φ ∘ g₁ = Φ ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := by
  let p : Metric.ball (0 : ComplexVector n) r → M.Carrier := fun z => Φ z
  let G₁ : A → Metric.ball (0 : ComplexVector n) r := fun x => ⟨g₁ x, hb₁ x⟩
  let G₂ : A → Metric.ball (0 : ComplexVector n) r := fun x => ⟨g₂ x, hb₂ x⟩
  have heq : G₁ = G₂ := (T2Space.isSeparatedMap p).eq_of_comp_eq
    (localBiholomorphism_locallyInjectiveOn hΦ)
    (h₁.subtype_mk hb₁) (h₂.subtype_mk hb₂) hcomp a (Subtype.ext ha)
  exact funext fun x => congrArg Subtype.val (congrFun heq x)

end Yau.Proofs.C07Aux
