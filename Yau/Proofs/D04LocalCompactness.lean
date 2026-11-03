import Yau.Proofs.D04RepresentativePsh

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem eventually_uniform_lt_of_representative_lt
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {u : ℕ → ComplexVector n → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    {f : ComplexVector n → ℝ}
    (hf : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O →
      Tendsto (fun j => ∫ y in S, |(u j y).toReal - f y|) atTop (𝓝 0))
    {K : Set (ComplexVector n)} (hK : IsCompact K) {a : ℝ}
    (hstrict : ∀ x ∈ K, uscRepresentative O f x < (a : EReal)) :
    ∀ᶠ j in atTop, ∀ x ∈ K, u j x < (a : EReal) := by
  classical
  have hloc (x : K) := eventually_locally_lt_of_uscRepresentative_lt hO hu hf hconv (hstrict x x.2)
  choose r hr hRO he using hloc
  choose N hN using fun x => eventually_atTop.mp (he x)
  let U : K → Set (ComplexVector n) := fun x => Metric.ball x (r x)
  have hcover : K ⊆ ⋃ x, U x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  refine eventually_atTop.mpr ⟨s.sup N, ?_⟩
  intro j hj x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨his, hix⟩ := mem_iUnion.mp hi
  exact hN i j ((Finset.le_sup his).trans hj) x (Metric.ball_subset_closedBall hix)

theorem erealDist_eq_ofReal_of_finite {a b : EReal}
    (hatop : a ≠ ⊤) (habot : a ≠ ⊥) (hbtop : b ≠ ⊤) (hbbot : b ≠ ⊥) :
    erealDist a b = ENNReal.ofReal |a.toReal - b.toReal| := by
  by_cases h : a = b
  · subst b
    simp [erealDist]
  · simp only [erealDist, ite_eq_right h, habot, hatop, hbbot, hbtop, or_self,
      ite_false]

/-- Finite-a.e. facts upgrade convergence of real pairings to the frozen
extended-real distance, without treating infinite values as zero. -/
theorem tendsto_lintegral_erealDist
    {u : ℕ → ComplexVector n → EReal} {v : ComplexVector n → EReal}
    {K : Set (ComplexVector n)}
    (hu : ∀ j, (∀ᵐ y ∂volume.restrict K, u j y ≠ ⊥ ∧ u j y ≠ ⊤) ∧
      IntegrableOn (fun y => (u j y).toReal) K volume)
    (hv : (∀ᵐ y ∂volume.restrict K, v y ≠ ⊥ ∧ v y ≠ ⊤) ∧
      IntegrableOn (fun y => (v y).toReal) K volume)
    (hconv : Tendsto (fun j => ∫ y in K, |(u j y).toReal - (v y).toReal|) atTop (𝓝 0)) :
    Tendsto (fun j => ∫⁻ y in K, erealDist (u j y) (v y)) atTop (𝓝 0) := by
  have heq (j : ℕ) : (∫⁻ y in K, erealDist (u j y) (v y)) =
      ENNReal.ofReal (∫ y in K, |(u j y).toReal - (v y).toReal|) := by
    have hi : IntegrableOn (fun y => |(u j y).toReal - (v y).toReal|) K volume := by
      simpa only [IntegrableOn, Real.norm_eq_abs, Pi.sub_apply] using ((hu j).2.sub hv.2).norm
    calc
      _ = ∫⁻ y in K, ENNReal.ofReal |(u j y).toReal - (v y).toReal| := by
        apply lintegral_congr_ae
        filter_upwards [(hu j).1, hv.1] with y hy hvy
        exact erealDist_eq_ofReal_of_finite hy.2 hy.1 hvy.2 hvy.1
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  simp_rw [heq]
  simpa only [ENNReal.ofReal_zero, Function.comp_def] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv

/-- Full fixed-domain compactness in arbitrary complex dimension, including
the same EReal representative, actual extended-real L¹ distance, and the
constant-limit Hartogs bound. Varying-domain exhaustion is assembled later. -/
theorem coordinate_psh_L1_compactness
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {u : ℕ → ComplexVector n → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    (hbound : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ y in K, |(u j y).toReal| ≤ B) :
    ∃ (σ : ℕ → ℕ) (v : ComplexVector n → EReal), StrictMono σ ∧ IsPshOn v O ∧
      CoordinateLocallyL1Converges O (fun j => u (σ j)) v ∧
      (∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O →
        Tendsto (fun j => ∫⁻ y in K, erealDist (u (σ j) y) (v y)) atTop (𝓝 0)) ∧
      (∀ c : ℝ, (∀ y ∈ O, v y = (c : EReal)) →
        ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ j in atTop, ∀ y ∈ K, u (σ j) y ≤ ((c + ε : ℝ) : EReal)) := by
  obtain ⟨σ, f, hσ, hf, hconv⟩ := psh_exists_real_L1_limit hO hu hbound
  have hsub : ∀ j, IsPshOn (u (σ j)) O ∧ CoordinateLocallyL1 O (u (σ j)) := fun j => hu (σ j)
  have hbound' : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ y in K, |(u (σ j) y).toReal| ≤ B := by
    intro K hK hKO
    obtain ⟨B, hB⟩ := hbound K hK hKO
    exact ⟨B, fun j => hB (σ j)⟩
  have hL1 := uscRepresentative_locallyL1Converges hO hsub hbound' hf hconv
  refine ⟨σ, uscRepresentative O f, hσ, uscRepresentative_isPshOn hO hsub hf hconv, hL1, ?_, ?_⟩
  · intro K hK hKO
    exact tendsto_lintegral_erealDist (fun j => (hsub j).2 K hK hKO) (hL1.1 K hK hKO)
      (hL1.2 K hK hKO)
  · intro c hc K hK hKO ε hε
    have hstrict : ∀ x ∈ K, uscRepresentative O f x < ((c + ε : ℝ) : EReal) := by
      intro x hx
      rw [hc x (hKO hx)]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    exact (eventually_uniform_lt_of_representative_lt hO hsub hf hconv hK hstrict).mono
      (fun j hj y hy => (hj y hy).le)

end Yau.Proofs.D04Aux
