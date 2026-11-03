import Yau.Proofs.D04RepresentativeUpper

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- The representative's circle bound yields one eventual bound on a thin
translated circle neighborhood. The test is controlled only on `[0,2π]`,
as justified by `intervalMajorant_submean`. -/
theorem eventually_shifted_circle_upper
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {u : ℕ → ComplexVector n → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    {f : ComplexVector n → ℝ}
    (hf : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O →
      Tendsto (fun j => ∫ y in S, |(u j y).toReal - f y|) atTop (𝓝 0))
    (z w : ComplexVector n) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hmajor : ∀ θ ∈ Icc 0 (2 * Real.pi),
      uscRepresentative O f (z + Complex.exp (θ * Complex.I) • w) ≤ (φ θ : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, ∀ a : ComplexVector n, ‖a‖ < δ →
      ∀ θ ∈ Icc 0 (2 * Real.pi),
        u j (z + Complex.exp (θ * Complex.I) • w - a) ≤ ((φ θ + ε : ℝ) : EReal) := by
  classical
  let c : ℝ → ComplexVector n := fun θ => z + Complex.exp (θ * Complex.I) • w
  have hc : Continuous c := by fun_prop
  have hloc (θ : Icc (0 : ℝ) (2 * Real.pi)) :
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall (c θ) r ⊆ O ∧
        ∀ᶠ j in atTop, ∀ y ∈ Metric.closedBall (c θ) r,
          u j y < ((φ θ + ε / 2 : ℝ) : EReal) := by
    apply eventually_locally_lt_of_uscRepresentative_lt hO hu hf hconv
    exact (hmajor θ θ.2).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  choose r hr hRO he using hloc
  choose N hN using fun θ => eventually_atTop.mp (he θ)
  let U : Icc (0 : ℝ) (2 * Real.pi) → Set (ℝ × ComplexVector n) := fun θ =>
    {p | dist (c p.1 - p.2) (c θ) < r θ ∧ φ θ + ε / 2 < φ p.1 + ε}
  have hUopen (θ : Icc (0 : ℝ) (2 * Real.pi)) : IsOpen (U θ) :=
    (isOpen_lt (((hc.comp continuous_fst).sub continuous_snd).dist continuous_const)
      continuous_const).inter
      (isOpen_lt continuous_const ((hφ.comp continuous_fst).add continuous_const))
  have hUbase (θ : Icc (0 : ℝ) (2 * Real.pi)) : ((θ : ℝ), (0 : ComplexVector n)) ∈ U θ := by
    change dist (c θ - 0) (c θ) < r θ ∧ φ θ + ε / 2 < φ θ + ε
    simp only [sub_zero, dist_self]
    exact ⟨hr θ, by linarith⟩
  have hcover : (Icc (0 : ℝ) (2 * Real.pi) ×ˢ {(0 : ComplexVector n)}) ⊆ ⋃ θ, U θ := by
    rintro ⟨θ, a⟩ ⟨hθ, ha⟩
    have ha0 : a = 0 := mem_singleton_iff.mp ha
    subst a
    exact mem_iUnion.mpr ⟨⟨θ, hθ⟩, hUbase ⟨θ, hθ⟩⟩
  obtain ⟨s, hs⟩ := (isCompact_Icc.prod isCompact_singleton).elim_finite_subcover U hUopen hcover
  let V : Set (ℝ × ComplexVector n) := ⋃ θ ∈ s, U θ
  have hVopen : IsOpen V := isOpen_biUnion fun θ _ => hUopen θ
  have hVbase (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) : (θ, (0 : ComplexVector n)) ∈ V :=
    hs ⟨hθ, mem_singleton 0⟩
  have hnear : ∀ᶠ a : ComplexVector n in 𝓝 0, ∀ θ ∈ Icc 0 (2 * Real.pi), (θ, a) ∈ V := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro θ hθ
    have hswap : Continuous (fun p : ComplexVector n × ℝ => (p.2, p.1)) :=
      continuous_snd.prodMk continuous_fst
    exact (hswap.tendsto (0, θ)).eventually (hVopen.mem_nhds (hVbase θ hθ))
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, eventually_atTop.mpr ⟨s.sup N, ?_⟩⟩
  intro j hj a ha θ hθ
  have haδ : a ∈ Metric.ball (0 : ComplexVector n) δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hδV haδ θ hθ)
  obtain ⟨his, hp⟩ := mem_iUnion.mp hi
  have hupper := hN i j ((Finset.le_sup his).trans hj)
    (c θ - a) (Metric.mem_closedBall.mpr hp.1.le)
  exact hupper.le.trans (EReal.coe_le_coe_iff.mpr hp.2.le)

end Yau.Proofs.D04Aux
