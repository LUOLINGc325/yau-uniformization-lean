import Yau.Proofs.P03AffineSchurCharts

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The explicit affine row charts have lower dimension whenever the
spatial and projective variables have dimension below twice the row count. -/
theorem dense_compl_affineSchurChart_image (a : E → ι → ℂ) (pivot : ι)
    (b : E → Fin m → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ l, DifferentiableOn ℝ (fun x => a x l) U)
    (hb : ∀ i, DifferentiableOn ℝ (fun x => b x i) U)
    (hdim : Module.finrank ℝ E < m * 2) :
    Dense (affineSchurChart a pivot b '' {p | p.1 ∈ U ∧ a p.1 pivot ≠ 0})ᶜ := by
  apply dense_compl_lower_dimensional_image
    (affineSchurChart_differentiableOn a pivot b hU ha hb)
  have htarget : Module.finrank ℝ (Fin m → ι → ℂ) = m * Fintype.card ι * 2 := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨pivot⟩
  rw [Module.finrank_prod, affineSchurFreeRows_finrank, htarget]
  calc
    Module.finrank ℝ E + m * (Fintype.card ι - 1) * 2 <
        m * 2 + m * (Fintype.card ι - 1) * 2 := Nat.add_lt_add_right hdim _
    _ = m * ((Fintype.card ι - 1) + 1) * 2 := by ring
    _ = m * Fintype.card ι * 2 := by rw [Nat.sub_add_cancel hcard]

/-- Finite coverage by genuine lower-dimensional parameter charts gives
density of the actual good parameter set. -/
theorem dense_good_of_finite_bad_charts {J : Type*} [Fintype J]
    (D : J → Type*) [∀ j, NormedAddCommGroup (D j)] [∀ j, NormedSpace ℝ (D j)]
    [∀ j, FiniteDimensional ℝ (D j)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ∀ j, Set (D j)) (f : ∀ j, D j → F)
    (hf : ∀ j, DifferentiableOn ℝ (f j) (s j))
    (hd : ∀ j, Module.finrank ℝ (D j) < Module.finrank ℝ F)
    {G : Set F} (hcover : Gᶜ ⊆ ⋃ j, f j '' s j) : Dense G := by
  apply (dense_compl_finite_lower_dimensional_images D s f hf hd).mono
  intro x hx
  by_contra hbad
  exact hx (hcover hbad)

end Yau.NodeProofs.P03Aux
