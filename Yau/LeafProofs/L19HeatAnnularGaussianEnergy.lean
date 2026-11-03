import Yau.LeafProofs.L19HeatAnnularEnergyBounds

/-! Derived annular energy growth and decay for the actual heat equations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- Every original positive heat solution has arbitrarily small Gaussian
annular scalar and gradient energy growth on a strictly positive slab. -/
theorem positiveHeatSolution_annular_gaussian_energy_growth
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution g.form u) (o : M.Carrier)
    {s T ε : ℝ} (hs : 0 < s) (hsT : s ≤ T) (hε : 0 < ε) :
    ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ ∀ R : ℝ, 1 ≤ R →
      (∀ t ∈ Icc s T,
        (∫ x in {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R},
          u x t ^ 2 ∂μ) ≤ D * Real.exp (ε * R ^ 2)) ∧
      (∫ t in s..T, ∫ x in {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R},
        scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x ∂μ) ≤
        E * Real.exp (ε * R ^ 2) := by
  let a := ε / 48
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨C, hC, hgrowth⟩ := positiveHeatSolution_uniform_slab_growth g hcomplete hK hRic hu o hs hsT ha
  let D := C ^ 2 * ∫ x, gaussianWeight g o a x ∂μ
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _)
    (integral_nonneg fun x => (gaussianWeight_pos g o a x).le)
  obtain ⟨A, hA, henergy⟩ := exists_uniform_annular_heat_energy_from_square_bound n
  let E := (2 + A * (T - s)) * D
  have hE : 0 ≤ E := mul_nonneg (by positivity) hD
  refine ⟨D, E, hD, hE, ?_⟩
  intro R hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hL2 (t : ℝ) (ht : t ∈ Icc s T) :
      (∫ x in {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R},
        u x t ^ 2 ∂μ) ≤ D * Real.exp (ε * R ^ 2) := by
    have hh := integralOn_sq_gaussian_growth_bound g hK hRic μ hμ o ha hC.le
      (show 0 ≤ 4 * R by positivity) (smoothSpaceTime_slice hu.1 (hs.trans_le ht.1))
      (scalarHeat_annulus_isCompact g o (R / 2) (4 * R)) (fun x hx => hx.2)
      (fun x => by rw [abs_of_pos (hu.2 x t (hs.trans_le ht.1)).1]; exact hgrowth t ht x)
    have he : 3 * a * (4 * R) ^ 2 = ε * R ^ 2 := by dsimp only [a]; ring
    rw [he] at hh
    exact hh.trans_eq (by dsimp only [D]; ring)
  refine ⟨hL2, ?_⟩
  have hh := henergy M g hK μ hμ (Ioi 0) isOpen_Ioi u hu.1
    (Or.inl fun x t ht => positiveHeatSolution_hasDerivAt g.form hu x ht)
    o R s T (D * Real.exp (ε * R ^ 2)) hR
    (fun t ht => hs.trans_le ht.1) hsT (mul_nonneg hD (Real.exp_pos _).le) hL2
  exact hh.trans_eq (by dsimp only [E]; ring)

/-- Pointwise Gaussian decay of a genuine heat flow gives Gaussian
annular scalar and gradient energy decay in either time direction. -/
theorem scalarHeat_annular_gaussian_energy_decay
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {I : Set ℝ} (hI : IsOpen I)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u I)
    (hheat : (∀ y t, t ∈ I → HasDerivAt (u y) (laplacian g.form (fun z => u z t) y) t) ∨
      (∀ y t, t ∈ I → HasDerivAt (u y) (-laplacian g.form (fun z => u z t) y) t))
    (o : M.Carrier) {s T C β : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T)
    (hC : 0 < C) (hβ : 0 < β)
    (hdecay : ∀ x t, t ∈ Icc s T → |u x t| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2)) :
    ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ ∀ R : ℝ, 1 ≤ R →
      (∀ t ∈ Icc s T,
        (∫ x in {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R},
          u x t ^ 2 ∂μ) ≤ D * Real.exp (-(β / 4) * R ^ 2)) ∧
      (∫ t in s..T, ∫ x in {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R},
        scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x ∂μ) ≤
        E * Real.exp (-(β / 4) * R ^ 2) := by
  let D := C ^ 2 * ∫ x, gaussianWeight g o β x ∂μ
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _)
    (integral_nonneg fun x => (gaussianWeight_pos g o β x).le)
  obtain ⟨A, hA, henergy⟩ := exists_uniform_annular_heat_energy_from_square_bound n
  let E := (2 + A * (T - s)) * D
  have hE : 0 ≤ E := mul_nonneg (by positivity) hD
  refine ⟨D, E, hD, hE, ?_⟩
  intro R hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hL2 (t : ℝ) (ht : t ∈ Icc s T) :
      (∫ x in {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R},
        u x t ^ 2 ∂μ) ≤ D * Real.exp (-(β / 4) * R ^ 2) := by
    have hh := integralOn_sq_gaussian_decay_bound g hK hRic μ hμ o hβ hC.le
      (show 0 ≤ R / 2 by positivity) (smoothSpaceTime_slice hu (hslab ht))
      (scalarHeat_annulus_isCompact g o (R / 2) (4 * R)) (fun x hx => hx.1)
      (fun x => hdecay x t ht)
    have he : -β * (R / 2) ^ 2 = -(β / 4) * R ^ 2 := by ring
    rw [he] at hh
    exact hh.trans_eq (by dsimp only [D]; ring)
  refine ⟨hL2, ?_⟩
  have hh := henergy M g hK μ hμ I hI u hu hheat o R s T
    (D * Real.exp (-(β / 4) * R ^ 2)) hR hslab hsT
    (mul_nonneg hD (Real.exp_pos _).le) hL2
  exact hh.trans_eq (by dsimp only [E]; ring)

end Yau.LeafProofs.L19Aux
