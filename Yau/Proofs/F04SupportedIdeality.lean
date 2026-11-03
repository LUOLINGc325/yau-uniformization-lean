import Yau.Proofs.F04AmbientNonnegativeCore
import Yau.Proofs.F04ShiftPositiveBounds
import Yau.Proofs.F04LpIdeality

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux
  Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- The supported closed energy space is an ideal for positive truncation
against any nonnegative element of the genuine ambient energy completion. -/
theorem dirichletEnergy_ambient_shift_posPart
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    ∃ v : DirichletEnergy g μ hμ O,
      scalarEnergyL2 g μ hμ v.val =
        Lp.posPart (scalarEnergyL2 g μ hμ u.val - scalarEnergyL2 g μ hμ q) ∧
      ‖v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + ‖scalarEnergyD g μ hμ O q‖ ^ 2 := by
  let := dirichletEnergy_completeSpace g μ hμ O
  obtain ⟨fs, hfn, hfs⟩ := exists_nonnegative_scalarEnergyDomain_tendsto g hK μ hμ q hq
  let J := dirichletL2 g μ hμ O
  let D := scalarEnergyD g μ hμ O
  let qH := fun j => l2Restriction μ O (scalarEnergyL2 g μ hμ (fs j : ScalarEnergySpace g μ hμ))
  let rH := l2Restriction μ O (scalarEnergyL2 g μ hμ q)
  have hr2 (j : ℕ) : ScalarL2 (μ.restrict O) (fs j) :=
    (scalarL2_iff_memLp _ _).mpr ((scalarEnergyDomain_memLp g μ hμ (fs j)).restrict O)
  have hdr2 (j : ℕ) : L2RealForm g.form (μ.restrict O) (scalarExterior (fs j)) :=
    scalarExterior_l2_restrict g μ hμ O (fs j).2.1 (fs j).2.2
  have hH (j : ℕ) : scalarToLp (hr2 j) = qH j := by
    dsimp only [qH]
    rw [scalarEnergyL2_coe]
    apply Lp.ext
    filter_upwards [scalarToLp_coe (hr2 j),
      restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ (fs j)),
      ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ (fs j))] with x hs hr hf
    exact hs.trans (hf.symm.trans hr.symm)
  let w : ℕ → DirichletEnergy g μ hμ O := fun j =>
    dirichletShiftPosPart g μ hμ O hO (fs j) (fs j).2.1
      (fun x _ => hfn j x) (hr2 j) (hdr2 j) u
  have hwJ (j : ℕ) : J (w j) = Lp.posPart (J u - qH j) := by
    rw [(dirichletShiftPosPart_spec g μ hμ O hO (fs j) (fs j).2.1
      (fun x _ => hfn j x) (hr2 j) (hdr2 j) u).1, hH]
  have hwN (j : ℕ) : ‖w j‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + ‖D (fs j : ScalarEnergySpace g μ hμ)‖ ^ 2 := by
    simpa only [D, scalarEnergyD_coe, scalarEnergyDomainD] using
      dirichletShiftPosPart_norm_sq_le g μ hμ O hO (fs j) (fs j).2.1
        (fun x _ => hfn j x) (hr2 j) (hdr2 j) u
  have hHlim : Tendsto qH atTop (𝓝 rH) :=
    (((l2Restriction μ O).continuous.comp (scalarEnergyL2 g μ hμ).continuous).tendsto q).comp hfs
  have hDlim := (D.continuous.tendsto q).comp hfs
  let z := Lp.posPart (J u - rH)
  have hstrong : Tendsto (fun j => J (w j)) atTop (𝓝 z) := by
    simpa only [hwJ, z, Function.comp_def] using (Lp.continuous_posPart.tendsto (J u - rH)).comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => J u) atTop (𝓝 (J u))).sub hHlim)
  let a : ℕ → ℝ := fun j => 2 * ‖u‖ ^ 2 + ‖D (fs j : ScalarEnergySpace g μ hμ)‖ ^ 2
  have ha : Tendsto a atTop (𝓝 (2 * ‖u‖ ^ 2 + ‖D q‖ ^ 2)) :=
    tendsto_const_nhds.add (hDlim.norm.pow 2)
  have hdb : ∀ᶠ j in atTop, ‖D (fs j : ScalarEnergySpace g μ hμ)‖ < ‖D q‖ + 1 :=
    (tendsto_order.mp hDlim.norm).2 _ (lt_add_one _)
  have hbound : ∀ᶠ j in atTop, ‖w j‖ ≤ 2 * ‖u‖ + ‖D q‖ + 1 := by
    filter_upwards [hdb] with j hj
    have hs := hwN j
    have hj2 := pow_le_pow_left₀ (norm_nonneg _) hj.le 2
    nlinarith [norm_nonneg (w j), norm_nonneg u, norm_nonneg (D q),
      mul_nonneg (norm_nonneg u) (norm_nonneg (D q))]
  obtain ⟨v, hvJ, hvN⟩ := hilbert_strong_image_limit J w z a
    (2 * ‖u‖ ^ 2 + ‖D q‖ ^ 2) (2 * ‖u‖ + ‖D q‖ + 1) hbound hstrong
    (Eventually.of_forall hwN) ha
  refine ⟨v, ?_, hvN⟩
  rw [← dirichletL2_zeroExtension g μ hμ O hO.measurableSet v, hvJ]
  have he := l2ZeroExtension_shift_posPart μ O hO.measurableSet
    (J u) (scalarEnergyL2 g μ hμ q) hq
  simpa only [J, z, rH, dirichletL2_zeroExtension g μ hμ O hO.measurableSet u] using he

end Yau.F04Proof
