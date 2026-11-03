import Yau.Proofs.F04InitialCaccioppoli

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

theorem initial_gradient_estimate {n : ℕ} {O : Set (Space n)}
    {S lam upper : ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hsmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hell : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    (V₀ V₁ : Set (Space n)) (s : ℝ)
    (hV₀ : IsOpen V₀) (hV₀c : IsCompact (closure V₀)) (hV₀V₁ : closure V₀ ⊆ V₁)
    (hV₁ : IsOpen V₁) (hV₁c : IsCompact (closure V₁)) (hV₁O : closure V₁ ⊆ O)
    (hs : 0 < s) (hsS : s < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 ≤ K → ∀ u : Point n → ℝ,
      ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S) →
      (∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0) →
      (∀ x ∈ V₁, ∀ t ∈ Ioo 0 s, |u (x, t)| ≤ K * t) →
      Integrable (fun p => dgGradientSq (dgGradient u p)) (productVolume V₀ (Ioo 0 s)) ∧
        (∫ p, dgGradientSq (dgGradient u p) ∂productVolume V₀ (Ioo 0 s)) ≤ C * K ^ 2 * s ^ 3 := by
  have hV₁sub : V₁ ⊆ O := fun x hx => hV₁O (subset_closure hx)
  have hV₀sub : V₀ ⊆ V₁ := fun x hx => hV₀V₁ (subset_closure hx)
  have hKsub : closure V₁ ×ˢ Icc (0 : ℝ) S ⊆ O ×ˢ Icc 0 S :=
    Set.prod_mono hV₁O (Subset.refl _)
  have hKsm : SmoothCoefficients (closure V₁ ×ˢ Icc 0 S) a b :=
    ⟨hsmooth.1.mono hKsub, fun i => (hsmooth.2 i).mono hKsub⟩
  have hVsm : SmoothCoefficients (V₁ ×ˢ Icc 0 S) a b :=
    ⟨hKsm.1.mono (Set.prod_mono subset_closure (Subset.refl _)),
      fun i => (hKsm.2 i).mono (Set.prod_mono subset_closure (Subset.refl _))⟩
  obtain ⟨D, hD, hDrift⟩ := compact_buffer_drift_bound hV₁ hV₁c hKsm
  obtain ⟨η, M, hη, hcη, hηV, hηrange, hηone, hM, hηM⟩ :=
    spatial_energy_cutoff hV₀c hV₁ hV₀V₁
  let C0 : ℝ := (2 + 8 * upper ^ 2 / lam + 2 * D ^ 2 / lam) * M * volume.real V₁ / lam
  have hLam : 0 < lam := hell.1
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  refine ⟨1 + C0, by linarith, ?_⟩
  intro K hK u hu heq hbound
  have hsub : V₁ ×ˢ Ioo (0 : ℝ) S ⊆ O ×ˢ Ioo 0 S :=
    Set.prod_mono hV₁sub (Subset.refl _)
  have huV := hu.mono hsub
  have heqV : ∀ p ∈ V₁ ×ˢ Ioo 0 S, linearOp (V₁ ×ˢ Icc 0 S) a b u p = 0 := by
    intro p hp
    have hh := heq p (hsub hp)
    change linearOp (cylinder O 0 S) a b u p = 0 at hh
    change linearOp (cylinder V₁ 0 S) a b u p = 0
    rw [linearOp_cylinder_restrict_space a b u
      (show p ∈ cylinder O 0 S from ⟨hV₁sub hp.1, Ioo_subset_Icc_self hp.2⟩)] at hh
    rw [linearOp_cylinder_restrict_space a b u
      (show p ∈ cylinder V₁ 0 S from ⟨hp.1, Ioo_subset_Icc_self hp.2⟩)]
    exact hh
  have hfields := homogeneous_classical_fields hV₁ hVsm huV
  have hclass := homogeneous_classical_divergence hV₁ hVsm huV heqV
  have hb : DGUniformBounds (V₁ ×ˢ Ioo 0 S) a (energyDrift a b) (fun _ => 0) lam upper D 0 := by
    refine ⟨⟨hell.1, hell.2.1, ?_⟩, hDrift, ?_⟩
    · exact fun p hp => hell.2.2 p ⟨hV₁sub hp.1, Ioo_subset_Icc_self hp.2⟩
    · exact fun _ _ => by simp only [abs_zero, le_refl]
  have hweighted := initial_gradient_cutoff_bound hV₁ hV₁c hs hsS hell.1 hD.le hM
    hη hcη hηV hηrange hηM hK hfields hclass hb hbound
  have hμ : productVolume V₀ (Ioo (0 : ℝ) s) ≤ productVolume V₁ (Ioo 0 s) :=
    Measure.prod_mono (Measure.restrict_mono_set volume hV₀sub) le_rfl
  have hInt0 := hweighted.1.mono_measure hμ
  have heq0 : (fun p => dgGradientSq (dgGradient u p)) =ᵐ[productVolume V₀ (Ioo 0 s)]
      (fun p => dgGradientSq (dgGradient u p) * (η p.1) ^ 2) := by
    rw [dg_productVolume_eq_restrict]
    filter_upwards [ae_restrict_mem (hV₀.prod isOpen_Ioo).measurableSet] with p hp
    rw [hηone p.1 (subset_closure hp.1), one_pow, mul_one]
  refine ⟨hInt0.congr (Filter.EventuallyEq.symm heq0), ?_⟩
  rw [integral_congr_ae heq0]
  calc
    _ ≤ ∫ p, dgGradientSq (dgGradient u p) * (η p.1) ^ 2 ∂productVolume V₁ (Ioo 0 s) :=
      integral_mono_measure hμ
        (.of_forall (fun p => mul_nonneg (dgGradientSq_nonneg _) (sq_nonneg _))) hweighted.1
    _ ≤ C0 * K ^ 2 * s ^ 3 := hweighted.2
    _ ≤ (1 + C0) * K ^ 2 * s ^ 3 := by
      have hh : 0 ≤ K ^ 2 * s ^ 3 := by positivity
      nlinarith only [hh]

end Yau.F04Proof
