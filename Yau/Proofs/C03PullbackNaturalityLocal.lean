import Yau.Proofs.C03PullbackNaturalityCoordinates

/-! The actual local coordinate map of a holomorphic immersion and the real
metric equality obtained from equality of the Hermitian pullback. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Yau Yau.LeafProofs.L12Aux
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem coordinate_domain_open
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {Φ : ComplexVector n → M.Carrier} (hΦ : ContinuousOn Φ O) (c : M.Carrier) :
    IsOpen (O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source) := by
  apply hΦ.isOpen_inter_preimage hO
  exact isOpen_extChartAt_source c

theorem coordinate_contDiff_complex
    {O : Set (ComplexVector n)} {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O) (c : M.Carrier) :
    ContDiffOn ℂ ∞ (fun z => chartPt c (Φ z))
      (O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source) := by
  simpa only [chartPt, extChartAt_source, Function.comp_def] using
    ((contMDiffOn_extChartAt (I := ComplexModel n) (x := c) (n := ∞)).comp
    (hΦ.mono Set.inter_subset_left) (fun _ hz => hz.2)).contDiffOn

theorem coordinate_contDiff_real
    {O : Set (ComplexVector n)} {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => chartPt c (Φ z))
      (O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source) :=
  (coordinate_contDiff_complex hΦ c).restrict_scalars ℝ

theorem coordinate_fderiv_real
    {Φ : ComplexVector n → M.Carrier} {z : ComplexVector n} (c : M.Carrier)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source)
    (hf : DifferentiableAt ℂ (fun p => chartPt c (Φ p)) z) (u : ComplexVector n) :
    fderiv ℝ (fun p => chartPt c (Φ p)) z u =
      tangentCoords c (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z u) := by
  rw [hf.fderiv_restrictScalars ℝ]
  exact coordinate_fderiv_complex c hΦ hy u

theorem coordinate_fderiv_I
    {f : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hf : DifferentiableAt ℂ f z) (u : ComplexVector n) :
    fderiv ℝ f z (Complex.I • u) = Complex.I • fderiv ℝ f z u := by
  rw [hf.fderiv_restrictScalars ℝ]
  exact (fderiv ℂ f z).map_smul Complex.I u

theorem coordinate_fderiv_bijective
    {Φ : ComplexVector n → M.Carrier} {z : ComplexVector n} (c : M.Carrier)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source)
    (hf : DifferentiableAt ℂ (fun p => chartPt c (Φ p)) z)
    (hbij : Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z)) :
    Function.Bijective (fderiv ℝ (fun p => chartPt c (Φ p)) z) := by
  have ht : Function.Bijective (tangentCoords c (Φ z)) := by
    constructor
    · intro U V he
      simpa only [chartVec_tangentCoords c (Φ z) hy] using congrArg (chartVec c (Φ z)) he
    · intro v
      exact ⟨chartVec c (Φ z) v, tangentCoords_chartVec c (Φ z) hy v⟩
  have he : (fun u => fderiv ℝ (fun p => chartPt c (Φ p)) z u) =
      (tangentCoords c (Φ z)) ∘ mfderiv (ComplexModel n) (ComplexModel n) Φ z := by
    funext u
    exact coordinate_fderiv_real c hΦ hy hf u
  change Function.Bijective (fun u => fderiv ℝ (fun p => chartPt c (Φ p)) z u)
  rw [he]
  exact ht.comp hbij

theorem realMetric_pullback
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (h : HermitianField M) {Φ : ComplexVector n → M.Carrier}
    {z : (ComplexEuclideanManifold n hn).Carrier} (c : M.Carrier)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source)
    (hf : DifferentiableAt ℂ (fun p => chartPt c (Φ p)) z)
    (heq : ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v))
    (u v : ComplexVector n) :
    realMetricInChart k (0 : ComplexVector n) z u v =
      realMetricInChart h c (chartPt c (Φ z))
        (fderiv ℝ (fun p => chartPt c (Φ p)) z u)
        (fderiv ℝ (fun p => chartPt c (Φ p)) z v) := by
  rw [source_realMetric hn k z u v, heq u v,
    coordinate_fderiv_real c hΦ hy hf u, coordinate_fderiv_real c hΦ hy hf v,
    target_realMetric_pair h c (Φ z) hy]

end Yau.Proofs.C03Aux.PullbackNaturality
