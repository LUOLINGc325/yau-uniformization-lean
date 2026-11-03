import Yau.Proofs.C01FirstExitPaths

/-! Actual distances and the additive extended lengths of smooth
segments, without completeness of the metric field. -/

noncomputable section
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem distance_le_smooth_segment_length
    (k : HermitianField M) (hk : MetricSmooth k) (f : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ∀ (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f)
      (a b : ℝ), a ≤ b →
      ENNReal.ofReal (inducedDistance k (f a) (f b)) ≤ actualPathELength k f a b := by
  letI := manifold_realSmooth M
  intro hf a b hab
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  change ENNReal.ofReal (inducedDistance k (f a) (f b)) ≤
    Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b
  rw [inducedDistance_eq_riemannianEDist k hk]
  exact riemannianEDist_le_pathELength_of_contMDiffAt_Ioo k hk hab
    hf.continuous.continuousOn (fun s _ => hf.contMDiffAt)

theorem actualPathELength_add (k : HermitianField M) (f : ℝ → M.Carrier)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    actualPathELength k f a b + actualPathELength k f b c = actualPathELength k f a c := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  exact Manifold.pathELength_add hab hbc

theorem actualPathELength_mono (k : HermitianField M) (f : ℝ → M.Carrier)
    {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    actualPathELength k f a b ≤ actualPathELength k f a' b' := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  exact Manifold.pathELength_mono ha hb

theorem actualPathELength_full_of_contMDiff (k : HermitianField M) (hk : MetricSmooth k)
    (f : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ∀ hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f,
      actualPathELength k f 0 1 = ENNReal.ofReal (curveLength k (piecewiseC1Curve_of_contMDiff hf)) := by
  letI := manifold_realSmooth M
  intro hf
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  exact (curveLength_eq_pathELength k (integrableCurve_of_contMDiff k hk hf)).symm

end Yau.NodeProofs.C01Aux
