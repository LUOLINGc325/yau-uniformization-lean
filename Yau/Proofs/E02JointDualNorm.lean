import Yau.Proofs.E02EnvelopeDomain
import Yau.Proofs.V03MetricTime

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

variable {n : ℕ} (X : KahlerManifold n)

/-- Smoothness uses the genuine one-sided metric time domain and the
original chart; the two physical product associations are explicit. -/
theorem jointDualNorm_contDiffOn (h : Flow X)
    (hh : MetricFamilySmooth h (Ici 0)) (T : ℝ) (x : Pt X) :
    ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ComplexVector n × ℝ =>
        dualNormChart (h p.2.2) x p.1 p.2.1) (envelopeDomain X T x) := by
  have he : ContDiff ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℝ =>
      ((p.1,p.2.1),p.2.2)) :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
      (contDiff_snd.comp contDiff_snd)
  exact (V03Proof.metricFamily_dualNormChart_contDiffOn hh x).comp he.contDiffOn
    (fun p hp => ⟨⟨hp.1,mem_univ _⟩,hp.2.1.le⟩)

/-- The compact upper bound comes from the actual smooth metric norm.
It is selected before the inf-convolution parameter. -/
theorem jointDualNorm_compact_upper (h : Flow X)
    (hh : MetricFamilySmooth h (Ici 0)) (T : ℝ) (x : Pt X)
    (K : Set (ComplexVector n × ComplexVector n × ℝ))
    (hK : IsCompact K) (hDom : K ⊆ envelopeDomain X T x) :
    ∃ M : ℝ, 0 < M ∧ ∀ p ∈ K, dualNormChart (h p.2.2) x p.1 p.2.1 ≤ M := by
  have hc := (jointDualNorm_contDiffOn X h hh T x).continuousOn.mono hDom
  obtain ⟨C,hC⟩ := hK.bddAbove_image hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro p hp
  exact (hC (mem_image_of_mem _ hp)).trans
    ((le_max_left C 0).trans (by linarith))

end Yau.NodeProofs.E02Aux
