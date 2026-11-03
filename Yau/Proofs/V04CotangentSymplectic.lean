import Yau.Proofs.D05FrameBivector
import Yau.Proofs.D05UniformBivector

/-! Actual cotangent transitions and the bivector of every given frame.
The accepted D05 argument controls the same ambient image Π_G on the
original compact boundary set; no selected frame is substituted. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}

theorem cotangentTransition_preserves_canonicalBivector
    (x x' : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    cotangentTransition x x' y * canonicalBivector * (cotangentTransition x x' y)ᵀ =
      (canonicalBivector : CotangentMatrix n) :=
  D05Proof.cotangentTransition_symplectic x x' y hy hy'

theorem frameBivector_fixed_chart (x : M.Carrier) (f : ℂ → CotangentPoint M)
    (E : ℂ → CotangentMatrix n) (z : ℂ) (hz : f z ∈ cotangentSource x) :
    frameBivector (frameInChart x f E z) = frameBivector (E z) :=
  D05Proof.frameBivector_in_fixed_chart x f E z hz

theorem normalizedFrame_bivector_contDiffOn {G : CotangentPoint M → ComplexVector q}
    {f : ℂ → CotangentPoint M} {E : ℂ → CotangentMatrix n}
    (hE : NormalizedDiscFrame G f E) (i j : CotangentIndex n) :
    ContDiffOn ℂ ∞ (fun z => frameBivector (E z) i j) (Metric.closedBall (0 : ℂ) 1) :=
  D05Proof.frameBivector_entry_contDiffOn hE.1 i j

theorem variation_frameBivector_uniform_bound {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, matrixFrobSq (frameBivector (E z)) ≤ C ^ 2 := by
  rcases hd with ⟨_, _, _, _, hG, _, _, _, _, _, _, _, _, hindex⟩
  obtain ⟨C, hC, hbound⟩ := D05Proof.normalizedFrame_uniform_bivector hG
    (boundaryCompact d j) (hindex j).2.2.1
  refine ⟨C, hC, fun F E hF hE => hbound F.f E hE ?_⟩
  intro θ
  have hb := hF.2.2.2.2.2.2.2.1 θ
  exact ⟨hb.1.le, hb.2.le⟩

end Yau.Blueprint.V04Proof
