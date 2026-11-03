import Yau.Proofs.V03AngularDirichlet
import Yau.Proofs.V03FamilyLogTrace
import Yau.Proofs.V03HilbertQuadratic

/-! The actual full logarithmic wall seminorm is a genuinely smooth
Hilbert quadratic along every original admissible holomorphic family.
Its actual mixed derivative is retained exactly, including the mixed jet. -/

open scoped Topology ContDiff lp

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem family_complexLogTrace_joint_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z}) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ))
      (Metric.ball (0 : ℂ) R ×ˢ Set.univ) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (family_logTrace_joint_contDiffOn hd j hfamily hadm)

def familyLogDirichletVector {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z})
    (z : ℂ) : ℓ²(ℤ, ℂ) :=
  angularDirichletVector Metric.isOpen_ball
    (family_complexLogTrace_joint_contDiffOn hd j hfamily hadm) z

theorem familyLogDirichletVector_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z}) :
    ContDiffOn ℝ ∞ (familyLogDirichletVector hd j hfamily hadm) (Metric.ball (0 : ℂ) R) :=
  angularDirichletVector_contDiffOn Metric.isOpen_ball
    (family_complexLogTrace_joint_contDiffOn hd j hfamily hadm)

theorem familyLogDirichletVector_norm_sq {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z})
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖familyLogDirichletVector hd j hfamily hadm z‖ ^ 2 =
      (scalarDSq (logTrace d j (fz z))).toReal := by
  have hp : Function.Periodic (fun θ => (logTrace d j (fz z) θ : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg Complex.ofReal (logTrace_periodic d j {F with f := fz z} θ)
  exact angularDirichletVector_norm_sq Metric.isOpen_ball
    (family_complexLogTrace_joint_contDiffOn hd j hfamily hadm) hz hp

theorem family_logEnergy_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z}) :
    ContDiffOn ℝ ∞ (fun z => (scalarDSq (logTrace d j (fz z))).toReal)
      (Metric.ball (0 : ℂ) R) := by
  have hh := (familyLogDirichletVector_contDiffOn hd j hfamily hadm).norm_sq ℂ
  exact hh.congr (fun z hz => (familyLogDirichletVector_norm_sq hd j hfamily hadm hz).symm)

theorem family_logEnergy_mixed_actual {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z}) :
    let Q := familyLogDirichletVector hd j hfamily hadm
    mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal) =
      (1 / 2 : ℝ) * (‖fderiv ℝ Q 0 1‖ ^ 2 + ‖fderiv ℝ Q 0 Complex.I‖ ^ 2) +
      (1 / 2 : ℝ) * (inner ℂ (Q 0) (fderiv ℝ (fderiv ℝ Q) 0 1 1 +
        fderiv ℝ (fderiv ℝ Q) 0 Complex.I Complex.I)).re := by
  letI : InnerProductSpace ℝ ℓ²(ℤ, ℂ) := InnerProductSpace.rclikeToReal ℂ ℓ²(ℤ, ℂ)
  let Q := familyLogDirichletVector hd j hfamily hadm
  have hQ : ContDiffAt ℝ 2 Q 0 :=
    ((familyLogDirichletVector_contDiffOn hd j hfamily hadm).contDiffAt
      (Metric.ball_mem_nhds (0 : ℂ) hfamily.1)).of_le (by simp)
  have heq : (fun z => (scalarDSq (logTrace d j (fz z))).toReal) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => ‖Q z‖ ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hfamily.1] with z hz
    exact (familyLogDirichletVector_norm_sq hd j hfamily hadm hz).symm
  rw [mixedReal_congr heq]
  exact mixedReal_norm_sq hQ

end Yau.Blueprint.V03Proof
