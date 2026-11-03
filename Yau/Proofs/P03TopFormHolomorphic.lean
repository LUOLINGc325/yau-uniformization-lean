import Yau.Proofs.P03TopFormMaps
import Yau.Proofs.P03FieldChartCriteria

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem scalar_holomorphic_iff (f : M.Carrier → ℂ) :
    HolomorphicTopForm (r := 1) (AntiCanonicalFiber M) (scalarToAntiTop f) ↔ IsHolomorphicFn f := by
  constructor
  · intro h
    apply (mdifferentiable_iff_chartDifferentiable f).mpr
    intro a
    have ha := h a 0
    rw [antiCanonical_localDomain] at ha
    exact ha.congr fun z hz => (scalarToAntiTop_coefficients f a hz 0).symm
  · intro h a α
    rw [antiCanonical_localDomain]
    exact ((mdifferentiable_iff_chartDifferentiable f).mp h a).congr
      fun z hz => scalarToAntiTop_coefficients f a hz α

theorem field_holomorphic_iff (V : VectorField M) :
    HolomorphicTopForm (r := n) (TangentAntiCanonicalFiber M) (fieldToTangentAntiTop V) ↔
      IsHolomorphicField V := by
  constructor
  · intro h
    apply (holomorphicField_iff_chartDifferentiable V).mpr
    intro a
    apply (differentiableOn_piLp (𝕜 := ℂ) 2).mpr
    intro α
    have ha := h a α
    rw [tangentAntiCanonical_localDomain] at ha
    exact ha.congr fun z hz =>
      (congrArg (fun w : ComplexVector n => w α) (fieldToTangentAntiTop_coefficients V a hz)).symm
  · intro h a α
    rw [tangentAntiCanonical_localDomain]
    have ha := (differentiableOn_piLp (𝕜 := ℂ) 2).mp
      ((holomorphicField_iff_chartDifferentiable V).mp h a) α
    exact ha.congr fun z hz =>
      congrArg (fun w : ComplexVector n => w α) (fieldToTangentAntiTop_coefficients V a hz)

theorem scalarToAntiTop_smooth (f : M.Carrier → ℂ)
    (hf : ∀ a : M.Carrier, ContDiffOn ℝ ∞ (inChart a f) (chartTarget a)) :
    SmoothForm (r := 1) (AntiCanonicalFiber M) (scalarToAntiTop f) := by
  intro a I α
  have hI : I = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
  subst I
  rw [antiCanonical_localDomain]
  exact (hf a).congr fun z hz => scalarToAntiTop_coefficients f a hz α

end Yau.NodeProofs.P03Aux
