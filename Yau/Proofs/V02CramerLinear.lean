import Yau.Proofs.V02CramerField
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The division-free Cramer polynomial is an actual linear map of its
right-hand vector. Its scalar coefficients are genuine smooth functions. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {ι κ β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

def tuplePushLinearMap (c : ι → β) : (ι → ℂ) →ₗ[ℂ] β → ℂ :=
  ∑ i, (LinearMap.single ℂ (fun _ : β => ℂ) (c i)).comp (LinearMap.proj i)

theorem tuplePushLinearMap_apply (c : ι → β) (v : ι → ℂ) :
    tuplePushLinearMap c v = tuplePush c v := by
  ext j
  simp [tuplePushLinearMap, tuplePush, LinearMap.sum_apply, Pi.single_apply, eq_comm]

def tupleCramerLinearMap (A : Matrix κ β ℂ) (r : ι → κ) (c : ι → β) :
    (κ → ℂ) →ₗ[ℂ] β → ℂ :=
  (tuplePushLinearMap c).comp
    ((A.submatrix r c).adjugate.mulVecLin.comp (LinearMap.funLeft ℂ ℂ r))

theorem tupleCramerLinearMap_apply (A : Matrix κ β ℂ) (r : ι → κ) (c : ι → β)
    (Y : κ → ℂ) : tupleCramerLinearMap A r c Y = tupleCramer A r c Y := by
  change tuplePushLinearMap c ((A.submatrix r c).adjugate *ᵥ (Y ∘ r)) = _
  exact tuplePushLinearMap_apply _ _

theorem tupleCramer_basis_sum (A : Matrix κ β ℂ) (r : ι → κ) (c : ι → β)
    (Y : κ → ℂ) (j : β) :
    tupleCramer A r c Y j = ∑ a, tupleCramer A r c (Pi.single a 1) j * Y a := by
  have hY : Y = ∑ a, Y a • Pi.single a (1 : ℂ) := by
    have he (a : κ) : Y a • Pi.single a (1 : ℂ) = Pi.single a (Y a) := by
      rw [← Pi.single_smul]
      simp
    simp_rw [he]
    ext i
    simp
  calc
    _ = (tupleCramerLinearMap A r c (∑ a, Y a • Pi.single a (1 : ℂ))) j := by
      rw [← hY, tupleCramerLinearMap_apply]
    _ = ∑ a, Y a * tupleCramer A r c (Pi.single a 1) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        tupleCramerLinearMap_apply]
    _ = _ := Finset.sum_congr rfl (fun a _ => mul_comm _ _)

variable {n q b : ℕ} {M : ComplexManifold n}

def spanningCramerCoefficient (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (k : SpanningMinorIndex n q b) (j : Fin b) (a : Fin q) (y : CotangentPoint M) : ℂ :=
  tupleCramer (spanningAmbientMatrix G Z y) k.1 k.2 (Pi.single a 1) j

theorem spanningCramerCoefficient_chart_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (k : SpanningMinorIndex n q b) (j : Fin b) (a : Fin q) (x : M.Carrier) :
    ContDiffOn ℂ ∞ (fun z => spanningCramerCoefficient G Z k j a (cotangentChartInv x z))
      (cotangentTarget x) :=
  tupleCramer_entry_contDiffOn
    (A := fun z => spanningAmbientMatrix G Z (cotangentChartInv x z))
    (Y := fun _ => Pi.single a 1)
    (fun a k => spanningAmbient_entry_chart_contDiffOn hG hZ x a k)
    (fun _ => contDiffOn_const) k.1 k.2 j

theorem spanningFirstCoefficients_as_sum
    (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (α : ℂ → ℂ) (ζ : ℂ) (j : Fin b) :
    spanningFirstCoefficients G Z f E l α ζ j =
      ∑ p : SpanningMinorIndex n q b × Fin q,
        (α ζ * spanningCorona G Z f p.1 ζ) * spanningCramerCoefficient G Z p.1 j p.2 (f ζ) *
          (ambientFrame G f E ζ *ᵥ l ζ) p.2 := by
  classical
  simp only [spanningFirstCoefficients, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [tupleCramer_basis_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [spanningCramerCoefficient]
  ring

end Yau.Blueprint.V02Proof
