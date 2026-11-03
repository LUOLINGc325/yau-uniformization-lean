import Yau.LeafProofs.L21WeightedDomainsOperators

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedLocalMultiplierTest {a : X n → ℂ}
    (ha : ContDiffOn ℝ ∞ a (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) : CompactTest (Metric.ball (0 : X n) 1) := by
  have hs : tsupport (fun x => a x*ψ x) ⊆ tsupport ψ := tsupport_mul_subset_right
  exact ⟨fun x => a x*ψ x,
    contDiff_of_contDiffOn_tsupport_subset Metric.isOpen_ball (ha.mul ψ.property.1.contDiffOn) hs ψ.property.2.2,
    ψ.property.2.1.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans ψ.property.2.2⟩

def weightedRhoInverseTest (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    CompactTest (Metric.ball (0 : X n) 1) :=
  weightedLocalMultiplierTest
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiff_rho.contDiffOn.inv (fun x hx => (rho_pos hx).ne'))) ψ

theorem rho_mul_weightedRhoInverseTest
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) (x : X n) :
    (rho x : ℂ)*weightedRhoInverseTest ψ x = ψ x := by
  by_cases hz : ψ x = 0
  · change (rho x : ℂ)*((((rho x)⁻¹ : ℝ) : ℂ)*ψ x) = _
    rw [hz,mul_zero,mul_zero]
  · have hr : (rho x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (rho_pos (ψ.property.2.2 (subset_tsupport ψ hz))).ne'
    change (rho x : ℂ)*((((rho x)⁻¹ : ℝ) : ℂ)*ψ x) = _
    rw [← mul_assoc,Complex.ofReal_inv,mul_inv_cancel₀ hr,one_mul]

theorem weightedTPrincipal_mul_rhoInverseTest
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Yau.RIdx n)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    (fun x => weightedTPrincipal A j () a x*weightedRhoInverseTest ψ x) =
      fun x => dbarRealCoefficient A j a x*ψ x := by
  funext x
  calc
    _ = dbarRealCoefficient A j a x*((rho x : ℂ)*weightedRhoInverseTest ψ x) := by
      dsimp only [weightedTPrincipal]
      ring
    _ = _ := by rw [rho_mul_weightedRhoInverseTest]

end Yau.LeafProofs.L21Aux
