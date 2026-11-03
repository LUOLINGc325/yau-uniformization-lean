import Yau.LeafProofs.L23CurvatureCalculus
import Yau.LeafProofs.L23RicciBound

/-! The explicit curvature reaction and precise, ordinary intermediate gaps.
These propositions are not axioms and add no hypothesis to the frozen leaf. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

def ricciTensor (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n) : CovTensor n 2 :=
  fun v => realRicciCoeff h c z (v 0) (v 1)

/-- The fixed quadratic polynomial selected with the project's curvature sign. -/
def rmReaction (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n) : CovTensor n 4 :=
  fun v =>
    -(∑ p, ∑ q, realRicciCoeff h c z (v 3) p*(realMetricFn h c z)⁻¹ p q*
      rmTensor h c z ![v 0,v 1,v 2,q]) -
    (1/2 : ℝ)*curvatureAction h c z (v 0) (v 1) (ricciTensor h c z) ![v 2,v 3] -
    (1/2 : ℝ)*(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      (curvatureAction h c z b (v 0) (rmTensor h c z) ![a,v 1,v 2,v 3]-
        curvatureAction h c z b (v 1) (rmTensor h c z) ![a,v 0,v 2,v 3]))

def jetParabolicTensor (h : ℝ → HermitianField M) (c : M.Carrier) (k : ℕ)
    (z : ComplexVector n) (t σ : ℝ) : CovTensor n (4+k) :=
  fun v => deriv (fun s => rmJet (h s) c k z v) t-
    (σ/2)*roughLap (h t) c (rmJet (h t) c k) z v

/-- The base equation that still needs the chart transfer and actual
connection/curvature time variation. It is an ordinary proof obligation. -/
def FixedChartRmEvolutionGap (n : ℕ) : Prop :=
  ∀ (M : ComplexManifold n) (h : ℝ → HermitianField M) (O : Set M.Carrier)
    (a b σ : ℝ), IsOpen O → a < b → 0 < σ →
    LocalRealRicciFlow h O (Set.Icc a b) σ →
    ∀ (c : M.Carrier) (z : ComplexVector n), z ∈ chartTarget c → chartInv c z ∈ O →
    ∀ t ∈ Set.Ioo a b, ∀ v : Fin 4 → RIdx n,
      jetParabolicTensor h c 0 z t σ v=σ*rmReaction (h t) c z v

/-- The norm-free-in-time geometry is quantified after the numerical
constant. A finite contraction-word proof is required to discharge this. -/
def JetReactionBoundGap (n k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : ComplexManifold n) (h : ℝ → HermitianField M) (O : Set M.Carrier)
      (a b σ : ℝ), IsOpen O → a < b → 0 < σ →
      LocalRealRicciFlow h O (Set.Icc a b) σ →
      ∀ (c : M.Carrier) (z : ComplexVector n), z ∈ chartTarget c → chartInv c z ∈ O →
      ∀ t ∈ Set.Ioo a b,
        Real.sqrt (covTensorNormSq (realMetricFn (h t) c z) (jetParabolicTensor h c k z t σ)) ≤
          σ*C*∑ i : Fin (k+1),
            Real.sqrt (covTensorNormSq (realMetricFn (h t) c z) (rmJet (h t) c i.val z))*
            Real.sqrt (covTensorNormSq (realMetricFn (h t) c z) (rmJet (h t) c (k-i.val) z))

theorem rmTensor_evolution_of_gap (hgap : FixedChartRmEvolutionGap n)
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hO : IsOpen O) (hab : a < b) (hσ : 0 < σ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget c) (hx : chartInv c z ∈ O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (v : Fin 4 → RIdx n) :
    jetParabolicTensor h c 0 z t σ v=σ*rmReaction (h t) c z v :=
  hgap M h O a b σ hO hab hσ hflow c z hz hx t ht v

end Yau.LeafProofs.L23Aux
