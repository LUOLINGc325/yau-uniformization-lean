import Yau.Proofs.D02Dimension
import Yau.Proofs.V03HolomorphicSmooth

/-! The actual differential and positive inverse-Jacobian potential of the
original immersion. Every local matrix is computed from that same map. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

def immersionInChart (F : M.Carrier → ComplexVector N) (x : M.Carrier) :
    ComplexVector n → ComplexVector N := F ∘ chartInv x

def immersionDerivativeMatrix (F : M.Carrier → ComplexVector N) (x : M.Carrier)
    (z : ComplexVector n) : Matrix (Fin N) (Fin n) ℂ :=
  Yau.LeafProofs.L17Aux.linearMatrix (fderiv ℂ (immersionInChart F x) z)

theorem immersionInChart_differentiableOn {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) :
    DifferentiableOn ℂ (immersionInChart F x) (chartTarget x) := by
  have hi := (contMDiffOn_extChartAt_symm (I := ComplexModel n) (n := ∞) x).mdifferentiableOn
    (by simp)
  have hh : MDifferentiableOn (ComplexModel n) (ComplexModel N) F Set.univ :=
    hF.mdifferentiableOn
  exact (hh.comp hi (fun _ _ => Set.mem_univ _)).differentiableOn

/-- The coordinate derivative is the actual manifold differential in the chart frame. -/
theorem immersionInChart_fderiv_apply {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    fderiv ℂ (immersionInChart F x) z v =
      mfderiv (ComplexModel n) (ComplexModel N) F (chartInv x z)
        (chartVec x (chartInv x z) v) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := ComplexModel n) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply z (hF (chartInv x z)) hi v
  rw [mfderiv_eq_fderiv] at hc
  have hround : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  change fderiv ℂ (F ∘ chartInv x) z v =
    mfderiv (ComplexModel n) (ComplexModel N) F (chartInv x z)
      (mfderiv (ComplexModel n) (ComplexModel n) (chartInv x) z v) at hc
  change fderiv ℂ (F ∘ chartInv x) z v =
    mfderiv (ComplexModel n) (ComplexModel N) F (chartInv x z)
      (mfderiv (ComplexModel n) (ComplexModel n) (chartInv x) (chartPt x (chartInv x z)) v)
  rw [hround]
  exact hc

theorem immersionInChart_fderiv_injective {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    Function.Injective (fderiv ℂ (immersionInChart F x) z) := by
  intro u v huv
  have hframe : Function.Injective (chartVec x (chartInv x z)) :=
    (show Function.LeftInverse (tangentCoords x (chartInv x z)) (chartVec x (chartInv x z)) from
      tangentCoords_chartVec x (chartInv x z) ((extChartAt (ComplexModel n) x).map_target hz)).injective
  apply hframe
  apply hImm (chartInv x z)
  simpa only [← immersionInChart_fderiv_apply hF x hz] using huv

theorem immersionDerivativeMatrix_mulVec (F : M.Carrier → ComplexVector N) (x : M.Carrier)
    (z v : ComplexVector n) :
    immersionDerivativeMatrix F x z *ᵥ WithLp.ofLp v =
      WithLp.ofLp (fderiv ℂ (immersionInChart F x) z v) :=
  Yau.LeafProofs.L17Aux.linearMatrix_mulVec _ v

theorem immersionDerivativeMatrix_mulVec_injective {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    Function.Injective (immersionDerivativeMatrix F x z).mulVec := by
  intro u v huv
  have h := congrArg (WithLp.toLp 2) (show
      WithLp.ofLp (fderiv ℂ (immersionInChart F x) z (WithLp.toLp 2 u)) =
      WithLp.ofLp (fderiv ℂ (immersionInChart F x) z (WithLp.toLp 2 v)) from by
    simpa only [← immersionDerivativeMatrix_mulVec, WithLp.ofLp_toLp] using huv)
  have hh := immersionInChart_fderiv_injective hF hImm x hz h
  exact congrArg WithLp.ofLp hh

def immersionGram (F : M.Carrier → ComplexVector N) (x : M.Carrier)
    (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  (immersionDerivativeMatrix F x z)ᴴ * immersionDerivativeMatrix F x z

theorem immersionGram_posDef {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) : (immersionGram F x z).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (immersionDerivativeMatrix_mulVec_injective hF hImm x hz)

def immersionJacobianWeight (g : HermitianField M) (F : M.Carrier → ComplexVector N)
    (y : M.Carrier) : ℝ :=
  (immersionGram F y (chartPt y y)).det.re / (gMat g y).det.re

def immersionPotential (g : HermitianField M) (F : M.Carrier → ComplexVector N)
    (y : M.Carrier) : ℝ := Real.log (immersionJacobianWeight g F y)

theorem immersionJacobianWeight_pos (g : HermitianField M) {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (y : M.Carrier) :
    0 < immersionJacobianWeight g F y := by
  exact div_pos
    (Complex.pos_iff.mp (immersionGram_posDef hF hImm y
      ((extChartAt (ComplexModel n) y).map_source (mem_extChartAt_source y))).det_pos).1
    (Complex.pos_iff.mp (gMat_posDef g y).det_pos).1

/-- Each actual Jacobian entry is holomorphic on its valid chart target. -/
theorem immersionDerivativeMatrix_differentiableOn {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) (a : Fin N) (b : Fin n) :
    DifferentiableOn ℂ (fun z => immersionDerivativeMatrix F x z a b) (chartTarget x) := by
  have hc := complex_holomorphic_fderiv_apply_differentiableOn
    (isOpen_extChartAt_target (I := ComplexModel n) x) (immersionInChart_differentiableOn hF x)
    (stdVec b)
  exact (EuclideanSpace.proj a : ComplexVector N →L[ℂ] ℂ).differentiable.comp_differentiableOn hc

theorem immersionGram_entry_contDiffOn {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => immersionGram F x z i j) (chartTarget x) := by
  have hs (a : Fin N) (b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => immersionDerivativeMatrix F x z a b) (chartTarget x) :=
    (complex_holomorphic_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
      (immersionDerivativeMatrix_differentiableOn hF x a b)).restrict_scalars ℝ
  simp only [immersionGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffOn.sum fun a _ =>
    (Complex.conjCLE.contDiff.comp_contDiffOn (hs a i)).mul (hs a j)

/-- The genuine local log inverse-Jacobian potential is smooth for the same metric. -/
theorem localImmersionPotential_contDiffOn (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => Real.log (immersionGram F x z).det.re -
      Real.log (hMat g x z).det.re) (chartTarget x) := by
  have hG := Complex.reCLM.contDiff.comp_contDiffOn
    (entrywise_matrix_det_contDiffOn (immersionGram_entry_contDiffOn hF x))
  have hH := Complex.reCLM.contDiff.comp_contDiffOn
    (entrywise_matrix_det_contDiffOn
      (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x))
  exact (hG.log (fun z hz => (Complex.pos_iff.mp (immersionGram_posDef hF hImm x hz).det_pos).1.ne')).sub
    (hH.log (fun z hz => (Complex.pos_iff.mp (hMat_posDef g x z hz).det_pos).1.ne'))

end Yau.NodeProofs.D02Aux
