import Yau.Proofs.D02FiberLimitFrame
import Yau.Proofs.D02FiberLimitEvaluation

open scoped Manifold Topology ContDiff Matrix
open Set Filter

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {M : ComplexManifold n}

/-- The genuine valid chart/minor neighborhood, for the one square frame. -/
def frameDomain (V : Fin m → VectorField M) (C : Fin n → Fin m → ℂ) (x : M.Carrier) :
    Set (ComplexVector n) :=
  chartTarget x ∩ {z | (frameMatrix V C x z).det ≠ 0}

theorem frameDomain_isOpen (V : Fin m → VectorField M)
    (hV : ∀ a, IsHolomorphicField (V a)) (C : Fin n → Fin m → ℂ) (x : M.Carrier) :
    IsOpen (frameDomain V C x) := by
  have hd : ContinuousOn (fun z ↦ (frameMatrix V C x z).det) (chartTarget x) :=
    continuous_id.matrix_det.comp_continuousOn (frameMatrix_continuousOn V hV C x)
  exact hd.isOpen_inter_preimage (isOpen_extChartAt_target (I := ComplexModel n) x) isOpen_ne

theorem frameDomain_center (V : Fin m → VectorField M) (C : Fin n → Fin m → ℂ)
    (x : M.Carrier) (hC : frameMatrix V C x (chartPt x x) = 1) :
    chartPt x x ∈ frameDomain V C x := by
  refine ⟨(extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x), ?_⟩
  change (frameMatrix V C x (chartPt x x)).det ≠ 0
  rw [hC, Matrix.det_one]
  exact one_ne_zero

/-- A continuous local inverse of the same finite field evaluations. -/
def frameReconstruct (V : Fin m → VectorField M) (C : Fin n → Fin m → ℂ)
    (x : M.Carrier) (p : ComplexVector n × (Fin m → ℂ)) : ComplexVector n :=
  WithLp.toLp 2 ((frameMatrix V C x p.1)⁻¹.mulVec (fun i ↦ ∑ a, C i a * p.2 a))

theorem frameReconstruct_continuousOn (V : Fin m → VectorField M)
    (hV : ∀ a, IsHolomorphicField (V a)) (C : Fin n → Fin m → ℂ) (x : M.Carrier) :
    ContinuousOn (frameReconstruct V C x) (frameDomain V C x ×ˢ univ) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hS : ContinuousAt (frameMatrix V C x) p.1 :=
    (frameMatrix_continuousOn V hV C x).continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hp.1.1)
  have hdet : (frameMatrix V C x p.1).det ≠ 0 := hp.1.2
  have hscalar : ContinuousAt (Inv.inv : ℂ → ℂ) (frameMatrix V C x p.1).det :=
    continuousAt_inv₀ hdet
  have hmatrix : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (frameMatrix V C x p.1) := continuousAt_matrix_inv (frameMatrix V C x p.1) (by
        simpa only [Ring.inverse_eq_inv'] using hscalar)
  have hinv : ContinuousAt (fun z ↦ (frameMatrix V C x z)⁻¹) p.1 := hmatrix.comp hS
  have hA : ContinuousAt (fun q : ComplexVector n × (Fin m → ℂ) ↦
      (frameMatrix V C x q.1)⁻¹) p := hinv.comp continuousAt_fst
  have he : Continuous (fun q : ComplexVector n × (Fin m → ℂ) ↦
      fun i : Fin n ↦ ∑ a, C i a * q.2 a) := by
    apply continuous_pi
    intro i
    have hcoord (a : Fin m) : Continuous (fun q : ComplexVector n × (Fin m → ℂ) ↦ q.2 a) :=
      (continuous_apply a).comp continuous_snd
    exact continuous_finsetSum _ (fun a _ ↦ (hcoord a).const_mul (C i a))
  have hmul : Continuous (fun q : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) ↦ q.1.mulVec q.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hprod : ContinuousAt (fun q : ComplexVector n × (Fin m → ℂ) ↦
      ((frameMatrix V C x q.1)⁻¹, fun i : Fin n ↦ ∑ a, C i a * q.2 a)) p :=
    hA.prodMk he.continuousAt
  change ContinuousAt (fun q : ComplexVector n × (Fin m → ℂ) ↦
    WithLp.toLp 2 ((frameMatrix V C x q.1)⁻¹.mulVec (fun i ↦ ∑ a, C i a * q.2 a))) p
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℂ)).continuousAt.comp
    (f := fun q : ComplexVector n × (Fin m → ℂ) ↦
      (frameMatrix V C x q.1)⁻¹.mulVec (fun i ↦ ∑ a, C i a * q.2 a))
    (hmul.continuousAt.comp (f := fun q : ComplexVector n × (Fin m → ℂ) ↦
      ((frameMatrix V C x q.1)⁻¹, fun i : Fin n ↦ ∑ a, C i a * q.2 a)) hprod)

theorem frameReconstruct_evaluation (V : Fin m → VectorField M) (C : Fin n → Fin m → ℂ)
    (x y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (hdet : (frameMatrix V C x (chartPt x y)).det ≠ 0) (ξ : Covector n) :
    frameReconstruct V C x (chartPt x y, evaluationVector V (y, ξ)) = covectorCoords x y ξ := by
  have hh := matrix_inverse_reconstruct (isUnit_iff_ne_zero.mpr hdet)
    (frameMatrix_evaluation V C x y hy ξ)
  exact congrArg (WithLp.toLp 2) hh.symm

end Yau.NodeProofs.D02FiberLimitAux
