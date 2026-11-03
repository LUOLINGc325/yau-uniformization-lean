import Yau.Blueprint.Nodes

open scoped Topology InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Fixed real/imaginary coordinates, assembled from the genuine standard
one/I orthonormal basis on each complex coordinate. -/
def complexRealCoordinates (n : ℕ) :
    ComplexVector n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*n)) :=
  (Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (((Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans finProdFinEquiv).trans
        (finCongr (Nat.mul_comm n 2))))

def euclideanJoin (n m : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n+m)) := EuclideanSpace.finAddEquivProd.symm

def timeRealCoordinates : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm

theorem timeRealCoordinates_norm_sq (t : ℝ) : ‖timeRealCoordinates t‖^2 = t^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [timeRealCoordinates,PiLp.equivOfUnique]

/-- Joining two Euclidean factors uses the squared sum, although the
ordinary topology-bearing product on the domain has its standard max norm. -/
theorem euclideanJoin_norm_sq (n m : ℕ)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ‖euclideanJoin n m q‖^2 = ‖q.1‖^2+‖q.2‖^2 := by
  let e := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finSumFinEquiv.symm : Fin (n+m) ≃ Fin n ⊕ Fin m)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℝ))
  change ‖e.symm (WithLp.toLp 2 q)‖^2 = _
  rw [e.symm.norm_map,WithLp.prod_norm_sq_eq_of_L2]
  rfl

def envelopeRealCoordinates (n : ℕ) :
    (ComplexVector n × ComplexVector n × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) :=
  let eZ := (complexRealCoordinates n).toContinuousLinearEquiv
  let eT := timeRealCoordinates
  ((eZ.prodCongr ((eZ.prodCongr eT).trans (euclideanJoin (2*n) 1))).trans
    (euclideanJoin (2*n) (2*n+1))).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (by omega : 2*n+(2*n+1) = 4*n+1))).toContinuousLinearEquiv

theorem envelopeRealCoordinates_norm_sq (n : ℕ)
    (p : ComplexVector n × ComplexVector n × ℝ) :
    ‖envelopeRealCoordinates n p‖^2 = ‖p.1‖^2+‖p.2.1‖^2+p.2.2^2 := by
  simp only [envelopeRealCoordinates,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map,euclideanJoin_norm_sq,timeRealCoordinates_norm_sq]
  ring

end Yau.NodeProofs.E02Aux
