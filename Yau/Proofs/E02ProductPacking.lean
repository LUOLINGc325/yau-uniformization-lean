import Yau.Proofs.E02EuclideanPacking

open Matrix
open scoped Topology InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

def fiberEuclideanIsometry (n m : ℕ) :
    PiLp 2 (fun _ : Fin m => ComplexVector n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (2*n*m)) :=
  ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin m => complexRealCoordinates n)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin m) (_ : Fin (2*n)) => ℝ)).symm).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (((Equiv.sigmaEquivProd (Fin m) (Fin (2*n))).trans finProdFinEquiv).trans
        (finCongr (Nat.mul_comm m (2*n)))))

def fiberRealCoordinates (n m : ℕ) :
    (Fin m → ComplexVector n) ≃L[ℝ] EuclideanSpace ℝ (Fin (2*n*m)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ComplexVector n)).symm.trans
    (fiberEuclideanIsometry n m).toContinuousLinearEquiv

theorem fiberRealCoordinates_norm_sq (n m : ℕ) (ξ : Fin m → ComplexVector n) :
    ‖fiberRealCoordinates n m ξ‖^2 = ∑ i, ‖ξ i‖^2 := by
  change ‖fiberEuclideanIsometry n m (WithLp.toLp 2 ξ)‖^2 = _
  rw [(fiberEuclideanIsometry n m).norm_map,PiLp.norm_sq_eq_of_L2]

/-- The shared base and physical time occur once, regardless of the
number of independent cotangent fibers. -/
def productRealCoordinates (n m : ℕ) :
    (ComplexVector n × ℝ × (Fin m → ComplexVector n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) :=
  (((complexRealCoordinates n).toContinuousLinearEquiv.prodCongr
    ((timeRealCoordinates.prodCongr (fiberRealCoordinates n m)).trans
      (euclideanJoin 1 (2*n*m)))).trans
    (euclideanJoin (2*n) (1+2*n*m))).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (by omega : 2*n+(1+2*n*m) = 2*n+1+2*n*m))).toContinuousLinearEquiv

theorem productRealCoordinates_norm_sq (n m : ℕ)
    (p : ComplexVector n × ℝ × (Fin m → ComplexVector n)) :
    ‖productRealCoordinates n m p‖^2 = ‖p.1‖^2+p.2.1^2+∑ i, ‖p.2.2 i‖^2 := by
  simp only [productRealCoordinates,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map,euclideanJoin_norm_sq,timeRealCoordinates_norm_sq,
    fiberRealCoordinates_norm_sq]
  ring

def factorProjectionRaw (n m : ℕ) (i : Fin m) :
    (ComplexVector n × ℝ × (Fin m → ComplexVector n)) →ₗ[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) where
  toFun p := (p.1,p.2.2 i,p.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def factorProjection (n m : ℕ) (i : Fin m) :
    EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) →L[ℝ] EuclideanSpace ℝ (Fin (4*n+1)) :=
  (envelopeRealCoordinates n).toContinuousLinearMap ∘L
    (LinearMap.toContinuousLinearMap (factorProjectionRaw n m i)) ∘L
    (productRealCoordinates n m).symm.toContinuousLinearMap

theorem factorProjection_on_product (n m : ℕ) (i : Fin m)
    (p : ComplexVector n × ℝ × (Fin m → ComplexVector n)) :
    factorProjection n m i (productRealCoordinates n m p) =
      envelopeRealCoordinates n (p.1,p.2.2 i,p.2.1) := by
  simp [factorProjection,factorProjectionRaw]

theorem factorProjection_norm_sq_on_product (n m : ℕ) (i : Fin m)
    (p : ComplexVector n × ℝ × (Fin m → ComplexVector n)) :
    ‖factorProjection n m i (productRealCoordinates n m p)‖^2 ≤
      ‖productRealCoordinates n m p‖^2 := by
  have hi : ‖p.2.2 i‖^2 ≤ ∑ j, ‖p.2.2 j‖^2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin m => ‖p.2.2 j‖^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [factorProjection_on_product,envelopeRealCoordinates_norm_sq,productRealCoordinates_norm_sq]
  linarith

theorem factorProjection_norm_le (n m : ℕ) (i : Fin m)
    (Q : EuclideanSpace ℝ (Fin (2*n+1+2*n*m))) : ‖factorProjection n m i Q‖ ≤ ‖Q‖ := by
  obtain ⟨p,rfl⟩ := (productRealCoordinates n m).surjective Q
  have hSq := factorProjection_norm_sq_on_product n m i p
  have hN0 := norm_nonneg (factorProjection n m i (productRealCoordinates n m p))
  have hN1 := norm_nonneg (productRealCoordinates n m p)
  nlinarith

theorem factorProjection_opNorm_le_one (n m : ℕ) (i : Fin m) : ‖factorProjection n m i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro Q
  simpa only [one_mul] using factorProjection_norm_le n m i Q

theorem factorProjection_surjective (n m : ℕ) (i : Fin m) :
    Function.Surjective (factorProjection n m i) := by
  intro y
  let q := (envelopeRealCoordinates n).symm y
  let p : ComplexVector n × ℝ × (Fin m → ComplexVector n) :=
    (q.1,q.2.2,fun j => if j = i then q.2.1 else 0)
  refine ⟨productRealCoordinates n m p,?_⟩
  rw [factorProjection_on_product]
  have hp : (p.1,p.2.2 i,p.2.1) = q := by simp [p]
  rw [hp]
  exact (envelopeRealCoordinates n).apply_symm_apply y

end Yau.NodeProofs.E02Aux
