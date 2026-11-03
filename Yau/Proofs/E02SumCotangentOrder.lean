import Yau.Proofs.E02CotangentTensor
import Yau.Proofs.E02SumJetMinimum
import Yau.Proofs.E02ProductMaps

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

/-- At ONE product contact, the actual Peano tensors give the complex
spatial form inequality in every independent fiber direction. The two
physical directions have time component zero. -/
theorem sumJet_cotangent_order (n m : ℕ)
    (f : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) → ℝ) (α : Fin m → ℝ)
    (Q : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
    (p : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : ∀ i, RealSecondJet (f i) (factorProjection n m i Q) (p i) (A i))
    (g : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) → ℝ)
    (hg : ContDiffAt ℝ 2 g Q)
    (slope : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) →L[ℝ] ℝ)
    (hMin : IsLocalMin (fun R => (∑ i, α i*f i (factorProjection n m i R))-g R-slope R) Q)
    (X : ComplexVector n) (V : Fin m → ComplexVector n) :
    (fderiv ℝ (fderiv ℝ g) Q (productSpaceCoordinates n m (X,V)) (productSpaceCoordinates n m (X,V))+
      fderiv ℝ (fderiv ℝ g) Q
        (productSpaceCoordinates n m (Complex.I • X,fun i => Complex.I • V i))
        (productSpaceCoordinates n m (Complex.I • X,fun i => Complex.I • V i)))/4 ≤
      ∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ
        (cotangentTensor (A i)*ᵥcotangentVector X (V i))).re := by
  have hOrder := (sumJet_localMin_constraints (factorProjection n m) f α Q p A hJet
    g _ _ (realSecondJet_of_contDiffAt_two hg) slope hMin).2
  have h1 := hOrder (productSpaceCoordinates n m (X,V))
  have h2 := hOrder (productSpaceCoordinates n m (Complex.I • X,fun i => Complex.I • V i))
  simp only [factorProjection_productSpace] at h1 h2
  have hSum : (∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ
      (cotangentTensor (A i)*ᵥcotangentVector X (V i))).re) =
      ((∑ i, α i*A i (envelopeSpaceCoordinates n (X,V i)) (envelopeSpaceCoordinates n (X,V i)))+
        ∑ i, α i*A i (envelopeSpaceCoordinates n (Complex.I • X,Complex.I • V i))
          (envelopeSpaceCoordinates n (Complex.I • X,Complex.I • V i)))/4 := by
    calc
      _ = ∑ i, α i*((A i (envelopeSpaceCoordinates n (X,V i)) (envelopeSpaceCoordinates n (X,V i))+
          A i (envelopeSpaceCoordinates n (Complex.I • X,Complex.I • V i))
            (envelopeSpaceCoordinates n (Complex.I • X,Complex.I • V i)))/4) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [cotangentTensor_quadratic (A i) (hJet i).1 X (V i)]
      _ = _ := by
        simp only [mul_div_assoc,mul_add,Finset.sum_add_distrib,Finset.sum_div,add_div]
  rw [hSum]
  linarith

end Yau.NodeProofs.E02Aux
