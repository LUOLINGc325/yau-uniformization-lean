import Yau.Proofs.C05HessianBlocks
import Yau.Proofs.C05GradientFlowDefinitions
import Yau.Proofs.C05LeviTimeDerivative
import Yau.Proofs.G04ScalarNormalization

/-! The mixed block of the actual covariant Hessian is the actual Levi matrix.
Both connection cancellations use the Kähler connection of the given metric. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.Proofs.C05GradientFlowAux Yau.LeafProofs.L18Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realHessInChart_isSymm (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n)
    (hf : ContDiffAt ℝ 2 (inChart c f) z) :
    (Matrix.of (realHessInChart k f c z)).IsSymm := by
  ext a b
  change realHessInChart k f c z b a = realHessInChart k f c z a b
  have hs := (hf.isSymmSndFDerivAt (by norm_num)).eq (realVec b) (realVec a)
  have hΓ : (∑ q, christoffel k c z q b a * rDeriv (inChart c f) z q) =
      ∑ q, christoffel k c z q a b * rDeriv (inChart c f) z q := by
    apply Finset.sum_congr rfl
    intro q _
    rw [christoffel_symm_lower k c z q b a]
  simp only [realHessInChart,Yau.LeafProofs.L18Aux.rDeriv_rDeriv_eq_hessian hf,hΓ,hs]

theorem hessianMixed_connection_cancel (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (D : Matrix (RIdx n) (RIdx n) ℝ)
    (p : RIdx n → ℝ) :
    hessianMixed (fun a b => D a b - ∑ q, christoffel k c z q a b * p q) =
      hessianMixed D := by
  have hΓ (i j : Fin n) (q : RIdx n) :
      christoffel k c z q (i,1) (j,1) = -christoffel k c z q (i,0) (j,0) := by
    simpa [Yau.LeafProofs.L12Aux.jSign,Yau.LeafProofs.L12Aux.jIndex] using
      Yau.NodeProofs.G04Aux.christoffel_double_J k hk hK c hz (i,0) (j,0) q
  ext i j
  have hsum : (∑ q, christoffel k c z q (i,1) (j,1) * p q) =
      -(∑ q, christoffel k c z q (i,0) (j,0) * p q) := by
    simp only [hΓ,neg_mul,Finset.sum_neg_distrib]
  have hcross : (∑ q, christoffel k c z q (i,1) (j,0) * p q) =
      ∑ q, christoffel k c z q (i,0) (j,1) * p q := by
    have hJ := Yau.NodeProofs.G04Aux.christoffel_double_J k hk hK c hz (i,0) (j,1)
    apply Finset.sum_congr rfl
    intro q _
    have hq := hJ q
    norm_num [Yau.LeafProofs.L12Aux.jSign,Yau.LeafProofs.L12Aux.jIndex] at hq
    rw [hq]
  apply Complex.ext <;>
    simp only [hessianMixed,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,mul_zero,sub_zero,zero_add,add_zero,hsum,hcross] <;> ring

theorem hessianMixed_partial_eq_leviC {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) :
    hessianMixed (fun a b => rDeriv (fun w => rDeriv f w b) z a) = leviC f z := by
  ext i j
  rw [leviC_eq_real_hessian hf i j]
  simp only [hessianMixed,Yau.LeafProofs.L18Aux.rDeriv_rDeriv_eq_hessian hf]
  have hs (u v : ComplexVector n) := (hf.isSymmSndFDerivAt (by norm_num)).eq u v
  simp only [realVec,Fin.isValue,ite_true,one_smul,show (1 : Fin 2) ≠ 0 by decide,
    ite_false,stdVec]
  rw [hs (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
    hs (Complex.I • EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1),
    hs (Complex.I • EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
    hs (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1)]

theorem hessianMixed_realHessInChart (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hf : ContDiffAt ℝ 2 (inChart c f) z) :
    hessianMixed (realHessInChart k f c z) = leviC (inChart c f) z := by
  change hessianMixed (fun a b =>
    rDeriv (fun w => rDeriv (inChart c f) w b) z a -
      ∑ q, christoffel k c z q a b * rDeriv (inChart c f) z q) = _
  exact (hessianMixed_connection_cancel k hk hK c hz
    (fun a b => rDeriv (fun w => rDeriv (inChart c f) w b) z a)
    (fun q => rDeriv (inChart c f) z q)).trans (hessianMixed_partial_eq_leviC hf)

end Yau.Proofs.C05Aux
