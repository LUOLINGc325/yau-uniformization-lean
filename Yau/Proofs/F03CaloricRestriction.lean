import Yau.Proofs.F03CaloricMembership

/-! Literal weak caloric equations restrict to smaller actual product domains. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem weakGradient_mono {O V : Set (Space d)} {I J : Set ℝ} (hVO : V ⊆ O) (hJI : J ⊆ I)
    {u : Point d → ℝ} {G : Point d → RIdx d → ℝ} (hG : WeakGradient O I u G) :
    WeakGradient V J u G := by
  intro φ hφ i
  have hφD : Test (O ×ˢ I) φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans (prod_mono hVO hJI)⟩
  have h := hG φ hφD i
  rw [productVolume_eq_restrict,integral_mul_test_eq (test_spatialDerivative hφD i) u,
    integral_mul_test_eq hφD (fun p => G p i)] at h
  rw [productVolume_eq_restrict,integral_mul_test_eq (test_spatialDerivative hφ i) u,
    integral_mul_test_eq hφ (fun p => G p i)]
  exact h

theorem weakEquation_zero_mono {O V : Set (Space d)} {I J : Set ℝ} (hVO : V ⊆ O) (hJI : J ⊆ I)
    {a : Point d → Mat d} {b : Point d → RIdx d → ℝ}
    {u : Point d → ℝ} {G : Point d → RIdx d → ℝ}
    (hWE : WeakEquation O I a b (fun _ => 0) u G) :
    WeakEquation V J a b (fun _ => 0) u G := by
  intro φ hφ
  have hφD : Test (O ×ˢ I) φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans (prod_mono hVO hJI)⟩
  let F : Point d → ℝ := fun p => -u p*deriv (fun t => φ (p.1,t)) p.2+
    (∑ i,∑ j,a p i j*G p j*Parabolic.d (fun x => φ (x,p.2)) p.1 i)-
    (∑ j,(b p j-∑ i,Parabolic.d (fun x => a (x,p.2) i j) p.1 i)*G p j*φ p)
  have hZero : ∀ p ∉ V ×ˢ J,F p=0 := by
    intro p hp
    have hφzero : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hφ.2.2 h))
    have hTime : deriv (fun t => φ (p.1,t)) p.2=0 :=
      image_eq_zero_of_notMem_tsupport (f := fun q : Point d => deriv (fun t => φ (q.1,t)) q.2)
        (fun h => hp ((test_timeDerivative hφ).2.2 h))
    have hSpace : ∀ i, Parabolic.d (fun x => φ (x,p.2)) p.1 i=0 := fun i =>
      image_eq_zero_of_notMem_tsupport (f := fun q : Point d => Parabolic.d (fun x => φ (x,q.2)) q.1 i)
        (fun h => hp ((test_spatialDerivative hφ i).2.2 h))
    simp only [F,hφzero,hTime,hSpace,mul_zero,Finset.sum_const_zero,zero_add,sub_zero]
  have hZeroD : ∀ p ∉ O ×ˢ I,F p=0 := fun p hp => hZero p (fun h => hp ((prod_mono hVO hJI) h))
  have h := hWE φ hφD
  rw [productVolume_eq_restrict] at h
  simp only [zero_mul,integral_zero] at h ⊢
  change (∫ p,F p ∂volume.restrict (O ×ˢ I))=0 at h
  change (∫ p,F p ∂productVolume V J)=0
  rw [productVolume_eq_restrict,setIntegral_eq_integral_of_forall_compl_eq_zero hZero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hZeroD] at h
  exact h

theorem localEnergy_mono {O V : Set (Space d)} {I J : Set ℝ} (hVO : V ⊆ O) (hJI : J ⊆ I)
    {u : Point d → ℝ} {G : Point d → RIdx d → ℝ} (hE : LocalEnergy O I u G) :
    LocalEnergy V J u G := by
  refine ⟨weakGradient_mono hVO hJI hE.1,?_⟩
  intro W c r hW hWc hWV hcr
  exact hE.2 W c r hW hWc (hWV.trans hVO) (hcr.trans hJI)

end Yau.Proofs.F03Aux
