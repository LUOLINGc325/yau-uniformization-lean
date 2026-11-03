import Yau.LeafProofs.L16WeakSobolevCalculus
import Yau.LeafProofs.L16SpatialSchwarz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem ae_eq_of_test_integrals_eq {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {f g : Point n → ℝ} (hf : MemLp f 2 (volume.restrict Q))
    (hg : MemLp g 2 (volume.restrict Q))
    (hPair : ∀ φ : Point n → ℝ, Test Q φ →
      (∫ p, f p*φ p ∂volume.restrict Q) = ∫ p, g p*φ p ∂volume.restrict Q) :
    f =ᵐ[volume.restrict Q] g := by
  have hLocal : LocallyIntegrableOn (fun p => f p-g p) Q volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hf.sub hg).locallyIntegrable (by norm_num))
  have hZero := hQ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLocal
    (fun φ hφ hcφ hφQ => by
      have hTest : Test Q φ := ⟨hφ,hcφ,hφQ⟩
      have hRest : (∫ p, φ p • (f p-g p)) =
          ∫ p, φ p • (f p-g p) ∂volume.restrict Q := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro p hp
        have hp' : p ∉ tsupport φ := fun h => hp (hφQ h)
        rw [image_eq_zero_of_notMem_tsupport hp',zero_smul]
      rw [hRest]
      have hIntf : Integrable (fun p => f p*φ p) (volume.restrict Q) := hf.integrable_mul (test_memLp hTest)
      have hIntg : Integrable (fun p => g p*φ p) (volume.restrict Q) := hg.integrable_mul (test_memLp hTest)
      have hFun : (fun p => φ p • (f p-g p)) = fun p => f p*φ p-g p*φ p := by
        ext p
        simp only [smul_eq_mul]
        ring
      rw [hFun,integral_sub hIntf hIntg,hPair φ hTest,sub_self])
  filter_upwards [(ae_restrict_iff' hQ.measurableSet).2 hZero] with p hp
  exact sub_eq_zero.mp hp

theorem weakGradientOn_congr_ae {n : ℕ} {Q : Set (Point n)}
    {u v : Point n → ℝ} {G H : Point n → Yau.RIdx n → ℝ}
    (hWeak : WeakGradientOn Q u G) (huv : u =ᵐ[volume.restrict Q] v)
    (hGH : ∀ i, (fun p => G p i) =ᵐ[volume.restrict Q] (fun p => H p i)) :
    WeakGradientOn Q v H := by
  intro φ hφ i
  have hLeft : (∫ p, v p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q) =
      ∫ p, u p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q := by
    apply integral_congr_ae
    filter_upwards [huv] with p hp
    rw [hp]
  have hRight : (∫ p, G p i*φ p ∂volume.restrict Q) =
      ∫ p, H p i*φ p ∂volume.restrict Q := by
    apply integral_congr_ae
    filter_upwards [hGH i] with p hp
    rw [hp]
  exact hLeft.trans ((hWeak φ hφ i).trans (congrArg Neg.neg hRight))

theorem weak_second_spatial_derivatives_commute_ae {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    {Z : Point n → Yau.RIdx n → Yau.RIdx n → ℝ}
    (hWu : WeakGradientOn Q u G)
    (hZ : ∀ i j, MemLp (fun p => Z p i j) 2 (volume.restrict Q))
    (hWG : ∀ j, WeakGradientOn Q (fun p => G p j) (fun p i => Z p i j)) :
    ∀ᵐ p ∂volume.restrict Q, ∀ i j, Z p i j = Z p j i := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  apply ae_eq_of_test_integrals_eq hQ (hZ i j) (hZ j i)
  intro φ hφ
  have h1 := hWG j φ hφ i
  have h2 := hWG i φ hφ j
  have h3 := hWu (fun p => fderiv ℝ φ p (Yau.realVec i,0))
    (test_directionalDerivative hφ (Yau.realVec i,0)) j
  have h4 := hWu (fun p => fderiv ℝ φ p (Yau.realVec j,0))
    (test_directionalDerivative hφ (Yau.realVec j,0)) i
  have hComm : (fun p => u p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (Yau.realVec j,0)) =
      fun p => u p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec j,0)) p (Yau.realVec i,0) := by
    funext p
    rw [directional_gradient_commute (hφ.1.of_le (by simp))]
  change (∫ p, u p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (Yau.realVec j,0) ∂volume.restrict Q) = _ at h3
  rw [hComm] at h3
  linarith

theorem localEnergy_homogeneous_symmetric_weak_hessian {n : ℕ}
    {O : Set (Space n)} {l r lam upper : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    (hEll : Elliptic (O ×ˢ Set.Ioo l r) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r) :
    ∃ Z : Point n → Yau.RIdx n → Yau.RIdx n → ℝ,
      (∀ i j, MemLp (fun p => Z p i j) 2 (volume.restrict V)) ∧
      (∀ j, WeakGradientOn V (fun p => G p j) (fun p i => Z p i j)) ∧
      (∀ᵐ p ∂volume.restrict V, ∀ i j, Z p i j = Z p j i) := by
  have hEach (j : Yau.RIdx n) :=
    localEnergy_homogeneous_gradient_component_h1 hO hSmooth hEll hE hEq hV hVC hVQ j
  choose Z _hG hZ hWZ using hEach
  have hWu := (weakGradientOn_prod_iff O (Set.Ioo l r) u G).2 hE.1
  have hWuV := weakGradientOn_mono hWu (subset_closure.trans hVQ)
  exact ⟨fun p i j => Z j p i,fun i j => hZ j i,hWZ,
    weak_second_spatial_derivatives_commute_ae hV hWuV (fun i j => hZ j i) hWZ⟩

end Yau.LeafProofs.L16Aux
