import Yau.Proofs.F03CaloricWeakSpace

/-! Exact weak characterization and genuine L² realization in the closed space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem weakGradient_congr_ae {O : Set (Space d)} {I : Set ℝ}
    {u v : Point d → ℝ} {G H : Point d → RIdx d → ℝ}
    (hW : WeakGradient O I u G) (hu : u =ᵐ[productVolume O I] v)
    (hG : ∀ i, (fun p => G p i) =ᵐ[productVolume O I] (fun p => H p i)) :
    WeakGradient O I v H := by
  intro φ hφ i
  calc
    _ = ∫ p, u p*Parabolic.d (fun x => φ (x,p.2)) p.1 i ∂productVolume O I := by
      apply integral_congr_ae
      filter_upwards [hu] with p hp
      exact congrArg (fun x : ℝ => x*Parabolic.d (fun x => φ (x,p.2)) p.1 i) hp.symm
    _ = -(∫ p, G p i*φ p ∂productVolume O I) := hW φ hφ i
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hG i] with p hp
      exact congrArg (fun x : ℝ => x*φ p) hp

theorem weakEquation_congr_ae {O : Set (Space d)} {I : Set ℝ}
    {a : Point d → Mat d} {b : Point d → RIdx d → ℝ} {f u v : Point d → ℝ}
    {G H : Point d → RIdx d → ℝ}
    (hW : WeakEquation O I a b f u G) (hu : u =ᵐ[productVolume O I] v)
    (hG : ∀ i, (fun p => G p i) =ᵐ[productVolume O I] (fun p => H p i)) :
    WeakEquation O I a b f v H := by
  intro φ hφ
  have heq : (∫ p, -v p*deriv (fun t => φ (p.1,t)) p.2+
      (∑ i,∑ j,a p i j*H p j*Parabolic.d (fun x => φ (x,p.2)) p.1 i)-
      (∑ j,(b p j-∑ i,Parabolic.d (fun x => a (x,p.2) i j) p.1 i)*H p j*φ p) ∂productVolume O I)=
      ∫ p, -u p*deriv (fun t => φ (p.1,t)) p.2+
      (∑ i,∑ j,a p i j*G p j*Parabolic.d (fun x => φ (x,p.2)) p.1 i)-
      (∑ j,(b p j-∑ i,Parabolic.d (fun x => a (x,p.2) i j) p.1 i)*G p j*φ p) ∂productVolume O I := by
    apply integral_congr_ae
    filter_upwards [hu,ae_all_iff.mpr hG] with p hp hGp
    simp only [← hp,← hGp]
  exact heq.trans (hW φ hφ)

theorem caloricSubmodule_mem_iff_weak (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (e : CaloricAmbient (O ×ˢ I)) :
    e ∈ caloricSubmodule (O ×ˢ I) hD a b hAB ↔
      WeakGradient O I (e.1 : Point d → ℝ) (fun p i => e.2 i p) ∧
      WeakEquation O I a b (fun _ => 0) (e.1 : Point d → ℝ) (fun p i => e.2 i p) := by
  constructor
  · intro he
    exact ⟨caloricSpace_weakGradient O I hD a b hAB ⟨e,he⟩,
      caloricSpace_weakEquation O I hD a b hAB ⟨e,he⟩⟩
  · rintro ⟨hG,hE⟩
    refine ⟨?_,?_⟩
    · intro φ i
      rw [caloricGradientTestCLM_apply]
      have h := hG φ.val φ.2 i
      rw [LeafProofs.L16Aux.productVolume_eq_restrict] at h
      linarith only [h]
    · intro φ
      rw [caloricEquationTestCLM_apply]
      have h := hE φ.val φ.2
      rw [LeafProofs.L16Aux.productVolume_eq_restrict] at h
      simpa only [zero_mul,integral_zero] using h

def caloricOfWeak (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (v : Point d → ℝ) (G : Point d → RIdx d → ℝ)
    (hv : MemLp v 2 (volume.restrict (O ×ˢ I)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict (O ×ˢ I)))
    (hWG : WeakGradient O I v G) (hWE : WeakEquation O I a b (fun _ => 0) v G) :
    CaloricSpace (O ×ˢ I) hD a b hAB := by
  refine ⟨(hv.toLp v,fun i => (hG i).toLp (fun p => G p i)),?_⟩
  apply (caloricSubmodule_mem_iff_weak O I hD a b hAB _).mpr
  have hval : v =ᵐ[productVolume O I] (hv.toLp v : Point d → ℝ) := by
    rw [LeafProofs.L16Aux.productVolume_eq_restrict]
    exact hv.coeFn_toLp.symm
  have hgrad : ∀ i, (fun p => G p i) =ᵐ[productVolume O I]
      ((hG i).toLp (fun p => G p i) : Point d → ℝ) := by
    intro i
    rw [LeafProofs.L16Aux.productVolume_eq_restrict]
    exact (hG i).coeFn_toLp.symm
  exact ⟨weakGradient_congr_ae hWG hval hgrad,weakEquation_congr_ae hWE hval hgrad⟩

theorem caloricOfWeak_value_ae (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (v : Point d → ℝ) (G : Point d → RIdx d → ℝ)
    (hv : MemLp v 2 (volume.restrict (O ×ˢ I)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict (O ×ˢ I)))
    (hWG : WeakGradient O I v G) (hWE : WeakEquation O I a b (fun _ => 0) v G) :
    ((caloricOfWeak O I hD a b hAB v G hv hG hWG hWE).val.1 : Point d → ℝ) =ᵐ[volume.restrict (O ×ˢ I)] v :=
  hv.coeFn_toLp

end Yau.Proofs.F03Aux
