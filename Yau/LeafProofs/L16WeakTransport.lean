import Yau.LeafProofs.L16WeakDifferenceQuotient
import Yau.LeafProofs.L16EnergyEquation

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

private theorem test_add_right {n : ℕ} {φ : Point n → ℝ}
    (hφ : Test (Set.univ : Set (Point n)) φ) (v : Point n) :
    Test Set.univ (fun p => φ (p+v)) := by
  refine ⟨hφ.1.comp (contDiff_id.add contDiff_const),?_,Set.subset_univ _⟩
  exact hφ.2.1.comp_homeomorph (Homeomorph.addRight v)

private theorem test_memLp_two {n : ℕ} {Q : Set (Point n)} {φ : Point n → ℝ}
    (hφ : Test Q φ) : MemLp φ 2 volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1

private theorem test_mul_integrable {n : ℕ} {Q : Set (Point n)}
    {w φ : Point n → ℝ} (hw : MemLp w 2 volume) (hφ : Test Q φ) :
    Integrable (fun p => w p*φ p) volume :=
  hw.integrable_mul (test_memLp_two hφ)

private theorem spatialDerivative_add_right {n : ℕ} (φ : Point n → ℝ)
    (v : Point n) (p : Point n) (i : Yau.RIdx n) :
    d (fun x => φ ((x,p.2)+v)) p.1 i =
      d (fun x => φ (x,(p+v).2)) (p+v).1 i := by
  unfold d
  exact congrArg (fun L => L (Yau.realVec i))
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun x => φ (x,p.2+v.2)) (x := p.1) v.1)

private theorem timeDerivative_add_right {n : ℕ} (φ : Point n → ℝ)
    (v : Point n) (p : Point n) :
    deriv (fun t => φ ((p.1,t)+v)) p.2 =
      deriv (fun t => φ ((p+v).1,t)) (p+v).2 := by
  exact deriv_comp_add_const (fun t => φ (p.1+v.1,t)) v.2 p.2

/-- Haar translation preserves the genuine global weak spatial-gradient identity. -/
theorem weakGradient_spatialTranslate {n : ℕ}
    {w : Point n → ℝ} {H : Point n → Yau.RIdx n → ℝ}
    (_hw : MemLp w 2 volume) (_hH : ∀ i, MemLp (fun p => H p i) 2 volume)
    (hGrad : WeakGradient Set.univ Set.univ w H) (v : Space n) :
    WeakGradient Set.univ Set.univ (spatialTranslate v w)
      (fun p i => spatialTranslate v (fun q => H q i) p) := by
  intro φ hφ i
  have hφ' : Test (Set.univ : Set (Point n)) φ := by simpa only [Set.univ_prod_univ] using hφ
  let V : Point n := (v,0)
  let ψ : Point n → ℝ := fun p => φ (p+-V)
  have hψ : Test (Set.univ ×ˢ Set.univ) ψ := by
    simpa only [Set.univ_prod_univ] using test_add_right hφ' (-V)
  have h := hGrad ψ hψ i
  rw [productVolume_eq_restrict] at h ⊢
  simp only [Set.univ_prod_univ,Measure.restrict_univ] at h ⊢
  have hLeft := integral_add_right_eq_self (μ := volume)
    (fun p : Point n => w p*d (fun x => ψ (x,p.2)) p.1 i) V
  have hRight := integral_add_right_eq_self (μ := volume)
    (fun p : Point n => H p i*ψ p) V
  have hDer (p : Point n) : d (fun x => ψ (x,(p+V).2)) (p+V).1 i =
      d (fun x => φ (x,p.2)) p.1 i := by
    dsimp only [ψ]
    rw [spatialDerivative_add_right]
    simp only [add_neg_cancel_right]
  simp_rw [hDer] at hLeft
  simp only [ψ,add_neg_cancel_right] at hRight
  have hRes : (∫ p, w (p+V)*d (fun x => φ (x,p.2)) p.1 i) =
      -(∫ p, H (p+V) i*φ p) := by
    rw [hLeft,hRight]
    exact h
  simpa only [V,spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero] using hRes

private theorem weakGradient_const_mul_sub {n : ℕ}
    {w₁ w₂ : Point n → ℝ} {H₁ H₂ : Point n → Yau.RIdx n → ℝ}
    (hw₁ : MemLp w₁ 2 volume) (hw₂ : MemLp w₂ 2 volume)
    (hH₁ : ∀ i, MemLp (fun p => H₁ p i) 2 volume)
    (hH₂ : ∀ i, MemLp (fun p => H₂ p i) 2 volume)
    (h₁ : WeakGradient Set.univ Set.univ w₁ H₁)
    (h₂ : WeakGradient Set.univ Set.univ w₂ H₂) (c : ℝ) :
    WeakGradient Set.univ Set.univ (fun p => c*(w₁ p-w₂ p))
      (fun p i => c*(H₁ p i-H₂ p i)) := by
  intro φ hφ i
  have h₁' := h₁ φ hφ i
  have h₂' := h₂ φ hφ i
  rw [productVolume_eq_restrict] at h₁' h₂' ⊢
  simp only [Set.univ_prod_univ,Measure.restrict_univ] at h₁' h₂' ⊢
  have hL₁ := test_mul_integrable hw₁ (test_spatialDerivative hφ i)
  have hL₂ := test_mul_integrable hw₂ (test_spatialDerivative hφ i)
  have hR₁ := test_mul_integrable (hH₁ i) hφ
  have hR₂ := test_mul_integrable (hH₂ i) hφ
  simp_rw [mul_assoc,sub_mul,mul_sub]
  rw [integral_sub (hL₁.const_mul c) (hL₂.const_mul c),
    integral_sub (hR₁.const_mul c) (hR₂.const_mul c)]
  simp_rw [integral_const_mul,h₁',h₂']
  ring

/-- The normalized spatial difference quotient preserves the actual weak gradient. -/
theorem weakGradient_spatialDifferenceQuotient {n : ℕ}
    {w : Point n → ℝ} {H : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hH : ∀ i, MemLp (fun p => H p i) 2 volume)
    (hGrad : WeakGradient Set.univ Set.univ w H) (e : Space n) (h : ℝ) :
    WeakGradient Set.univ Set.univ (spatialDifferenceQuotient w e h)
      (fun p i => spatialDifferenceQuotient (fun q => H q i) e h p) := by
  have hwT : MemLp (spatialTranslate (h • e) w) 2 volume := by
    change MemLp (fun p : Point n => w (p.1+h • e,p.2)) 2 volume
    simpa only [spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero,Function.comp_def] using
      hw.comp_measurePreserving (measurePreserving_add_right volume ((h • e,0) : Point n))
  have hHT (i : Yau.RIdx n) : MemLp (fun p => spatialTranslate (h • e) (fun q => H q i) p) 2 volume := by
    simpa only [spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero,Function.comp_def] using
      (hH i).comp_measurePreserving (measurePreserving_add_right volume ((h • e,0) : Point n))
  exact weakGradient_const_mul_sub hwT hw hHT hH
    (weakGradient_spatialTranslate hw hH hGrad (h • e)) hGrad h⁻¹

/-- Haar translation preserves the concrete global distributional evolution equation. -/
theorem weakDivergenceEvolution_spatialTranslate {n : ℕ}
    {w R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (_hw : MemLp w 2 volume) (_hP : ∀ i, MemLp (fun p => P p i) 2 volume)
    (_hR : MemLp R 2 volume)
    (hW : WeakDivergenceEvolution Set.univ Set.univ w P R) (v : Space n) :
    WeakDivergenceEvolution Set.univ Set.univ (spatialTranslate v w)
      (fun p i => spatialTranslate v (fun q => P q i) p) (spatialTranslate v R) := by
  intro φ hφ
  have hφ' : Test (Set.univ : Set (Point n)) φ := by simpa only [Set.univ_prod_univ] using hφ
  let V : Point n := (v,0)
  let ψ : Point n → ℝ := fun p => φ (p+-V)
  have hψ : Test (Set.univ ×ˢ Set.univ) ψ := by
    simpa only [Set.univ_prod_univ] using test_add_right hφ' (-V)
  have h := hW ψ hψ
  rw [productVolume_eq_restrict] at h ⊢
  simp only [Set.univ_prod_univ,Measure.restrict_univ] at h ⊢
  have hShift := integral_add_right_eq_self (μ := volume)
    (fun p : Point n => -w p*deriv (fun t => ψ (p.1,t)) p.2+
      (∑ i, P p i*d (fun x => ψ (x,p.2)) p.1 i)-R p*ψ p) V
  have hDerS (p : Point n) (i : Yau.RIdx n) :
      d (fun x => ψ (x,(p+V).2)) (p+V).1 i =
        d (fun x => φ (x,p.2)) p.1 i := by
    dsimp only [ψ]
    rw [spatialDerivative_add_right]
    simp only [add_neg_cancel_right]
  have hDerT (p : Point n) : deriv (fun t => ψ ((p+V).1,t)) (p+V).2 =
      deriv (fun t => φ (p.1,t)) p.2 := by
    dsimp only [ψ]
    rw [timeDerivative_add_right]
    simp only [add_neg_cancel_right]
  simp_rw [hDerS,hDerT] at hShift
  simp only [ψ,add_neg_cancel_right] at hShift
  have hRes : (∫ p, -w (p+V)*deriv (fun t => φ (p.1,t)) p.2+
      (∑ i, P (p+V) i*d (fun x => φ (x,p.2)) p.1 i)-R (p+V)*φ p) = 0 := by
    rw [hShift]
    exact h
  simpa only [V,spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero] using hRes

private theorem evolutionIntegrand_integrable {n : ℕ} {Q : Set (Point n)}
    {w R φ : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hP : ∀ i, MemLp (fun p => P p i) 2 volume)
    (hR : MemLp R 2 volume) (hφ : Test Q φ) :
    Integrable (fun p => -w p*deriv (fun t => φ (p.1,t)) p.2+
      (∑ i, P p i*d (fun x => φ (x,p.2)) p.1 i)-R p*φ p) volume := by
  have hT := (test_mul_integrable hw (test_timeDerivative hφ)).neg
  have hS : Integrable (fun p => ∑ i, P p i*d (fun x => φ (x,p.2)) p.1 i) volume := by
    exact integrable_finsetSum _ (fun i _ => test_mul_integrable (hP i) (test_spatialDerivative hφ i))
  convert! (hT.add hS).sub (test_mul_integrable hR hφ) using 1
  ext p
  simp only [Pi.neg_apply,Pi.add_apply,Pi.sub_apply,neg_mul]

private theorem weakDivergenceEvolution_const_mul_sub {n : ℕ}
    {w₁ w₂ R₁ R₂ : Point n → ℝ} {P₁ P₂ : Point n → Yau.RIdx n → ℝ}
    (hw₁ : MemLp w₁ 2 volume) (hw₂ : MemLp w₂ 2 volume)
    (hP₁ : ∀ i, MemLp (fun p => P₁ p i) 2 volume)
    (hP₂ : ∀ i, MemLp (fun p => P₂ p i) 2 volume)
    (hR₁ : MemLp R₁ 2 volume) (hR₂ : MemLp R₂ 2 volume)
    (h₁ : WeakDivergenceEvolution Set.univ Set.univ w₁ P₁ R₁)
    (h₂ : WeakDivergenceEvolution Set.univ Set.univ w₂ P₂ R₂) (c : ℝ) :
    WeakDivergenceEvolution Set.univ Set.univ (fun p => c*(w₁ p-w₂ p))
      (fun p i => c*(P₁ p i-P₂ p i)) (fun p => c*(R₁ p-R₂ p)) := by
  intro φ hφ
  have h₁' := h₁ φ hφ
  have h₂' := h₂ φ hφ
  rw [productVolume_eq_restrict] at h₁' h₂' ⊢
  simp only [Set.univ_prod_univ,Measure.restrict_univ] at h₁' h₂' ⊢
  have hA₁ := evolutionIntegrand_integrable hw₁ hP₁ hR₁ hφ
  have hA₂ := evolutionIntegrand_integrable hw₂ hP₂ hR₂ hφ
  have hEq (p : Point n) :
      -(c*(w₁ p-w₂ p))*deriv (fun t => φ (p.1,t)) p.2+
        (∑ i, c*(P₁ p i-P₂ p i)*d (fun x => φ (x,p.2)) p.1 i)-c*(R₁ p-R₂ p)*φ p =
      c*((-w₁ p*deriv (fun t => φ (p.1,t)) p.2+
        (∑ i, P₁ p i*d (fun x => φ (x,p.2)) p.1 i)-R₁ p*φ p)-
        (-w₂ p*deriv (fun t => φ (p.1,t)) p.2+
        (∑ i, P₂ p i*d (fun x => φ (x,p.2)) p.1 i)-R₂ p*φ p)) := by
    have hSum : (∑ i, c*(P₁ p i-P₂ p i)*d (fun x => φ (x,p.2)) p.1 i) =
        c*((∑ i, P₁ p i*d (fun x => φ (x,p.2)) p.1 i)-
          ∑ i, P₂ p i*d (fun x => φ (x,p.2)) p.1 i) := by
      rw [← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hSum]
    ring
  simp_rw [hEq]
  rw [integral_const_mul,integral_sub hA₁ hA₂,h₁',h₂']
  simp only [sub_self,mul_zero]

/-- Normalized spatial difference quotients preserve the genuine weak evolution. -/
theorem weakDivergenceEvolution_spatialDifferenceQuotient {n : ℕ}
    {w R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hP : ∀ i, MemLp (fun p => P p i) 2 volume)
    (hR : MemLp R 2 volume)
    (hW : WeakDivergenceEvolution Set.univ Set.univ w P R) (e : Space n) (h : ℝ) :
    WeakDivergenceEvolution Set.univ Set.univ (spatialDifferenceQuotient w e h)
      (fun p i => spatialDifferenceQuotient (fun q => P q i) e h p)
      (spatialDifferenceQuotient R e h) := by
  have hwT : MemLp (spatialTranslate (h • e) w) 2 volume := by
    change MemLp (fun p : Point n => w (p.1+h • e,p.2)) 2 volume
    simpa only [spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero,Function.comp_def] using
      hw.comp_measurePreserving (measurePreserving_add_right volume ((h • e,0) : Point n))
  have hPT (i : Yau.RIdx n) : MemLp (fun p => spatialTranslate (h • e) (fun q => P q i) p) 2 volume := by
    simpa only [spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero,Function.comp_def] using
      (hP i).comp_measurePreserving (measurePreserving_add_right volume ((h • e,0) : Point n))
  have hRT : MemLp (spatialTranslate (h • e) R) 2 volume := by
    change MemLp (fun p : Point n => R (p.1+h • e,p.2)) 2 volume
    simpa only [spatialTranslate,spatialTranslatePoint,Prod.add_def,add_zero,Function.comp_def] using
      hR.comp_measurePreserving (measurePreserving_add_right volume ((h • e,0) : Point n))
  exact weakDivergenceEvolution_const_mul_sub hwT hw hPT hP hRT hR
    (weakDivergenceEvolution_spatialTranslate hw hP hR hW (h • e)) hW h⁻¹

/-- The exact matrix-flux product rule for the normalized spatial quotient. -/
theorem spatialDifferenceQuotient_energyFlux {n : ℕ}
    (a : Point n → Mat n) (H : Point n → Yau.RIdx n → ℝ)
    (e : Space n) (h : ℝ) (p : Point n) (i : Yau.RIdx n) :
    spatialDifferenceQuotient (fun q => energyFlux a H q i) e h p =
      energyFlux (spatialTranslate (h • e) a)
        (fun q j => spatialDifferenceQuotient (fun z => H z j) e h q) p i+
      energyFlux (spatialDifferenceQuotient a e h) H p i := by
  simp only [spatialDifferenceQuotient,energyFlux,spatialTranslate,spatialTranslatePoint,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,Finset.mul_sum,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact finite-dimensional drift product rule for the normalized quotient. -/
theorem spatialDifferenceQuotient_driftPairing {n : ℕ}
    (c H : Point n → Yau.RIdx n → ℝ) (e : Space n) (h : ℝ) (p : Point n) :
    spatialDifferenceQuotient (fun q => ∑ j, c q j*H q j) e h p =
      (∑ j, spatialTranslate (h • e) c p j*
        spatialDifferenceQuotient (fun q => H q j) e h p)+
      ∑ j, spatialDifferenceQuotient (fun q => c q j) e h p*H p j := by
  simp only [spatialDifferenceQuotient,spatialTranslate,spatialTranslatePoint,
    smul_eq_mul,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Yau.LeafProofs.L16Aux
