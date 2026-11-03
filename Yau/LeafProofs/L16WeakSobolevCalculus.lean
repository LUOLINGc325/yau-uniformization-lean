import Yau.LeafProofs.L16WeakSecondDerivative

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Concrete weak spatial derivatives on an arbitrary open coordinate region. -/
def WeakGradientOn {n : ℕ} (Q : Set (Point n)) (u : Point n → ℝ)
    (G : Point n → Yau.RIdx n → ℝ) : Prop :=
  ∀ (φ : Point n → ℝ), Test Q φ → ∀ i,
    (∫ p, u p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q) =
      -(∫ p, G p i*φ p ∂volume.restrict Q)

theorem weakGradientOn_prod_iff {n : ℕ} (O : Set (Space n)) (I : Set ℝ)
    (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ) :
    WeakGradientOn (O ×ˢ I) u G ↔ WeakGradient O I u G := by
  unfold WeakGradientOn WeakGradient
  simp only [productVolume_eq_restrict]
  constructor <;> intro h φ hφ i
  · simpa only [d_eq_joint_fderiv (hφ.1.differentiable (by simp) _) i] using h φ hφ i
  · simpa only [d_eq_joint_fderiv (hφ.1.differentiable (by simp) _) i] using h φ hφ i

theorem test_pairing_integral_restrict {n : ℕ} {Q : Set (Point n)}
    {φ : Point n → ℝ} (hφ : Test Q φ) (f : Point n → ℝ) :
    (∫ p, f p*φ p ∂volume.restrict Q) = ∫ p, f p*φ p := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hp' : p ∉ tsupport φ := fun h => hp (hφ.2.2 h)
  rw [image_eq_zero_of_notMem_tsupport hp',mul_zero]

theorem weakGradientOn_mono {n : ℕ} {Q V : Set (Point n)}
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hWeak : WeakGradientOn Q u G) (hVQ : V ⊆ Q) : WeakGradientOn V u G := by
  intro φ hφ i
  have hφQ : Test Q φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hVQ⟩
  have h := hWeak φ hφQ i
  rw [test_pairing_integral_restrict (test_directionalDerivative hφQ (Yau.realVec i,0)) u,
    test_pairing_integral_restrict hφQ (fun p => G p i)] at h
  rw [test_pairing_integral_restrict (test_directionalDerivative hφ (Yau.realVec i,0)) u,
    test_pairing_integral_restrict hφ (fun p => G p i)]
  exact h

theorem localEnergy_homogeneous_gradient_component_h1 {n : ℕ}
    {O : Set (Space n)} {l r lam upper : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    (hEll : Elliptic (O ×ˢ Set.Ioo l r) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r) (j : Yau.RIdx n) :
    ∃ Z : Point n → Yau.RIdx n → ℝ, MemLp (fun p => G p j) 2 (volume.restrict V) ∧
      (∀ i, MemLp (fun p => Z p i) 2 (volume.restrict V)) ∧ WeakGradientOn V (fun p => G p j) Z := by
  have hEach (i : Yau.RIdx n) :=
    localEnergy_homogeneous_spatial_weak_derivative_gain hO hSmooth hEll hE hEq hV hVC hVQ i j
  choose Z hZ hWeak using hEach
  have hG := (localEnergy_memLp_on_compact hO hE hVC hVQ).2 j
  refine ⟨fun p i => Z i p,hG.mono_measure (Measure.restrict_mono subset_closure le_rfl),hZ,?_⟩
  intro φ hφ i
  simpa only [d_eq_joint_fderiv (hφ.1.differentiable (by simp) _) i] using hWeak i φ hφ

theorem smooth_compact_spatial_derivative_bound {n : ℕ} {g : Point n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ (∀ p, |g p| ≤ C) ∧ ∀ p i, |fderiv ℝ g p (Yau.realVec i,0)| ≤ C := by
  obtain ⟨C,hC,hVal,hDeriv,_hLip⟩ := smooth_compact_global_bounds hg hcg
  refine ⟨C,hC,fun p => by simpa only [Real.norm_eq_abs] using hVal p,?_⟩
  intro p i
  have hEval := (fderiv ℝ g p).le_opNorm (Yau.realVec i,0)
  have hUnit : ‖((Yau.realVec i,0) : Point n)‖ = 1 := by
    simp only [Prod.norm_def,realVec_norm,norm_zero,max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hUnit,mul_one,Real.norm_eq_abs] at hEval
  exact hEval.trans (hDeriv p)

theorem weakGradientOn_smooth_compact_mul {n : ℕ} {Q : Set (Point n)}
    {u g : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict Q)) (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict Q))
    (hWeak : WeakGradientOn Q u G) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    MemLp (fun p => g p*u p) 2 (volume.restrict Q) ∧
      (∀ i, MemLp (fun p => g p*G p i+u p*fderiv ℝ g p (Yau.realVec i,0)) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (fun p => g p*u p)
        (fun p i => g p*G p i+u p*fderiv ℝ g p (Yau.realVec i,0)) := by
  obtain ⟨C,hC,hVal,hDeriv⟩ := smooth_compact_spatial_derivative_bound hg hcg
  have hgu : MemLp (fun p => g p*u p) 2 (volume.restrict Q) :=
    continuous_bounded_mul_memLp hg.continuous hVal hu
  have hgG (i : Yau.RIdx n) : MemLp (fun p => g p*G p i) 2 (volume.restrict Q) :=
    continuous_bounded_mul_memLp hg.continuous hVal (hG i)
  have huDg (i : Yau.RIdx n) :
      MemLp (fun p => u p*fderiv ℝ g p (Yau.realVec i,0)) 2 (volume.restrict Q) := by
    have hDCont : Continuous (fun p => fderiv ℝ g p (Yau.realVec i,0)) :=
      ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    have h := continuous_bounded_mul_memLp hDCont (fun p => hDeriv p i) hu
    convert! h using 1
    ext p
    ring
  refine ⟨hgu,fun i => (hgG i).add (huDg i),?_⟩
  intro φ hφ i
  have hφ2 := test_memLp hφ
  have hDφ2 := test_memLp (test_directionalDerivative hφ (Yau.realVec i,0))
  have hX : Integrable (fun p => (g p*u p)*fderiv ℝ φ p (Yau.realVec i,0)) (volume.restrict Q) :=
    hgu.integrable_mul hDφ2
  have hY : Integrable (fun p => (u p*fderiv ℝ g p (Yau.realVec i,0))*φ p) (volume.restrict Q) :=
    (huDg i).integrable_mul hφ2
  have hZ : Integrable (fun p => (g p*G p i)*φ p) (volume.restrict Q) :=
    (hgG i).integrable_mul hφ2
  have h := hWeak (fun p => φ p*g p) (test_mul_smooth hφ hg) i
  have hD (p : Point n) : fderiv ℝ (fun q => φ q*g q) p (Yau.realVec i,0) =
      φ p*fderiv ℝ g p (Yau.realVec i,0)+g p*fderiv ℝ φ p (Yau.realVec i,0) := by
    rw [fderiv_fun_mul (hφ.1.differentiable (by simp) p) (hg.differentiable (by simp) p)]
    rfl
  have hLeft : (fun p => u p*fderiv ℝ (fun q => φ q*g q) p (Yau.realVec i,0)) =
      fun p => (g p*u p)*fderiv ℝ φ p (Yau.realVec i,0)+(u p*fderiv ℝ g p (Yau.realVec i,0))*φ p := by
    funext p
    rw [hD]
    ring
  have hRight : (fun p => G p i*(φ p*g p)) = fun p => (g p*G p i)*φ p := by
    funext p
    ring
  rw [hLeft,hRight] at h
  have hSplit1 := integral_add hX hY
  rw [hSplit1] at h
  have hGoal : (fun p => (g p*G p i+u p*fderiv ℝ g p (Yau.realVec i,0))*φ p) =
      fun p => (g p*G p i)*φ p+(u p*fderiv ℝ g p (Yau.realVec i,0))*φ p := by
    funext p
    ring
  rw [hGoal]
  have hSplit2 := integral_add hZ hY
  rw [hSplit2]
  linarith

theorem weakGradientOn_zero {n : ℕ} (Q : Set (Point n)) :
    WeakGradientOn Q (fun _ => 0) (fun _ _ => 0) := by
  intro φ hφ i
  simp

theorem weakGradientOn_add {n : ℕ} {Q : Set (Point n)}
    {u v : Point n → ℝ} {G H : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict Q)) (hv : MemLp v 2 (volume.restrict Q))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict Q))
    (hH : ∀ i, MemLp (fun p => H p i) 2 (volume.restrict Q))
    (hWu : WeakGradientOn Q u G) (hWv : WeakGradientOn Q v H) :
    WeakGradientOn Q (fun p => u p+v p) (fun p i => G p i+H p i) := by
  intro φ hφ i
  have hDφ := test_memLp (test_directionalDerivative hφ (Yau.realVec i,0))
  have hφ2 := test_memLp hφ
  have hSplit1 := integral_add (hu.integrable_mul hDφ) (hv.integrable_mul hDφ)
  have hSplit2 := integral_add ((hG i).integrable_mul hφ2) ((hH i).integrable_mul hφ2)
  simp only [Pi.mul_apply] at hSplit1 hSplit2
  simp_rw [add_mul]
  rw [hSplit1,hSplit2,hWu φ hφ i,hWv φ hφ i]
  ring

theorem weakGradientOn_const_mul {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hWu : WeakGradientOn Q u G) (c : ℝ) :
    WeakGradientOn Q (fun p => c*u p) (fun p i => c*G p i) := by
  intro φ hφ i
  simp_rw [mul_assoc]
  rw [integral_const_mul,integral_const_mul,hWu φ hφ i]
  ring

theorem weakGradientOn_finset_sum {n : ℕ} {Q : Set (Point n)}
    {ι : Type*} (s : Finset ι) (u : ι → Point n → ℝ)
    (G : ι → Point n → Yau.RIdx n → ℝ)
    (hu : ∀ k ∈ s, MemLp (u k) 2 (volume.restrict Q))
    (hG : ∀ k ∈ s, ∀ i, MemLp (fun p => G k p i) 2 (volume.restrict Q))
    (hWu : ∀ k ∈ s, WeakGradientOn Q (u k) (G k)) :
    MemLp (fun p => ∑ k ∈ s, u k p) 2 (volume.restrict Q) ∧
      (∀ i, MemLp (fun p => ∑ k ∈ s, G k p i) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (fun p => ∑ k ∈ s, u k p) (fun p i => ∑ k ∈ s, G k p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (And.intro (MemLp.zero' : MemLp (fun _ : Point n => (0 : ℝ)) 2 (volume.restrict Q))
      (And.intro (fun _ : Yau.RIdx n => (MemLp.zero' : MemLp (fun _ : Point n => (0 : ℝ)) 2 (volume.restrict Q)))
        (weakGradientOn_zero Q)))
  | @insert k s hks ih =>
    have hs := ih (fun z hz => hu z (Finset.mem_insert_of_mem hz))
      (fun z hz => hG z (Finset.mem_insert_of_mem hz))
      (fun z hz => hWu z (Finset.mem_insert_of_mem hz))
    have huSum : MemLp (fun p => u k p+∑ z ∈ s, u z p) 2 (volume.restrict Q) := by
      convert! (hu k (Finset.mem_insert_self k s)).add hs.1 using 1
    have hGSum (i : Yau.RIdx n) :
        MemLp (fun p => G k p i+∑ z ∈ s, G z p i) 2 (volume.restrict Q) := by
      convert! (hG k (Finset.mem_insert_self k s) i).add (hs.2.1 i) using 1
    simpa only [Finset.sum_insert hks] using
      (And.intro huSum (And.intro hGSum
        (weakGradientOn_add (hu k (Finset.mem_insert_self k s)) hs.1
          (hG k (Finset.mem_insert_self k s)) hs.2.1
          (hWu k (Finset.mem_insert_self k s)) hs.2.2)))

end Yau.LeafProofs.L16Aux
