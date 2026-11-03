import Yau.LeafProofs.L16WeakMollification
import Yau.LeafProofs.L16WordSource

open MeasureTheory Filter
open scoped Topology ContDiff Convolution Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def energyFlux {n : ℕ} (a : Point n → Mat n) (G : Point n → Yau.RIdx n → ℝ)
    (p : Point n) (i : Yau.RIdx n) : ℝ := ∑ j, a p i j*G p j

def energyDrift {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (p : Point n) (j : Yau.RIdx n) : ℝ := b p j-∑ i, d (fun x => a (x,p.2) i j) p.1 i

/-- The actual distributional evolution equation `w_t = div P + R`.
Its test class and integration measure are the frozen concrete ones. -/
def WeakDivergenceEvolution {n : ℕ} (O : Set (Space n)) (I : Set ℝ)
    (w : Point n → ℝ) (P : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ) : Prop :=
  ∀ φ : Point n → ℝ, Test (O ×ˢ I) φ →
    (∫ p, -w p*deriv (fun t => φ (p.1,t)) p.2 +
      (∑ i, P p i*d (fun x => φ (x,p.2)) p.1 i)-R p*φ p ∂productVolume O I) = 0

theorem weakEquation_homogeneous_divergence {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    {G : Point n → Yau.RIdx n → ℝ}
    (hEq : WeakEquation O I a b (fun _ => 0) u G) :
    WeakDivergenceEvolution O I u (energyFlux a G)
      (fun p => ∑ j, energyDrift a b p j*G p j) := by
  intro φ hφ
  have h := hEq φ hφ
  simp only [zero_mul,integral_zero] at h
  simpa only [energyFlux,energyDrift,Finset.sum_mul] using h

theorem test_timeDerivative_eq_joint_fderiv {n : ℕ} {φ : Point n → ℝ} {p : Point n}
    (hφ : DifferentiableAt ℝ φ p) :
    deriv (fun t => φ (p.1,t)) p.2 = fderiv ℝ φ p (0,1) := by
  have hMap : HasDerivAt (fun t : ℝ => (p.1,t)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h := hφ.hasFDerivAt.comp_hasDerivAt p.2 hMap
  exact h.deriv

theorem test_timeDerivative {n : ℕ} {Q : Set (Point n)} {φ : Point n → ℝ}
    (hφ : Test Q φ) : Test Q (fun p : Point n => deriv (fun t => φ (p.1,t)) p.2) := by
  have hEq : (fun p : Point n => deriv (fun t => φ (p.1,t)) p.2) =
      fun p => fderiv ℝ φ p (0,1) := by
    funext p
    exact test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) p)
  rw [hEq]
  exact test_directionalDerivative hφ _

theorem energyDrift_smooth {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients Q a b) (j : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (fun p => energyDrift a b p j) Q := by
  apply (hSmooth.2 j).sub
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_spatialDerivative_of_isOpen hQ
    ((matrixEntryCLM i j).contDiff.comp_contDiffOn hSmooth.1) i

theorem localEnergy_cutoff_flux_memLp {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) (i : Yau.RIdx n) :
    MemLp (fun p => η p*energyFlux a G p i) 2 volume := by
  have hEach (j : Yau.RIdx n) : MemLp (fun p => (η p*a p i j)*G p j) 2 volume := by
    have hTest := test_mul_contDiffOn (hO.prod isOpen_Ioo) hη
      ((matrixEntryCLM i j).contDiff.comp_contDiffOn hSmooth.1)
    exact (localEnergy_cutoff_memLp hO hE hTest.1.continuous hTest.2.1 hTest.2.2).2 j
  have hSum := memLp_finsetSum Finset.univ (fun j _ => hEach j)
  convert! hSum using 1
  ext p
  simp only [energyFlux,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem localEnergy_cutoff_drift_memLp {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) :
    MemLp (fun p => η p*∑ j, energyDrift a b p j*G p j) 2 volume := by
  have hEach (j : Yau.RIdx n) :
      MemLp (fun p => (η p*energyDrift a b p j)*G p j) 2 volume := by
    have hTest := test_mul_contDiffOn (hO.prod isOpen_Ioo) hη
      (energyDrift_smooth (hO.prod isOpen_Ioo) hSmooth j)
    exact (localEnergy_cutoff_memLp hO hE hTest.1.continuous hTest.2.1 hTest.2.2).2 j
  have hSum := memLp_finsetSum Finset.univ (fun j _ => hEach j)
  convert! hSum using 1
  ext p
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem test_timeDerivative_mul {n : ℕ} {η φ : Point n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hφ : ContDiff ℝ ∞ φ) (p : Point n) :
    deriv (fun t => η (p.1,t)*φ (p.1,t)) p.2 =
      η p*deriv (fun t => φ (p.1,t)) p.2+φ p*deriv (fun t => η (p.1,t)) p.2 := by
  rw [test_timeDerivative_eq_joint_fderiv ((hη.mul hφ).differentiable (by simp) p),
    test_timeDerivative_eq_joint_fderiv (hφ.differentiable (by simp) p),
    test_timeDerivative_eq_joint_fderiv (hη.differentiable (by simp) p)]
  rw [fderiv_fun_mul (hη.differentiable (by simp) p) (hφ.differentiable (by simp) p)]
  rfl

def cutoffEvolutionSource {n : ℕ} (w : Point n → ℝ)
    (P : Point n → Yau.RIdx n → ℝ) (R η : Point n → ℝ) (p : Point n) : ℝ :=
  η p*R p+w p*deriv (fun t => η (p.1,t)) p.2-
    ∑ i, P p i*d (fun x => η (x,p.2)) p.1 i

theorem weakDivergenceEvolution_cutoff {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {w : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ} {R η : Point n → ℝ}
    (hW : WeakDivergenceEvolution O I w P R) (hη : Test (O ×ˢ I) η) :
    WeakDivergenceEvolution Set.univ Set.univ (fun p => η p*w p)
      (fun p i => η p*P p i) (cutoffEvolutionSource w P R η) := by
  intro φ hφ
  have hTest := test_mul_smooth hη hφ.1
  have h := hW (fun p => η p*φ p) hTest
  rw [productVolume_eq_restrict] at h
  have hVanish (p : Point n) (hp : p ∉ O ×ˢ I) :
      -w p*deriv (fun t => η (p.1,t)*φ (p.1,t)) p.2+
        (∑ i, P p i*d (fun x => η (x,p.2)*φ (x,p.2)) p.1 i)-R p*(η p*φ p) = 0 := by
    have hZero : η p*φ p = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun q => η q*φ q) (fun h => hp (hTest.2.2 h))
    have hTime : deriv (fun t => η (p.1,t)*φ (p.1,t)) p.2 = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun q : Point n => deriv (fun t => η (q.1,t)*φ (q.1,t)) q.2)
        (fun h => hp ((test_timeDerivative hTest).2.2 h))
    have hSpace (i : Yau.RIdx n) : d (fun x => η (x,p.2)*φ (x,p.2)) p.1 i = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun q : Point n => d (fun x => η (x,q.2)*φ (x,q.2)) q.1 i)
        (fun h => hp ((test_spatialDerivative hTest i).2.2 h))
    simp only [hZero,hTime,hSpace,mul_zero,Finset.sum_const_zero,add_zero,sub_self]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hVanish] at h
  rw [productVolume_eq_restrict]
  simp only [Set.univ_prod_univ,Measure.restrict_univ]
  convert h using 1
  congr 1
  ext p
  rw [test_timeDerivative_mul hη.1 hφ.1]
  simp_rw [test_spatialDerivative_mul hη.1 hφ.1]
  simp only [cutoffEvolutionSource,mul_add,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring_nf
  simp only [Finset.mul_sum,mul_assoc]

theorem cutoffEvolutionSource_compact {n : ℕ} {Q : Set (Point n)}
    (w : Point n → ℝ) (P : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ)
    {η : Point n → ℝ} (hη : Test Q η) :
    HasCompactSupport (cutoffEvolutionSource w P R η) := by
  apply hη.2.1.mono'
  intro p hp
  by_contra hNot
  have hValue : η p = 0 := image_eq_zero_of_notMem_tsupport hNot
  have hTime : deriv (fun t => η (p.1,t)) p.2 = 0 := by
    have hD := test_timeDerivative (Q := tsupport η) ⟨hη.1,hη.2.1,Set.Subset.rfl⟩
    exact image_eq_zero_of_notMem_tsupport
      (f := fun q : Point n => deriv (fun t => η (q.1,t)) q.2)
      (fun h => hNot (hD.2.2 h))
  have hSpace (i : Yau.RIdx n) : d (fun x => η (x,p.2)) p.1 i = 0 := by
    have hSub : tsupport (fun q : Point n => d (fun x => η (x,q.2)) q.1 i) ⊆ tsupport η := by
      have hD := test_spatialDerivative (Q := tsupport η) ⟨hη.1,hη.2.1,Set.Subset.rfl⟩ i
      exact hD.2.2
    exact image_eq_zero_of_notMem_tsupport (f := fun q : Point n => d (fun x => η (x,q.2)) q.1 i)
      (fun h => hNot (hSub h))
  exact hp (by simp only [cutoffEvolutionSource,hValue,hTime,hSpace,zero_mul,mul_zero,
    Finset.sum_const_zero,zero_add,sub_zero])

theorem localEnergy_cutoff_evolutionSource_memLp {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) :
    MemLp (cutoffEvolutionSource u (energyFlux a G)
      (fun p => ∑ j, energyDrift a b p j*G p j) η) 2 volume := by
  have hR := localEnergy_cutoff_drift_memLp hO hSmooth hE hη
  have hTestT := test_timeDerivative hη
  have hU := (localEnergy_cutoff_memLp hO hE hTestT.1.continuous hTestT.2.1 hTestT.2.2).1
  have hU' : MemLp (fun p : Point n => u p*deriv (fun t => η (p.1,t)) p.2) 2 volume := by
    simpa only [mul_comm] using hU
  have hEach (i : Yau.RIdx n) :
      MemLp (fun p : Point n => energyFlux a G p i*d (fun x => η (x,p.2)) p.1 i) 2 volume := by
    have h := localEnergy_cutoff_flux_memLp hO hSmooth hE (test_spatialDerivative hη i) i
    simpa only [mul_comm] using h
  exact (hR.add hU').sub (memLp_finsetSum Finset.univ (fun i _ => hEach i))

theorem weakEquation_homogeneous_cutoff {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    {G : Point n → Yau.RIdx n → ℝ} {η : Point n → ℝ}
    (hEq : WeakEquation O I a b (fun _ => 0) u G) (hη : Test (O ×ˢ I) η) :
    WeakDivergenceEvolution Set.univ Set.univ (fun p => η p*u p)
      (fun p i => η p*energyFlux a G p i)
      (cutoffEvolutionSource u (energyFlux a G) (fun p => ∑ j, energyDrift a b p j*G p j) η) :=
  weakDivergenceEvolution_cutoff (weakEquation_homogeneous_divergence hEq) hη

end Yau.LeafProofs.L16Aux
