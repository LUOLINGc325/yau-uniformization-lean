import Yau.LeafProofs.L16CoefficientForcing
import Yau.LeafProofs.L16WeakTransport
import Yau.LeafProofs.L16DifferenceQuotientToWeak
import Mathlib.Topology.MetricSpace.Thickening

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem compact_spatial_shift_radius {n : ℕ} {K U : Set (Point n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, ∀ v : Space n, ‖v‖ < δ → spatialTranslatePoint v p ∈ U := by
  obtain ⟨δ,hδ,hThick⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ,hδ,?_⟩
  intro p hp v hv
  apply hThick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨p,hp,?_⟩
  simpa only [spatialTranslatePoint,dist_eq_norm,Prod.sub_def,add_sub_cancel_left,sub_self,
    Prod.norm_def,norm_zero,max_eq_left (norm_nonneg v)] using hv

theorem hasCompactSupport_spatialDifferenceQuotient {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {w : Point n → V}
    (hcw : HasCompactSupport w) (e : Space n) (h : ℝ) :
    HasCompactSupport (spatialDifferenceQuotient w e h) := by
  have hT : HasCompactSupport (fun p : Point n => w (p.1+h • e,p.2)) := by
    simpa [Function.comp_def,Homeomorph.addRight,Prod.add_def] using
      hcw.comp_homeomorph (Homeomorph.addRight ((h • e,0) : Point n))
  exact (hT.sub hcw).smul_left

theorem exists_open_common_agreement {n : ℕ} {Q K : Set (Point n)} (hQ : IsOpen Q) (hKQ : K ⊆ Q)
    {η : Point n → ℝ} {a a' : Point n → Mat n} {c c' : Point n → Yau.RIdx n → ℝ}
    (hη : ∀ p ∈ K, η =ᶠ[𝓝 p] (fun _ => 1))
    (hA : ∀ p ∈ K, a' =ᶠ[𝓝 p] a)
    (hC : ∀ p ∈ K, ∀ j, (fun q => c' q j) =ᶠ[𝓝 p] (fun q => c q j)) :
    ∃ U : Set (Point n), IsOpen U ∧ K ⊆ U ∧ U ⊆ Q ∧
      ∀ p ∈ U, η p = 1 ∧ a' p = a p ∧ ∀ j, c' p j = c p j := by
  let S : Set (Point n) := {p | p ∈ Q ∧ η p = 1 ∧ a' p = a p ∧ ∀ j, c' p j = c p j}
  refine ⟨interior S,isOpen_interior,?_,fun p hp => (interior_subset hp).1,?_⟩
  · intro p hp
    apply mem_interior_iff_mem_nhds.mpr
    have hCs : ∀ᶠ q in 𝓝 p, ∀ j, c' q j = c q j := eventually_all.mpr (hC p hp)
    filter_upwards [hQ.mem_nhds (hKQ hp),hη p hp,hA p hp,hCs] with q hq hηq hAq hCq
    exact ⟨hq,hηq,hAq,hCq⟩
  · intro p hp
    exact (interior_subset hp).2

theorem fderiv_cutoff_eq_zero_on_open_plateau {n : ℕ} {U : Set (Point n)}
    (hU : IsOpen U) {η : Point n → ℝ} (hOne : ∀ p ∈ U, η p = 1)
    {p : Point n} (hp : p ∈ U) : fderiv ℝ η p = 0 := by
  have hNear : η =ᶠ[𝓝 p] (fun _ => 1) :=
    Filter.eventually_of_mem (hU.mem_nhds hp) (fun q hq => hOne q hq)
  simpa only [fderiv_fun_const,Pi.zero_apply] using hNear.fderiv_eq (𝕜 := ℝ)

theorem cutoff_fields_eq_on_open_plateau {n : ℕ} {Q U : Set (Point n)}
    (hU : IsOpen U) {η : Point n → ℝ} (hη : Test Q η) (hOne : ∀ p ∈ U, η p = 1)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ)
    (G : Point n → Yau.RIdx n → ℝ) {p : Point n} (hp : p ∈ U) :
    η p*u p = u p ∧
      (∀ i, η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i = G p i) ∧
      (∀ i, η p*energyFlux a G p i = energyFlux a G p i) ∧
      cutoffEvolutionSource u (energyFlux a G) (fun q => ∑ j, energyDrift a b q j*G q j) η p =
        ∑ j, energyDrift a b p j*G p j := by
  have hD := fderiv_cutoff_eq_zero_on_open_plateau hU hOne hp
  have hSpace (i : Yau.RIdx n) : d (fun x => η (x,p.2)) p.1 i = 0 := by
    rw [d_eq_joint_fderiv (hη.1.differentiable (by simp) p) i,hD,zero_apply]
  have hTime : deriv (fun t => η (p.1,t)) p.2 = 0 := by
    rw [test_timeDerivative_eq_joint_fderiv (hη.1.differentiable (by simp) p),hD,zero_apply]
  simp only [cutoffEvolutionSource,hOne p hp,hSpace,hTime,one_mul,mul_zero,add_zero,
    Finset.sum_const_zero,sub_zero,and_self,implies_true]

def localizedWeakGradient {n : ℕ} (η u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ)
    (p : Point n) (i : Yau.RIdx n) : ℝ := η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i

def localizedWeakFlux {n : ℕ} (η : Point n → ℝ) (a : Point n → Mat n)
    (G : Point n → Yau.RIdx n → ℝ) (p : Point n) (i : Yau.RIdx n) : ℝ := η p*energyFlux a G p i

def localizedWeakSource {n : ℕ} (η u : Point n → ℝ) (a : Point n → Mat n)
    (b G : Point n → Yau.RIdx n → ℝ) : Point n → ℝ :=
  cutoffEvolutionSource u (energyFlux a G) (fun p => ∑ j, energyDrift a b p j*G p j) η

theorem localizedWeakFields_regular {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {η : Point n → ℝ} (hη : Test (O ×ˢ Set.Ioo l r) η) :
    MemLp (fun p => η p*u p) 2 volume ∧ HasCompactSupport (fun p => η p*u p) ∧
      (∀ i, MemLp (fun p => localizedWeakGradient η u G p i) 2 volume ∧
        HasCompactSupport (fun p => localizedWeakGradient η u G p i)) ∧
      (∀ i, MemLp (fun p => localizedWeakFlux η a G p i) 2 volume ∧
        HasCompactSupport (fun p => localizedWeakFlux η a G p i)) ∧
      MemLp (localizedWeakSource η u a b G) 2 volume ∧ HasCompactSupport (localizedWeakSource η u a b G) ∧
      WeakGradient Set.univ Set.univ (fun p => η p*u p) (localizedWeakGradient η u G) ∧
      WeakDivergenceEvolution Set.univ Set.univ (fun p => η p*u p)
        (localizedWeakFlux η a G) (localizedWeakSource η u a b G) := by
  obtain ⟨hw,hH,hGrad⟩ := localEnergy_cutoff_weakH1 hO hE hη
  exact ⟨hw,hη.2.1.mul_right,
    fun i => ⟨hH i,hη.2.1.mul_right.add (test_spatialDerivative hη i).2.1.mul_left⟩,
    fun i => ⟨localEnergy_cutoff_flux_memLp hO hSmooth hE hη i,hη.2.1.mul_right⟩,
    localEnergy_cutoff_evolutionSource_memLp hO hSmooth hE hη,
    cutoffEvolutionSource_compact _ _ _ hη,hGrad,weakEquation_homogeneous_cutoff hEq hη⟩

theorem localizedWeakFields_eq_on_open_plateau {n : ℕ} {Q U : Set (Point n)}
    (hU : IsOpen U) {η : Point n → ℝ} (hη : Test Q η) (hOne : ∀ p ∈ U, η p = 1)
    {a a' : Point n → Mat n} {b c' : Point n → Yau.RIdx n → ℝ}
    (hA : ∀ p ∈ U, a' p = a p) (hC : ∀ p ∈ U, ∀ j, c' p j = energyDrift a b p j)
    (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ) {p : Point n} (hp : p ∈ U) :
    (∀ i, localizedWeakGradient η u G p i = G p i) ∧
      (∀ i, localizedWeakFlux η a G p i = energyFlux a' (localizedWeakGradient η u G) p i) ∧
      localizedWeakSource η u a b G p = ∑ j, c' p j*localizedWeakGradient η u G p j := by
  obtain ⟨_hw,hH,hP,hR⟩ := cutoff_fields_eq_on_open_plateau hU hη hOne a b u G hp
  refine ⟨hH,?_,?_⟩
  · intro i
    rw [show localizedWeakFlux η a G p i = energyFlux a G p i from hP i]
    simp only [energyFlux,hA p hp,show ∀ j, localizedWeakGradient η u G p j = G p j from hH]
  · rw [show localizedWeakSource η u a b G p = ∑ j, energyDrift a b p j*G p j from hR]
    simp only [hC p hp,show ∀ j, localizedWeakGradient η u G p j = G p j from hH]

end Yau.LeafProofs.L16Aux
