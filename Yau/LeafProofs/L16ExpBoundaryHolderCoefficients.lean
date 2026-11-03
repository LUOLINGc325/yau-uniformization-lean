import Yau.LeafProofs.L16ExpBoundary
import Yau.LeafProofs.L16DeGiorgiTruncation

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryHolderAux

open Yau.Parabolic Yau.ParabolicCandidates L16Aux

def expDGMatrix {n : ℕ} (a : Point n → Mat n) (q : Point n → ℝ) (z : Point n) : Mat n :=
  (q z)⁻¹ • a z

def expDGDrift {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (q : Point n → ℝ) (z : Point n) (i : Yau.RIdx n) : ℝ := energyDrift a b z i/q z

def expDGForcing {n : ℕ} (R q : Point n → ℝ) (z : Point n) : ℝ := (q z-1)*R z

theorem timeD_halfOpen_eq_deriv {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {z : Point n} (hz : z ∈ O ×ˢ Ioo 0 T) (q : Point n → ℝ) :
    timeD (O ×ˢ Ioc 0 T) q z = deriv (fun t => q (z.1,t)) z.2 := by
  have hf : {t | (z.1,t) ∈ O ×ˢ Ioc 0 T} = Ioc 0 T := by
    ext t
    simp [hz.1]
  simp only [timeD,hf]
  exact derivWithin_of_mem_nhds (Ioc_mem_nhds hz.2.1 hz.2.2)

/-- The original nonlinear divergence equation is exactly the classical
divergence equation with the value-dependent principal and drift fields. -/
theorem expDivergence_classical {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {R q : Point n → ℝ}
    (heq : ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q) :
    ClassicalDivEq (O ×ˢ Ioo 0 T) (expDGMatrix a q) (expDGDrift a b q) (expDGForcing R q) q := by
  intro z hz
  have h := heq z ⟨hz.1,hz.2.1,hz.2.2.le⟩
  rw [timeD_halfOpen_eq_deriv hz] at h
  simpa only [expDGMatrix,expDGDrift,expDGForcing,energyDrift,dgGradient,
    Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

theorem expDivergence_classical_fields {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {T m : ℝ} (hm : 0 < m)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {R q : Point n → ℝ}
    (hab : SmoothCoefficients (cylinder (closure O) 0 T) a b)
    (hR : ContDiffOn ℝ ∞ R (cylinder (closure O) 0 T))
    (hq : ContDiffOn ℝ ∞ q (O ×ˢ Ioc 0 T))
    (hbound : ∀ z ∈ cylinder (closure O) 0 T, m ≤ q z) :
    DGClassicalFields (O ×ˢ Ioo 0 T) (expDGMatrix a q) (expDGDrift a b q) (expDGForcing R q) q := by
  have hUK : O ×ˢ Ioo 0 T ⊆ cylinder (closure O) 0 T := by
    intro z hz
    exact ⟨subset_closure hz.1,Ioo_subset_Icc_self hz.2⟩
  have hUI : O ×ˢ Ioo 0 T ⊆ O ×ˢ Ioc 0 T := fun z hz => ⟨hz.1,hz.2.1,hz.2.2.le⟩
  have hqU := hq.mono hUI
  have hne : ∀ z ∈ O ×ˢ Ioo 0 T, q z ≠ 0 := fun z hz => (hm.trans_le (hbound z (hUK hz))).ne'
  have hSmooth : SmoothCoefficients (O ×ˢ Ioo 0 T) a b :=
    ⟨hab.1.mono hUK,fun i => (hab.2 i).mono hUK⟩
  refine ⟨?_,?_,?_,hqU⟩
  · intro i j
    have h := ((matrixEntryCLM i j).contDiff.comp_contDiffOn hSmooth.1).div hqU hne
    apply h.congr
    intro z hz
    change (q z)⁻¹*a z i j = a z i j/q z
    ring
  · intro i
    exact (energyDrift_smooth (hO.prod isOpen_Ioo) hSmooth i).div hqU hne
  · exact (hqU.sub contDiffOn_const).mul (hR.mono hUK)

/-- The ellipticity constants are fixed before the solution is introduced. -/
theorem expDivergence_ellipticity_constants {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {lam upper m B : ℝ} (he : Elliptic Q a lam upper)
    (hm : 0 < m) (hmB : m ≤ B) : 0 < lam/B ∧ lam/B ≤ upper/m := by
  have hB : 0 < B := hm.trans_le hmB
  have hu : 0 < upper := he.1.trans_le he.2.1
  refine ⟨div_pos he.1 hB,(div_le_div_iff₀ hB hm).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_right he.2.1 hm.le).trans
    (mul_le_mul_of_nonneg_left hmB hu.le)

/-- The drift and forcing budgets depend only on the fixed compact data and
the value interval. No derivative of the candidate solution is bounded. -/
theorem expDivergence_uniform_budgets {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O)
    {T lam upper m B : ℝ} (hT : 0 < T) (hm : 0 < m) (hmB : m ≤ B)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (cylinder (closure O) 0 T) a b)
    (hR : ContDiffOn ℝ ∞ R (cylinder (closure O) 0 T))
    (he : Elliptic (cylinder (closure O) 0 T) a lam upper) :
    ∃ D F : ℝ, 0 < D ∧ 0 < F ∧
      ∀ q : Point n → ℝ, (∀ z ∈ cylinder (closure O) 0 T, m ≤ q z ∧ q z ≤ B) →
        DGUniformBounds (O ×ˢ Ioo 0 T) (expDGMatrix a q) (expDGDrift a b q)
          (expDGForcing R q) (lam/B) (upper/m) D F := by
  classical
  obtain ⟨A₀,D₀,hA₀,hD₀,hA,hDrift⟩ := smoothDomain_compact_coefficient_bounds hO hT hab
  obtain ⟨C,hC⟩ := (hO.2.2.1.prod isCompact_Icc).exists_bound_of_continuousOn hR.continuousOn
  let R₀ : ℝ := 1+|C|
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hB : 0 < B := hm.trans_le hmB
  refine ⟨D₀/m,(B+1)*R₀,by positivity,by positivity,?_⟩
  intro q hbound
  have hUK : O ×ˢ Ioo 0 T ⊆ cylinder (closure O) 0 T := by
    intro z hz
    exact ⟨subset_closure hz.1,Ioo_subset_Icc_self hz.2⟩
  have hEll := elliptic_div_of_bounds he hm hmB hbound
  refine ⟨⟨hEll.1,hEll.2.1,fun z hz => hEll.2.2 z (hUK hz)⟩,?_,?_⟩
  · intro z hz
    have hqpos : 0 < q z := hm.trans_le (hbound z (hUK hz)).1
    have hqSq : m^2 ≤ (q z)^2 := pow_le_pow_left₀ hm.le (hbound z (hUK hz)).1 2
    have hsum : (∑ i, (energyDrift a b z i)^2) ≤ D₀^2 := by
      simpa only [sq_abs] using hDrift z hz
    have hboundDiv : (∑ i, (energyDrift a b z i)^2)/(q z)^2 ≤ D₀^2/m^2 :=
      (div_le_div_of_nonneg_right hsum (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left (sq_nonneg D₀) (sq_pos_of_pos hm) hqSq)
    simpa only [dgGradientSq,expDGDrift,div_pow,Finset.sum_div] using hboundDiv
  · intro z hz
    have hzQ := hUK hz
    have hqpos : 0 < q z := hm.trans_le (hbound z hzQ).1
    have hqabs : |q z-1| ≤ B+1 := by
      have h := abs_sub (q z) (1 : ℝ)
      rw [abs_of_pos hqpos,abs_one] at h
      exact h.trans (add_le_add (hbound z hzQ).2 le_rfl)
    have hRF : |R z| ≤ R₀ := by
      have hh : |R z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hzQ
      exact hh.trans (by dsimp [R₀]; linarith [le_abs_self C])
    exact (abs_mul _ _).trans_le (mul_le_mul hqabs hRF (abs_nonneg _) (by positivity))

end Yau.LeafProofs.L16ExpBoundaryHolderAux
