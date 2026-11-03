import Yau.Blueprint.Nodes

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E]

/-- The genuine compact-source infimum, on the Euclidean space used later
for the shared-base construction. -/
def compactInfConvolution (K : Set E) (v : E → ℝ) (κ : ℝ) (q : E) : ℝ :=
  sInf {r : ℝ | ∃ a ∈ K, r = v a+‖q-a‖^2/(2*κ)}

theorem compactInfConvolution_eq_of_min
    (K : Set E) (v : E → ℝ) (κ : ℝ) (q a : E) (ha : a ∈ K)
    (hmin : ∀ b ∈ K, v a+‖q-a‖^2/(2*κ) ≤ v b+‖q-b‖^2/(2*κ)) :
    compactInfConvolution K v κ q = v a+‖q-a‖^2/(2*κ) := by
  let S : Set ℝ := {r | ∃ b ∈ K, r = v b+‖q-b‖^2/(2*κ)}
  have hMem : v a+‖q-a‖^2/(2*κ) ∈ S := ⟨a,ha,rfl⟩
  have hNE : S.Nonempty := ⟨_,hMem⟩
  have hLower : ∀ r ∈ S, v a+‖q-a‖^2/(2*κ) ≤ r := by
    rintro r ⟨b,hb,rfl⟩
    exact hmin b hb
  have hBdd : BddBelow S := ⟨_,hLower⟩
  exact le_antisymm (csInf_le hBdd hMem) (le_csInf hNE hLower)

/-- Actual compactness and lower semicontinuity construct the minimizing
source; no minimizer premise is propagated to the E02 producer. -/
theorem compactInfConvolution_attained
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (κ : ℝ) (q : E) :
    ∃ a ∈ K, compactInfConvolution K v κ q = v a+‖q-a‖^2/(2*κ) ∧
      ∀ b ∈ K, v a+‖q-a‖^2/(2*κ) ≤ v b+‖q-b‖^2/(2*κ) := by
  have hpen : Continuous (fun a : E => ‖q-a‖^2/(2*κ)) := by fun_prop
  obtain ⟨a,ha,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK
    (hv.add hpen.continuousOn.lowerSemicontinuousOn)
  exact ⟨a,ha,compactInfConvolution_eq_of_min K v κ q a ha (fun b hb => hmin hb),
    fun b hb => hmin hb⟩

theorem compactInfConvolution_nonneg
    (K : Set E) (v : E → ℝ) (hne : K.Nonempty)
    (hv0 : ∀ a ∈ K, 0 ≤ v a) {κ : ℝ} (hκ : 0 < κ) (q : E) :
    0 ≤ compactInfConvolution K v κ q := by
  apply le_csInf
  · obtain ⟨a,ha⟩ := hne
    exact ⟨v a+‖q-a‖^2/(2*κ),a,ha,rfl⟩
  · rintro r ⟨a,ha,rfl⟩
    exact add_nonneg (hv0 a ha) (div_nonneg (sq_nonneg _) (by positivity))

theorem compactInfConvolution_le
    (K : Set E) (v : E → ℝ) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    {κ : ℝ} (hκ : 0 < κ) (q : E) (hq : q ∈ K) :
    compactInfConvolution K v κ q ≤ v q := by
  have hBdd : BddBelow {r : ℝ | ∃ a ∈ K, r = v a+‖q-a‖^2/(2*κ)} := by
    refine ⟨0,?_⟩
    rintro r ⟨a,ha,rfl⟩
    exact add_nonneg (hv0 a ha) (div_nonneg (sq_nonneg _) (by positivity))
  apply csInf_le hBdd
  exact ⟨q,hq,by simp⟩

theorem compactInfConvolution_le_cost
    (K : Set E) (v : E → ℝ) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    {κ : ℝ} (hκ : 0 < κ) (q a : E) (ha : a ∈ K) :
    compactInfConvolution K v κ q ≤ v a+‖q-a‖^2/(2*κ) := by
  have hBdd : BddBelow {r : ℝ | ∃ b ∈ K, r = v b+‖q-b‖^2/(2*κ)} := by
    refine ⟨0,?_⟩
    rintro r ⟨b,hb,rfl⟩
    exact add_nonneg (hv0 b hb) (div_nonneg (sq_nonneg _) (by positivity))
  exact csInf_le hBdd ⟨a,ha,rfl⟩

/-- The displacement estimate is obtained from the same actual attained
cost, before any limit of sources or jets is considered. -/
theorem compactInfConvolution_source_displacement
    (K : Set E) (v : E → ℝ) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (q a : E) (hq : q ∈ K)
    (ha : a ∈ K) (hqM : v q ≤ M)
    (haMin : compactInfConvolution K v κ q = v a+‖q-a‖^2/(2*κ)) :
    ‖q-a‖^2 ≤ 2*κ*M ∧ ‖q-a‖ ≤ Real.sqrt (2*κ*M) := by
  have hCost : v a+‖q-a‖^2/(2*κ) ≤ M := by
    rw [←haMin]
    exact (compactInfConvolution_le K v hv0 hκ q hq).trans hqM
  have hVa : 0 ≤ v a := hv0 a ha
  have hDiv : ‖q-a‖^2/(2*κ) ≤ M := by linarith
  have hSq : ‖q-a‖^2 ≤ 2*κ*M := by
    have := (div_le_iff₀ (show 0 < 2*κ by positivity)).mp hDiv
    nlinarith
  refine ⟨hSq,?_⟩
  have hArg : 0 ≤ 2*κ*M := by positivity
  have hSqrt := Real.sq_sqrt hArg
  have hSqrt0 := Real.sqrt_nonneg (2*κ*M)
  have hNorm := norm_nonneg (q-a)
  nlinarith

end Yau.NodeProofs.E02Aux
