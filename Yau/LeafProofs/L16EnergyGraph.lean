import Yau.Blueprint.ParabolicSpaces
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Sequences

/-! The closed spatial `L²` graph of the actual compactly supported smooth functions.
The ambient norm is the Hilbert square-sum norm, including the value coordinate. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

variable {n : ℕ}

/-- Value and real coordinate derivative classes, with their genuine Hilbert norm. -/
abbrev EnergyGraphAmbient (O : Set (Space n)) :=
  PiLp 2 (fun _ : Option (Yau.RIdx n) => Lp ℝ 2 (volume.restrict O))

/-- Actual spatial smooth functions compactly supported in `O`. -/
def energySpatialTests (O : Set (Space n)) : Submodule ℝ (Space n → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro φ ψ hφ hψ
    exact ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
      (tsupport_add φ ψ).trans (Set.union_subset hφ.2.2 hψ.2.2)⟩
  smul_mem' := by
    intro c φ hφ
    exact ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left (f := fun _ => c),
      (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.2.2⟩

theorem energySpatialTest_memLp {O : Set (Space n)} (φ : energySpatialTests O) :
    MemLp φ.1 2 (volume.restrict O) :=
  (φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1).restrict O

theorem energySpatialTest_d_memLp {O : Set (Space n)} (φ : energySpatialTests O)
    (i : Yau.RIdx n) : MemLp (fun x => d φ.1 x i) 2 (volume.restrict O) := by
  have hc : Continuous (fun x => d φ.1 x i) :=
    (φ.2.1.contDiff_fderiv_apply (m := 0) (by simp)).continuous.comp
      (continuous_id.prodMk continuous_const)
  exact (hc.memLp_of_hasCompactSupport (φ.2.2.1.fderiv_apply ℝ (Yau.realVec i))).restrict O

/-- The canonical lift of an actual value and actual derivative representatives. -/
def energyGraphLift {O : Set (Space n)} {u : Space n → ℝ}
    {G : Space n → Yau.RIdx n → ℝ} (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) : EnergyGraphAmbient O :=
  WithLp.toLp 2 (fun k => match k with
    | none => hu.toLp u
    | some i => (hG i).toLp (fun x => G x i))

@[simp] theorem energyGraphLift_none {O : Set (Space n)} {u : Space n → ℝ}
    {G : Space n → Yau.RIdx n → ℝ} (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) :
    energyGraphLift hu hG none = hu.toLp u := rfl

@[simp] theorem energyGraphLift_some {O : Set (Space n)} {u : Space n → ℝ}
    {G : Space n → Yau.RIdx n → ℝ} (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) (i : Yau.RIdx n) :
    energyGraphLift hu hG (some i) = (hG i).toLp (fun x => G x i) := rfl

/-- The actual smooth value/derivative graph map. -/
def energySpatialGraph (O : Set (Space n)) : energySpatialTests O →ₗ[ℝ] EnergyGraphAmbient O where
  toFun φ := energyGraphLift (energySpatialTest_memLp φ) (energySpatialTest_d_memLp φ)
  map_add' φ ψ := by
    apply PiLp.ext
    intro k
    cases k with
    | none => exact MemLp.toLp_add (energySpatialTest_memLp φ) (energySpatialTest_memLp ψ)
    | some i =>
      change (energySpatialTest_d_memLp (φ + ψ) i).toLp _ =
        (energySpatialTest_d_memLp φ i).toLp _ + (energySpatialTest_d_memLp ψ i).toLp _
      have hd : (fun x => d (φ + ψ).1 x i) =
          (fun x => d φ.1 x i) + (fun x => d ψ.1 x i) := by
        funext x
        exact congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i))
          (fderiv_add (φ.2.1.differentiable (by simp) x)
            (ψ.2.1.differentiable (by simp) x))
      simpa only [hd] using MemLp.toLp_add (energySpatialTest_d_memLp φ i)
        (energySpatialTest_d_memLp ψ i)
  map_smul' c φ := by
    apply PiLp.ext
    intro k
    cases k with
    | none => exact MemLp.toLp_const_smul c (energySpatialTest_memLp φ)
    | some i =>
      change (energySpatialTest_d_memLp (c • φ) i).toLp _ =
        c • (energySpatialTest_d_memLp φ i).toLp _
      have hd : (fun x => d (c • φ).1 x i) = c • (fun x => d φ.1 x i) := by
        funext x
        exact congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i))
          (fderiv_const_smul (φ.2.1.differentiable (by simp) x) c)
      simpa only [hd] using MemLp.toLp_const_smul c (energySpatialTest_d_memLp φ i)

/-- The smooth graph is a linear subspace of the Hilbert ambient. -/
def smoothGraphCore (O : Set (Space n)) : Submodule ℝ (EnergyGraphAmbient O) :=
  (energySpatialGraph O).range

/-- The actual closed graph space; its Hilbert and completeness instances are inherited. -/
abbrev EnergyGraphSpace (O : Set (Space n)) := (smoothGraphCore O).topologicalClosure

instance energyGraphSpace_complete (O : Set (Space n)) : CompleteSpace (EnergyGraphSpace O) :=
  inferInstance

instance energyGraphSpace_innerProduct (O : Set (Space n)) :
    InnerProductSpace ℝ (EnergyGraphSpace O) := inferInstance

/-- The scalar `L²` square norm, with the original representatives. -/
theorem energy_toLp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, |f x| ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs]

/-- The square of the Hilbert graph distance is exactly the frozen `H10` error. -/
theorem energySpatialGraph_dist_sq {O : Set (Space n)} (φ : energySpatialTests O)
    {u : Space n → ℝ} {G : Space n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) :
    ‖energySpatialGraph O φ - energyGraphLift hu hG‖ ^ 2 =
      (∫ x in O, |φ.1 x - u x| ^ 2) +
        ∑ i, ∫ x in O, |d φ.1 x i - G x i| ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]
  congr 1
  · change ‖(energySpatialTest_memLp φ).toLp φ.1 - hu.toLp u‖ ^ 2 = _
    rw [← MemLp.toLp_sub]
    exact energy_toLp_norm_sq ((energySpatialTest_memLp φ).sub hu)
  · apply Finset.sum_congr rfl
    intro i _
    change ‖(energySpatialTest_d_memLp φ i).toLp _ - (hG i).toLp _‖ ^ 2 = _
    rw [← MemLp.toLp_sub]
    exact energy_toLp_norm_sq ((energySpatialTest_d_memLp φ i).sub (hG i))

/-- Convergence in the Hilbert graph is exactly the frozen scalar error convergence. -/
theorem energySpatialGraph_tendsto_iff {O : Set (Space n)}
    (φ : ℕ → energySpatialTests O) {u : Space n → ℝ}
    {G : Space n → Yau.RIdx n → ℝ} (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) :
    Tendsto (fun k => (∫ x in O, |(φ k).1 x - u x| ^ 2) +
      ∑ i, ∫ x in O, |d (φ k).1 x i - G x i| ^ 2) atTop (𝓝 0) ↔
      Tendsto (fun k => energySpatialGraph O (φ k)) atTop (𝓝 (energyGraphLift hu hG)) := by
  have heq (k : ℕ) := energySpatialGraph_dist_sq (φ k) hu hG
  simp_rw [← heq]
  constructor
  · intro h
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp h
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  · intro h
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp h
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hnorm.pow 2

/-- Exact identification of frozen `H10` with the closure of the actual smooth graph.
No openness, weak-gradient uniqueness, or density assumption is used. -/
theorem h10_iff_energyGraphLift_mem_closure {O : Set (Space n)}
    {u : Space n → ℝ} {G : Space n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) :
    H10 O u G ↔ energyGraphLift hu hG ∈ (smoothGraphCore O).topologicalClosure := by
  constructor
  · rintro ⟨_, _, v, hv, hlim⟩
    let φ : ℕ → energySpatialTests O := fun k => ⟨v k, hv k⟩
    have hseq : Tendsto (fun k => energySpatialGraph O (φ k)) atTop
        (𝓝 (energyGraphLift hu hG)) :=
      (energySpatialGraph_tendsto_iff φ hu hG).mp hlim
    exact (smoothGraphCore O).isClosed_topologicalClosure.mem_of_tendsto hseq
      (Eventually.of_forall fun k =>
        (smoothGraphCore O).le_topologicalClosure ⟨φ k, rfl⟩)
  · intro h
    change energyGraphLift hu hG ∈ closure (smoothGraphCore O : Set (EnergyGraphAmbient O)) at h
    obtain ⟨z, hz, hseq⟩ := mem_closure_iff_seq_limit.mp h
    choose φ hφ using hz
    refine ⟨hu, hG, fun k => (φ k).1, fun k => (φ k).2, ?_⟩
    apply (energySpatialGraph_tendsto_iff φ hu hG).mpr
    simpa only [hφ] using hseq

/-- A genuine smooth sequence approximates every vector of the closed Hilbert graph. -/
theorem energyGraphSpace_smooth_approx {O : Set (Space n)} (v : EnergyGraphSpace O) :
    ∃ φ : ℕ → energySpatialTests O,
      Tendsto (fun k => energySpatialGraph O (φ k)) atTop (𝓝 v.1) := by
  have h : v.1 ∈ closure (smoothGraphCore O : Set (EnergyGraphAmbient O)) := v.2
  obtain ⟨z, hz, hseq⟩ := mem_closure_iff_seq_limit.mp h
  choose φ hφ using hz
  exact ⟨φ, by simpa only [hφ] using hseq⟩

/-- The smooth graph map with codomain restricted to its actual closure. -/
def energySpatialGraphInSpace (O : Set (Space n)) :
    energySpatialTests O →ₗ[ℝ] EnergyGraphSpace O :=
  (energySpatialGraph O).codRestrict _ (fun φ =>
    (smoothGraphCore O).le_topologicalClosure ⟨φ, rfl⟩)

/-- Smooth graph vectors are dense in the closed graph space itself. -/
theorem energySpatialGraphInSpace_denseRange (O : Set (Space n)) :
    DenseRange (energySpatialGraphInSpace O) := by
  intro v
  obtain ⟨φ, hφ⟩ := energyGraphSpace_smooth_approx v
  apply mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun k => energySpatialGraphInSpace O (φ k))
  · exact tendsto_subtype_rng.mpr hφ
  · exact Eventually.of_forall fun k => ⟨φ k, rfl⟩

/-- Every value/derivative coordinate is a bounded linear projection. -/
def energyCoordinateProjection (O : Set (Space n)) (k : Option (Yau.RIdx n)) :
    EnergyGraphSpace O →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  (PiLp.proj 2 (fun _ : Option (Yau.RIdx n) => Lp ℝ 2 (volume.restrict O)) k).comp
    (smoothGraphCore O).topologicalClosure.subtypeL

/-- The value projection from the closed Hilbert graph to `L²`. -/
def energyValueProjection (O : Set (Space n)) :
    EnergyGraphSpace O →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  energyCoordinateProjection O none

/-- The actual real coordinate gradient projection from the closed Hilbert graph. -/
def energyGradientProjection (O : Set (Space n)) (i : Yau.RIdx n) :
    EnergyGraphSpace O →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  energyCoordinateProjection O (some i)

theorem energyCoordinateProjection_norm_le (O : Set (Space n)) (k : Option (Yau.RIdx n)) :
    ‖energyCoordinateProjection O k‖ ≤ 1 := by
  apply (energyCoordinateProjection O k).opNorm_le_bound zero_le_one
  intro v
  change ‖v.1 k‖ ≤ 1 * ‖v.1‖
  simpa only [one_mul] using PiLp.norm_apply_le v.1 k

theorem energyValueProjection_norm_le (O : Set (Space n)) : ‖energyValueProjection O‖ ≤ 1 :=
  energyCoordinateProjection_norm_le O none

theorem energyGradientProjection_norm_le (O : Set (Space n)) (i : Yau.RIdx n) :
    ‖energyGradientProjection O i‖ ≤ 1 := energyCoordinateProjection_norm_le O (some i)

@[simp] theorem energyValueProjection_lift {O : Set (Space n)}
    {u : Space n → ℝ} {G : Space n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O))
    (h : energyGraphLift hu hG ∈ (smoothGraphCore O).topologicalClosure) :
    energyValueProjection O ⟨energyGraphLift hu hG, h⟩ = hu.toLp u := rfl

@[simp] theorem energyGradientProjection_lift {O : Set (Space n)}
    {u : Space n → ℝ} {G : Space n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O))
    (h : energyGraphLift hu hG ∈ (smoothGraphCore O).topologicalClosure) (i : Yau.RIdx n) :
    energyGradientProjection O i ⟨energyGraphLift hu hG, h⟩ =
      (hG i).toLp (fun x => G x i) := rfl

theorem energyValueProjection_lift_ae {O : Set (Space n)}
    {u : Space n → ℝ} {G : Space n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O))
    (h : energyGraphLift hu hG ∈ (smoothGraphCore O).topologicalClosure) :
    (energyValueProjection O ⟨energyGraphLift hu hG, h⟩ : Space n → ℝ) =ᵐ[volume.restrict O] u :=
  hu.coeFn_toLp

theorem energyGradientProjection_lift_ae {O : Set (Space n)}
    {u : Space n → ℝ} {G : Space n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict O))
    (h : energyGraphLift hu hG ∈ (smoothGraphCore O).topologicalClosure) (i : Yau.RIdx n) :
    (energyGradientProjection O i ⟨energyGraphLift hu hG, h⟩ : Space n → ℝ) =ᵐ[volume.restrict O]
      (fun x => G x i) := (hG i).coeFn_toLp

/-- The actual graph vector of a frozen `H10` value and gradient. -/
def energyOfH10 {O : Set (Space n)} {u : Space n → ℝ}
    {G : Space n → Yau.RIdx n → ℝ} (h : H10 O u G) : EnergyGraphSpace O :=
  ⟨energyGraphLift h.1 h.2.1,
    (h10_iff_energyGraphLift_mem_closure h.1 h.2.1).mp h⟩

/-- Frozen `H10` is closed under strong convergence of the value/gradient graph. -/
theorem h10_of_tendsto_energyGraphLift {O : Set (Space n)}
    {u : ℕ → Space n → ℝ} {G : ℕ → Space n → Yau.RIdx n → ℝ}
    {v : Space n → ℝ} {F : Space n → Yau.RIdx n → ℝ}
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict O))
    (hG : ∀ k i, MemLp (fun x => G k x i) 2 (volume.restrict O))
    (hv : MemLp v 2 (volume.restrict O))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict O))
    (h : ∀ k, H10 O (u k) (G k))
    (hlim : Tendsto (fun k => energyGraphLift (hu k) (hG k)) atTop
      (𝓝 (energyGraphLift hv hF))) : H10 O v F := by
  apply (h10_iff_energyGraphLift_mem_closure hv hF).mpr
  exact (smoothGraphCore O).isClosed_topologicalClosure.mem_of_tendsto hlim
    (Eventually.of_forall fun k => (h10_iff_energyGraphLift_mem_closure (hu k) (hG k)).mp (h k))

end Yau.LeafProofs.L16Aux
