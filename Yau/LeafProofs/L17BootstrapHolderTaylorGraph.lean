import Yau.LeafProofs.L17LocalHolderAlgebraBasic
import Yau.LeafProofs.L17LocalHolderBanachAlgebraBasic
import Yau.LeafProofs.L17BootstrapHolderTaylorCalculus
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Actual derivative operators and Taylor estimates in the weighted Holder graph. -/

noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L17BootstrapHolderTaylorAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T beta : ℝ}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def holderApply (u : LocalHolderSpace (E →L[ℝ] F) P T beta) (h : E) :
    LocalHolderSpace F P T beta :=
  localMapCLM (ContinuousLinearMap.apply ℝ F h) u

@[simp] theorem holderApply_value (u : LocalHolderSpace (E →L[ℝ] F) P T beta)
    (h : E) (q : LocalCylinder P T) :
    localFun F (holderApply u h) q = localFun (E →L[ℝ] F) u q h := rfl

theorem holderApply_norm_le (u : LocalHolderSpace (E →L[ℝ] F) P T beta) (h : E) :
    ‖holderApply u h‖ ≤ ‖u‖*‖h‖ := by
  apply (localNorm_le_iff F _ (by positivity)).mpr
  constructor
  · intro q
    exact ((localFun (E →L[ℝ] F) u q).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (localValue_norm_le _ u q) (norm_nonneg h))
  · intro i
    change ‖pairWeight P T beta i •
      (localFun (E →L[ℝ] F) u (localRight P T i) h-
        localFun (E →L[ℝ] F) u (localLeft P T i) h)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.smul_apply]
    exact (ContinuousLinearMap.le_opNorm _ h).trans
      (mul_le_mul_of_nonneg_right (localWeighted_difference_norm_le _ u i) (norm_nonneg h))

def holderUncurryLinear :
    LocalHolderSpace (E →L[ℝ] F) P T beta →ₗ[ℝ] E →ₗ[ℝ] LocalHolderSpace F P T beta where
  toFun u := {
    toFun := holderApply u
    map_add' := by
      intro h k
      apply localFun_injective F P T beta
      funext q
      exact (localFun (E →L[ℝ] F) u q).map_add h k
    map_smul' := by
      intro c h
      apply localFun_injective F P T beta
      funext q
      exact (localFun (E →L[ℝ] F) u q).map_smul c h }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro h
    apply localFun_injective F P T beta
    funext q
    rfl
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro h
    apply localFun_injective F P T beta
    funext q
    rfl

/-- Currying a local operator field yields a genuine bounded derivative operator. -/
def holderUncurryCLM :
    LocalHolderSpace (E →L[ℝ] F) P T beta →L[ℝ] E →L[ℝ] LocalHolderSpace F P T beta :=
  holderUncurryLinear.mkContinuous₂ 1 (fun u h => by
    change ‖holderApply u h‖ ≤ 1*‖u‖*‖h‖
    simpa only [one_mul] using holderApply_norm_le u h)

@[simp] theorem holderUncurryCLM_value (u : LocalHolderSpace (E →L[ℝ] F) P T beta)
    (h : E) (q : LocalCylinder P T) :
    localFun F (holderUncurryCLM u h) q = localFun (E →L[ℝ] F) u q h := rfl

theorem holderUncurryCLM_norm_le :
    ‖holderUncurryCLM (P := P) (T := T) (beta := beta) (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  change ‖holderApply u h‖ ≤ (1*‖u‖)*‖h‖
  simpa only [one_mul] using holderApply_norm_le u h

/-- The norm remainder controls both value and the literal weighted pair coordinate.
Its premises are ordinary finite-coordinate derivatives, not graph-valued derivatives. -/
theorem holder_taylor_remainder_le
    {s : Set E} (hs : Convex ℝ s)
    (u : E → LocalHolderSpace F P T beta)
    (v : E → LocalHolderSpace (E →L[ℝ] F) P T beta)
    (w : E → LocalHolderSpace (E →L[ℝ] E →L[ℝ] F) P T beta)
    (hdu : ∀ a ∈ s, ∀ q, HasFDerivAt (fun b => localFun F (u b) q)
      (localFun (E →L[ℝ] F) (v a) q) a)
    (hdv : ∀ a ∈ s, ∀ q, HasFDerivAt (fun b => localFun (E →L[ℝ] F) (v b) q)
      (localFun (E →L[ℝ] E →L[ℝ] F) (w a) q) a)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a ∈ s, ‖w a‖ ≤ C)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖u y-u x-holderUncurryCLM (v x) (y-x)‖ ≤ C*‖y-x‖^2 := by
  apply (localNorm_le_iff F _ (by positivity)).mpr
  constructor
  · intro q
    exact norm_taylor_remainder_le hs (fun a ha => hdu a ha q)
      (fun a ha => hdv a ha q) hC
      (fun a ha => (localValue_norm_le _ (w a) q).trans (hw a ha)) hx hy
  · intro i
    let r := localRight P T i
    let l := localLeft P T i
    let wt := pairWeight P T beta i
    have hd : ∀ a ∈ s, HasFDerivAt
        (fun b => wt • (localFun F (u b) r-localFun F (u b) l))
        (wt • (localFun (E →L[ℝ] F) (v a) r-localFun (E →L[ℝ] F) (v a) l)) a := by
      intro a ha
      exact ((hdu a ha r).sub (hdu a ha l)).const_smul wt
    have hd' : ∀ a ∈ s, HasFDerivAt
        (fun b => wt • (localFun (E →L[ℝ] F) (v b) r-localFun (E →L[ℝ] F) (v b) l))
        (wt • (localFun (E →L[ℝ] E →L[ℝ] F) (w a) r-
          localFun (E →L[ℝ] E →L[ℝ] F) (w a) l)) a := by
      intro a ha
      exact ((hdv a ha r).sub (hdv a ha l)).const_smul wt
    have h := norm_taylor_remainder_le hs hd hd' hC
      (fun a ha => (localWeighted_difference_norm_le _ (w a) i).trans (hw a ha)) hx hy
    convert h using 1
    congr 1
    change wt • ((localFun F (u y) r-localFun F (u x) r-localFun (E →L[ℝ] F) (v x) r (y-x))-
        (localFun F (u y) l-localFun F (u x) l-localFun (E →L[ℝ] F) (v x) l (y-x))) = _
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_sub]
    abel

theorem holder_hasFDerivAt
    {s : Set E} (hs : Convex ℝ s) (hsOpen : IsOpen s)
    (u : E → LocalHolderSpace F P T beta)
    (v : E → LocalHolderSpace (E →L[ℝ] F) P T beta)
    (w : E → LocalHolderSpace (E →L[ℝ] E →L[ℝ] F) P T beta)
    (hdu : ∀ a ∈ s, ∀ q, HasFDerivAt (fun b => localFun F (u b) q)
      (localFun (E →L[ℝ] F) (v a) q) a)
    (hdv : ∀ a ∈ s, ∀ q, HasFDerivAt (fun b => localFun (E →L[ℝ] F) (v b) q)
      (localFun (E →L[ℝ] E →L[ℝ] F) (w a) q) a)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a ∈ s, ‖w a‖ ≤ C)
    {x : E} (hx : x ∈ s) :
    HasFDerivAt u (holderUncurryCLM (v x)) x := by
  apply hasFDerivAt_of_quadratic_remainder
  filter_upwards [hsOpen.mem_nhds hx] with y hy
  exact holder_taylor_remainder_le hs u v w hdu hdv hC hw hx hy

/-- The Banach-algebra renorming is an actual continuous linear lift. -/
def localToBanachCLM : LocalHolderSpace F P T beta →L[ℝ]
    L17LocalHolderBanachAlgebraAux.LocalHolderBanach F P T beta :=
  (L17LocalHolderBanachAlgebraAux.valueContinuousLinearEquiv F P T beta).symm

theorem localToBanachCLM_norm (u : LocalHolderSpace F P T beta) :
    ‖localToBanachCLM u‖ = 2*‖u‖ :=
  L17LocalHolderBanachAlgebraAux.norm_ofLocal F P T beta u

/-- Passing to the renormed Banach space keeps the required factor two. -/
theorem banach_taylor_remainder_le
    {u : E → LocalHolderSpace F P T beta} {A : E →L[ℝ] LocalHolderSpace F P T beta}
    {x y : E} {C : ℝ}
    (h : ‖u y-u x-A (y-x)‖ ≤ C*‖y-x‖^2) :
    ‖localToBanachCLM (u y)-localToBanachCLM (u x)-
      (localToBanachCLM.comp A) (y-x)‖ ≤ 2*C*‖y-x‖^2 := by
  change ‖localToBanachCLM (u y)-localToBanachCLM (u x)-localToBanachCLM (A (y-x))‖ ≤ _
  rw [← map_sub, ← map_sub, localToBanachCLM_norm]
  nlinarith

end Yau.LeafProofs.L17BootstrapHolderTaylorAux
