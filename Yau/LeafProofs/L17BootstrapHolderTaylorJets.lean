import Yau.LeafProofs.L17BootstrapHolderTaylorGraph
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Canonical parameter jets, their actual curried derivative, and Holder towers. -/

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L17BootstrapHolderTaylorAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux

variable {Param X F : Type*}
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev ParamJet (Param : Type*) [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    (k : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin k => Param) F

/-- Nondependent aliases keep nested operator-space instance search stable. -/
instance paramJetNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (ParamJet Param k F) :=
  inferInstanceAs (NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin k => Param) F))

instance paramJetNormedSpace (k : ℕ) : NormedSpace ℝ (ParamJet Param k F) :=
  inferInstanceAs (NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Param) F))

instance paramJetOneNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (Param →L[ℝ] ParamJet Param k F) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance paramJetOneNormedSpace (k : ℕ) : NormedSpace ℝ (Param →L[ℝ] ParamJet Param k F) :=
  ContinuousLinearMap.toNormedSpace

def parameterJet (k : ℕ) (c : Param → X → F) (p : Param × X) : ParamJet Param k F :=
  iteratedFDeriv ℝ k (fun a => c a p.2) p.1

/-- Joint smoothness of actual partial parameter derivatives, proved from ordinary calculus. -/
theorem contDiffAt_parameterJet {c : Param → X → F} {p : Param × X}
    (hc : ContDiffAt ℝ ∞ (fun b : Param × X => c b.1 b.2) p) (k : ℕ) :
    ContDiffAt ℝ ∞ (parameterJet k c) p := by
  induction k with
  | zero =>
    exact hc.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ Param F).symm : F →L[ℝ] ParamJet Param 0 F)
  | succ k ih =>
    have hcomp : ContDiffAt ℝ ∞
        (fun b : (Param × X) × Param => parameterJet k c (b.2,b.1.2)) (p,p.1) :=
      ih.comp (p,p.1) (contDiffAt_snd.prodMk (contDiffAt_fst.snd))
    have hd := ContDiffAt.fderiv (𝕜 := ℝ)
      (f := fun (b : Param × X) (a : Param) => parameterJet k c (a,b.2))
      (g := fun b : Param × X => b.1) hcomp contDiffAt_fst
      (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => Param) F).symm :
        (Param →L[ℝ] ParamJet Param k F) →L[ℝ] ParamJet Param (k+1) F)

def jetCurry (k : ℕ) : ParamJet Param (k+1) F →L[ℝ] Param →L[ℝ] ParamJet Param k F :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => Param) F).toContinuousLinearEquiv

theorem jetCurry_norm (k : ℕ) (v : ParamJet Param (k+1) F) : ‖(jetCurry (Param := Param) (F := F) k) v‖ = ‖v‖ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => Param) F).norm_map v

theorem jetCurry_norm_le (k : ℕ) : ‖jetCurry (Param := Param) (F := F) k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using (jetCurry_norm (Param := Param) (F := F) k v).le

theorem hasFDerivAt_parameterJet {c : Param → F} {a : Param}
    (hc : ContDiffAt ℝ ∞ c a) (k : ℕ) :
    HasFDerivAt (iteratedFDeriv ℝ k c) ((jetCurry (Param := Param) (F := F) k) (iteratedFDeriv ℝ (k+1) c a)) a := by
  apply (hc.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt.congr_fderiv
  rw [fderiv_iteratedFDeriv]
  rfl

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T beta : ℝ}

/-- The actual candidate derivative of a Holder-valued parameter jet. -/
def holderJetDerivativeCLM (k : ℕ) :
    LocalHolderSpace (ParamJet Param (k+1) F) P T beta →L[ℝ]
      Param →L[ℝ] LocalHolderSpace (ParamJet Param k F) P T beta :=
  holderUncurryCLM.comp (localMapCLM ((jetCurry (Param := Param) (F := F) k)))

theorem holderJetDerivativeCLM_value (k : ℕ)
    (v : LocalHolderSpace (ParamJet Param (k+1) F) P T beta)
    (h : Param) (q : LocalCylinder P T) :
    localFun _ ((holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) v h) q = (jetCurry (Param := Param) (F := F) k) (localFun _ v q) h := rfl

theorem holderJetDerivativeCLM_norm_le (k : ℕ) :
    ‖holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  change ‖holderApply (localMapCLM (jetCurry (Param := Param) (F := F) k) v) h‖ ≤ (1*‖v‖)*‖h‖
  apply (holderApply_norm_le _ h).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
  exact (localMapElement_norm_le (jetCurry (Param := Param) (F := F) k) v).trans
    (mul_le_mul_of_nonneg_right (jetCurry_norm_le (Param := Param) (F := F) k) (norm_nonneg v))

/-- Finite-order Holder Taylor estimate, requiring only three consecutive ordinary jets. -/
theorem holder_parameterJet_remainder_le
    {s : Set Param} (hs : Convex ℝ s)
    (u : (k : ℕ) → Param → LocalHolderSpace (ParamJet Param k F) P T beta)
    (k : ℕ)
    (hdu : ∀ j ∈ Icc k (k+1), ∀ a ∈ s, ∀ q,
      HasFDerivAt (fun b => localFun _ (u j b) q)
        ((jetCurry (Param := Param) (F := F) j) (localFun _ (u (j+1) a) q)) a)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a ∈ s, ‖u (k+2) a‖ ≤ C)
    {x y : Param} (hx : x ∈ s) (hy : y ∈ s) :
    ‖u k y-u k x-(holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) (u (k+1) x) (y-x)‖ ≤ C*‖y-x‖^2 := by
  let L := jetCurry (Param := Param) (F := F) k
  let L' := jetCurry (Param := Param) (F := F) (k+1)
  let B : ParamJet Param (k+2) F →L[ℝ] Param →L[ℝ] Param →L[ℝ] ParamJet Param k F :=
    (ContinuousLinearMap.compL ℝ Param (ParamJet Param (k+1) F)
      (Param →L[ℝ] ParamJet Param k F) L).comp L'
  apply holder_taylor_remainder_le hs (u k)
    (fun a => localMapCLM L (u (k+1) a))
    (fun a => localMapCLM B (u (k+2) a))
    (fun a ha q => hdu k ⟨le_rfl, Nat.le_succ k⟩ a ha q) ?_ hC ?_ hx hy
  · intro a ha q
    exact L.hasFDerivAt.comp a (hdu (k+1) ⟨Nat.le_succ k, le_rfl⟩ a ha q)
  · intro a ha
    have hB : ‖B‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      change ‖L.comp (L' v)‖ ≤ 1*‖v‖
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_right (jetCurry_norm_le (Param := Param) (F := F) k)
          (norm_nonneg _)).trans_eq (by
            dsimp only [L']
            rw [jetCurry_norm, one_mul]))
    exact (localMapElement_norm_le B (u (k+2) a)).trans
      ((mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans (by simpa only [one_mul] using hw a ha))

/-- Every finite coefficient derivative is the derivative of its actual Holder lift. -/
theorem holder_parameterJet_hasFDerivAt
    {s : Set Param} (hs : Convex ℝ s) (hsOpen : IsOpen s)
    (u : (k : ℕ) → Param → LocalHolderSpace (ParamJet Param k F) P T beta)
    (k : ℕ)
    (hdu : ∀ j ∈ Icc k (k+1), ∀ a ∈ s, ∀ q,
      HasFDerivAt (fun b => localFun _ (u j b) q)
        ((jetCurry (Param := Param) (F := F) j) (localFun _ (u (j+1) a) q)) a)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a ∈ s, ‖u (k+2) a‖ ≤ C)
    {x : Param} (hx : x ∈ s) :
    HasFDerivAt (u k) ((holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) (u (k+1) x)) x := by
  apply hasFDerivAt_of_quadratic_remainder
  filter_upwards [hsOpen.mem_nhds hx] with y hy
  exact holder_parameterJet_remainder_le hs u k hdu hC hw hx hy

/-- The finite successor induction is simultaneous in the coefficient-jet order. -/
theorem holder_parameterJet_contDiffOn
    {s : Set Param} (hs : Convex ℝ s) (hsOpen : IsOpen s)
    (u : (k : ℕ) → Param → LocalHolderSpace (ParamJet Param k F) P T beta)
    (hdu : ∀ k a, a ∈ s → ∀ q,
      HasFDerivAt (fun b => localFun _ (u k b) q)
        ((jetCurry (Param := Param) (F := F) k) (localFun _ (u (k+1) a) q)) a)
    (H : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k)
    (hbound : ∀ k a, a ∈ s → ‖u k a‖ ≤ H k) :
    ∀ k, ContDiffOn ℝ ∞ (u k) s := by
  have hd : ∀ k a, a ∈ s →
      HasFDerivAt (u k) ((holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) (u (k+1) a)) a := by
    intro k a ha
    exact holder_parameterJet_hasFDerivAt hs hsOpen u k
      (fun j _ b hb => hdu j b hb) (hH (k+2)) (hbound (k+2)) ha
  have hfinite : ∀ m : ℕ, ∀ k, ContDiffOn ℝ m (u k) s := by
    intro m
    induction m with
    | zero =>
      intro k
      apply contDiffOn_zero.mpr
      intro a ha
      exact (hd k a ha).continuousAt.continuousWithinAt
    | succ m ih =>
      intro k
      change ContDiffOn ℝ ((m : ℕ∞ω)+1) (u k) s
      apply (contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (m : ℕ∞ω) ≠ ∞)).mpr
      intro a ha
      refine ⟨s, ?_, ?_,
        fun b => (holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) (u (k+1) b), ?_, ?_⟩
      · rw [insert_eq_of_mem ha]
        exact self_mem_nhdsWithin
      · simp
      · intro b hb
        exact (hd k b hb).hasFDerivWithinAt
      · exact (ih (k+1)).continuousLinearMap_comp ((holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k))
  intro k
  exact contDiffOn_infty.mpr (fun m => hfinite m k)

end Yau.LeafProofs.L17BootstrapHolderTaylorAux
