import Yau.LeafProofs.L16HolderOnlyInverse
import Yau.LeafProofs.L16ZeroInitialSchauderJets
import Yau.LeafProofs.L16CutoffFullHolderExtension

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance interiorDirichlet_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance interiorDirichlet_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance interiorDirichlet_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance interiorDirichlet_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

def interiorDirichletCoefficientCutoff {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) : Space n → ℝ :=
  innerPatchBump (2*r) (by positivity) z

def interiorDirichletPrincipalExtension {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r)
    (a : Point n → Mat n) (p : Point n) : Mat n :=
  interiorDirichletCoefficientCutoff z r hr p.1 • a p+
    (1-interiorDirichletCoefficientCutoff z r hr p.1) • (1 : Mat n)

def interiorDirichletDriftExtension {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r)
    (b : Point n → Yau.RIdx n → ℝ) (p : Point n) (i : Yau.RIdx n) : ℝ :=
  interiorDirichletCoefficientCutoff z r hr p.1*b p i

def interiorDirichletPatch {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r)
    (v : Point n → ℝ) : Point n → ℝ := fun p => outerPatchBump r hr z p.1*v p

/-- The actual cutoff coefficients extend to the whole slab without any
bound on the original coefficients outside the actual closed domain. -/
theorem interiorDirichlet_coefficient_extension {n : ℕ} {O : Set (Space n)}
    {α M lam upper : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    (z : Space n) {r : ℝ} (hr : 0 < r) (hInside : Metric.closedBall z (4*r) ⊆ O) :
    ∃ J : ℝ, 0 < J ∧ ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      Elliptic (cylinder (closure O) 0 T) a lam upper →
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      Elliptic (cylinder univ 0 T) (interiorDirichletPrincipalExtension z r hr a) (min lam 1) (max upper 1) ∧
      HolderBound α (cylinder univ 0 T) (interiorDirichletPrincipalExtension z r hr a) J ∧
      (∀ i, HolderBound α (cylinder univ 0 T) (fun p => interiorDirichletDriftExtension z r hr b p i) J) ∧
      (∀ p ∈ cylinder univ 0 T, p.1 ∉ Metric.closedBall z (3*r) →
        interiorDirichletPrincipalExtension z r hr a p = 1 ∧
          ∀ i, interiorDirichletDriftExtension z r hr b p i = 0) ∧
      ∀ p ∈ cylinder (Metric.closedBall z (2*r)) 0 T,
        interiorDirichletPrincipalExtension z r hr a p = a p ∧
          ∀ i, interiorDirichletDriftExtension z r hr b p i = b p i := by
  let χ := interiorDirichletCoefficientCutoff z r hr
  have hSupport : tsupport χ ⊆ Metric.closedBall z (3*r) := by
    dsimp only [χ,interiorDirichletCoefficientCutoff]
    rw [(innerPatchBump (2*r) (by positivity) z).tsupport_eq]
    change Metric.closedBall z (3*(2*r)/2) ⊆ Metric.closedBall z (3*r)
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hSupportO : tsupport χ ⊆ O := hSupport.trans
    ((Metric.closedBall_subset_closedBall (by linarith : 3*r ≤ 4*r)).trans hInside)
  obtain ⟨P,hP,hχGlobal⟩ := innerPatchBump_global_holderBound hα hα1 (by positivity : 0 < 2*r) z
  let J : ℝ := 1+2*P*M+2*(1+P)*‖(1 : Mat n)‖
  refine ⟨J,by dsimp only [J]; positivity,?_⟩
  intro T a b hEll ha hb
  let Q := cylinder (n := n) univ 0 T
  let U := closure O ×ˢ (univ : Set ℝ)
  have hχ : HolderBound α Q (fun p => χ p.1) P := holderBound_mono hχGlobal (subset_univ Q)
  have hSub : U∩Q ⊆ cylinder (closure O) 0 T := fun p hp => ⟨hp.1.1,hp.2.2⟩
  have hZero : ∀ p ∈ Q, p ∉ U → χ p.1 = 0 := by
    intro p hp hOut
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hOut ⟨subset_closure (hSupportO hs),mem_univ _⟩
  have hProduct := holderBound_smul_cutoff_extension hχ (holderBound_mono ha hSub) hZero
  have hDrift (i : Yau.RIdx n) := holderBound_smul_cutoff_extension hχ (holderBound_mono (hb i) hSub) hZero
  have hOne := holderBound_one_sub hχ
  have hConst := holderBound_const α Q (1 : Mat n)
  have hIdentity := holderBound_smul_refined hOne hConst hOne.1 hConst.1
    (fun p hp => by simpa only [Real.norm_eq_abs] using hOne.2.1 p hp) hConst.2.1
  have hBudget : 2*P*M+((1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖) ≤ J := by dsimp only [J]; linarith
  have hEllExt := elliptic_cutoff_extension (Q := Q) (χ := fun p => χ p.1) (φ := id) hEll
    (fun p hp => ⟨(innerPatchBump (2*r) (by positivity) z).nonneg,(innerPatchBump (2*r) (by positivity) z).le_one⟩)
    (fun p hp hNonzero => ⟨subset_closure (hSupportO (subset_tsupport χ (Function.mem_support.mpr hNonzero))),hp.2⟩)
  refine ⟨hEllExt,holderBound_mono_const (holderBound_add hProduct hIdentity) hBudget,?_,?_,?_⟩
  · intro i
    change HolderBound α Q (fun p => χ p.1*b p i) J
    have hh : HolderBound α Q (fun p => χ p.1*b p i) (2*P*M) := by simpa only [smul_eq_mul] using hDrift i
    apply holderBound_mono_const hh
    dsimp only [J]
    have hNonnegative : 0 ≤ 2*(1+P)*‖(1 : Mat n)‖ := by positivity
    linarith
  · intro p hp hOut
    have hχ0 : χ p.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hOut (hSupport hs))
    change χ p.1 • a p+(1-χ p.1) • (1 : Mat n) = 1 ∧ ∀ i, χ p.1*b p i = 0
    simp only [hχ0,zero_smul,sub_zero,one_smul,zero_add,zero_mul,and_self,implies_true]
  · intro p hp
    have hχ1 : χ p.1 = 1 := innerPatchBump_eq_one (by positivity : 0 < 2*r) (by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hp.1)
    change χ p.1 • a p+(1-χ p.1) • (1 : Mat n) = a p ∧ ∀ i, χ p.1*b p i = b p i
    simp only [hχ1,one_smul,sub_self,zero_smul,add_zero,one_mul,and_self,implies_true]

/-- The actual source cutoff extends g from the actual closed domain. No
initial vanishing or corner condition is required for an interior patch. -/
theorem interiorDirichlet_source_holder {n : ℕ} {O : Set (Space n)} {α T P F : ℝ}
    (z : Space n) {r : ℝ} (hr : 0 < r) (hInside : Metric.closedBall z (4*r) ⊆ O)
    (ψ : Space n → ℝ) (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x) (hT1 : T ≤ 1)
    {g : Point n → ℝ} (hg : HolderBound α (cylinder (closure O) 0 T) g F) :
    HolderBound α (cylinder univ 0 T) (fun p => ψ p.1*g p) (2*P*F) := by
  let Q := cylinder (n := n) univ 0 T
  let U := closure O ×ˢ (univ : Set ℝ)
  have hSupport : tsupport (outerPatchBump r hr z : Space n → ℝ) ⊆ closure O := by
    rw [(outerPatchBump r hr z).tsupport_eq]
    exact ((Metric.closedBall_subset_closedBall (by linarith : 2*r ≤ 4*r)).trans hInside).trans subset_closure
  have hZero : ∀ p ∈ Q, p ∉ U → ψ p.1 = 0 := by
    intro p hp hOut
    have hNot : p.1 ∉ tsupport (outerPatchBump r hr z : Space n → ℝ) :=
      fun hs => hOut ⟨hSupport hs,mem_univ _⟩
    have h := hPlateau p.1
    rw [image_eq_zero_of_notMem_tsupport hNot,zero_mul] at h
    exact h.symm
  have hψT : HolderBound α Q (fun p => ψ p.1) P := holderBound_mono hψ
    (fun p hp => ⟨mem_univ _,hp.2.1,hp.2.2.trans hT1⟩)
  have hLocal : HolderBound α (U∩Q) g F := holderBound_mono hg (fun p hp => ⟨hp.1.1,hp.2.2⟩)
  simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension hψT hLocal hZero


/-- The actual full-drift model equation has exactly the physical cutoff
commutator as its error on the original closed domain. -/
theorem interiorDirichlet_operator {n : ℕ} {O : Set (Space n)} {T : ℝ}
    (z : Space n) {r : ℝ} (hr : 0 < r) (ψ : Space n → ℝ)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (g v : Point n → ℝ)
    (hv : C2 (cylinder univ 0 T) v)
    (hPDE : ∀ p ∈ cylinder univ 0 T, linearOp (cylinder univ 0 T)
      (interiorDirichletPrincipalExtension z r hr a) (interiorDirichletDriftExtension z r hr b) v p = ψ p.1*g p) :
    ∀ p ∈ cylinder (closure O) 0 T,
      linearOp (cylinder (closure O) 0 T) a b (interiorDirichletPatch z r hr v) p =
        ψ p.1*g p-spatialCutoffCommutator a b (outerPatchBump r hr z) v p := by
  intro p hp
  let φ : Space n → ℝ := outerPatchBump r hr z
  have hpAmbient : p ∈ cylinder univ 0 T := ⟨mem_univ _,hp.2⟩
  by_cases hx : p.1 ∈ tsupport φ
  · have hxBall : p.1 ∈ Metric.closedBall z (2*r) := by
      change p.1 ∈ tsupport (outerPatchBump r hr z : Space n → ℝ) at hx
      rw [(outerPatchBump r hr z).tsupport_eq] at hx
      exact hx
    have hχ1 : interiorDirichletCoefficientCutoff z r hr p.1 = 1 :=
      innerPatchBump_eq_one (by positivity : 0 < 2*r) (by
        simpa only [Metric.mem_closedBall,dist_eq_norm] using hxBall)
    have hOriginal : linearOp (cylinder (closure O) 0 T) a b v p = ψ p.1*g p := by
      rw [linearOp_cylinder_restrict_space a b v hp]
      have h := hPDE p hpAmbient
      simpa only [linearOp,interiorDirichletPrincipalExtension,interiorDirichletDriftExtension,
        hχ1,one_smul,sub_self,zero_smul,add_zero,one_mul] using h
    have h := linearOp_spatial_mul (Q := cylinder (closure O) 0 T) (a := a) (b := b)
      (φ := φ) (outerPatchBump r hr z).contDiff.contDiffAt (hv.2.2.2.2.1 p hpAmbient)
    rw [hOriginal] at h
    change linearOp (cylinder (closure O) 0 T) a b (fun p => φ p.1*v p) p = _
    rw [h]
    dsimp only [spatialCutoffCommutator]
    rw [←mul_assoc,hPlateau]
    ring
  · have hZero := spatial_cutoff_jets_zero_of_notMem_tsupport (cylinder (closure O) 0 T) φ v hx
    have hφ0 := image_eq_zero_of_notMem_tsupport hx
    have hψ0 : ψ p.1 = 0 := by
      have h := hPlateau p.1
      change φ p.1*ψ p.1 = ψ p.1 at h
      rw [hφ0,zero_mul] at h
      exact h.symm
    have hDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
    have hDDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (show p.1 ∉ tsupport (fderiv ℝ φ) from fun h => hx (tsupport_fderiv_subset ℝ h))
    change linearOp (cylinder (closure O) 0 T) a b (fun p => φ p.1*v p) p =
      ψ p.1*g p-spatialCutoffCommutator a b φ v p
    simp only [linearOp,hZero.2.1,hZero.2.2.1,hZero.2.2.2,hψ0,
      spatialCutoffCommutator,hDφ,hDDφ,zero_apply,zero_mul,mul_zero,
      Finset.sum_const_zero,add_zero,sub_zero]

/-- Any actual whole-space model solution yields a physical interior patch.
The cutoff has a true buffer from the frontier even when O is not assumed
open, and the lower Holder budget retains its own small factor. -/
theorem interiorDirichlet_transport {n : ℕ} {O : Set (Space n)} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hInside : Metric.closedBall z (4*r) ⊆ O) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : Space n → ℝ),
      (∀ x, outerPatchBump r hr z x*ψ x = ψ x) →
      ∀ (T K L : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (g v : Point n → ℝ),
      T ≤ 1 → SchauderBound α (cylinder univ 0 T) v K →
      HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) L →
      (∀ x, v (x,0) = 0) →
      (∀ p ∈ cylinder univ 0 T, linearOp (cylinder univ 0 T)
        (interiorDirichletPrincipalExtension z r hr a) (interiorDirichletDriftExtension z r hr b) v p = ψ p.1*g p) →
      let w := interiorDirichletPatch z r hr v
      SchauderBound α (cylinder univ 0 T) w (C*(K+L)) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*L) ∧
      (∀ x, w (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*g p-
          spatialCutoffCommutator a b (outerPatchBump r hr z) v p := by
  let φ : Space n → ℝ := outerPatchBump r hr z
  have hφ : ContDiff ℝ 2 φ := (outerPatchBump r hr z).contDiff
  have hSupport : tsupport φ ⊆ interior O := by
    dsimp only [φ]
    rw [(outerPatchBump r hr z).tsupport_eq]
    exact (Metric.closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
      (Metric.isOpen_ball.subset_interior_iff.mpr (Metric.ball_subset_closedBall.trans hInside))
  obtain ⟨J,hJ,hJets⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  let E0 := cutoffJetBudget α J r 0
  let E1 := cutoffJetBudget α J r 1
  let E2 := cutoffJetBudget α J r 2
  let E := 1+E0+E1+E2
  have hE0 : 0 ≤ E0 := by dsimp only [E0,cutoffJetBudget]; positivity
  have hE1 : 0 ≤ E1 := by dsimp only [E1,cutoffJetBudget]; positivity
  have hE2 : 0 ≤ E2 := by dsimp only [E2,cutoffJetBudget]; positivity
  have hE0' : E0 ≤ E := by dsimp only [E]; linarith
  have hE1' : E1 ≤ E := by dsimp only [E]; linarith
  have hE2' : E2 ≤ E := by dsimp only [E]; linarith
  have hJet := hJets r hr hr1 1 z φ (Or.inr rfl)
  have hφ0 : HolderBound α (cylinder univ 0 1) (fun p => φ p.1) E := by
    apply holderBound_mono_const hJet.1
    simpa only [E0,cutoffJetBudget,Nat.zero_add,pow_one] using hE0'
  have hφ1 : HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ φ p.1) E :=
    holderBound_mono_const hJet.2.1 hE1'
  have hφ2 : HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E :=
    holderBound_mono_const hJet.2.2 hE2'
  have hE : 0 ≤ E := hφ0.1
  let C : ℝ := 1+8*E
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro ψ hPlateau T K L a b g v hT1 hv hvLow hv0 hvPDE
  have hSub := cylinder_mono_time (n := n) (O := univ) hT1
  have hK : 0 ≤ K := hv.2.1
  have hL : 0 ≤ L := hvLow.1
  have hKL : 0 ≤ K+L := add_nonneg hK hL
  have hKB : K ≤ K+L := by linarith only [hL]
  have hLB : L ≤ K+L := by linarith only [hK]
  have h0 := holderBound_mono_const (holderBound_fst hvLow) hLB
  have h1 := holderBound_mono_const (holderBound_snd hvLow) hLB
  have h2 := holderBound_mono_const hv.2.2.2.1 hKB
  have ht := holderBound_mono_const hv.2.2.2.2 hKB
  have hFull := cutoff_full_jet_holderBound hφ hv.1 (holderBound_mono hφ0 hSub)
    (holderBound_mono hφ1 hSub) (holderBound_mono hφ2 hSub) h0 h1 h2 ht
  have hLow := cutoff_low_pair_holder_extension isOpen_univ hφ (subset_univ _) hv.1
    (holderBound_mono hφ0 hSub) (holderBound_mono hφ1 hSub) (holderBound_fst hvLow) (holderBound_snd hvLow)
  have hSch : SchauderBound α (cylinder univ 0 T) (fun p => φ p.1*v p) (8*E*(K+L)) := by
    refine ⟨hFull.1,hFull.2.1.1,?_,hFull.2.2.2.1,hFull.2.2.2.2⟩
    intro p hp
    exact ⟨by simpa only [Real.norm_eq_abs] using hFull.2.1.2.1 p hp,hFull.2.2.1.2.1 p hp⟩
  have hPair : HolderBound α (cylinder univ 0 T)
      (fun p => (φ p.1*v p,spatialD (fun q => φ q.1*v q) p)) (4*E*L) := by
    refine ⟨hLow.2.1.1,fun p hp => max_le (hLow.2.1.2.1 p hp) (hLow.2.2.2.1 p hp),
      fun p hp q hq => max_le (hLow.2.1.2.2 p hp q hq) (hLow.2.2.2.2 p hp q hq)⟩
  have hBudget : 8*E*(K+L) ≤ C*(K+L) := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hKL
  have hLowBudget : 4*E*L ≤ C*L := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hE]) hL
  refine ⟨schauderBound_mono_const hSch hBudget,holderBound_mono_const hPair hLowBudget,?_,?_,?_⟩
  · intro x
    change φ x*v (x,0) = 0
    rw [hv0,mul_zero]
  · intro x hx t ht
    have hNot : x ∉ tsupport φ := fun hs => hx.2 (hSupport hs)
    change φ x*v (x,t) = 0
    rw [image_eq_zero_of_notMem_tsupport hNot,zero_mul]
  · exact interiorDirichlet_operator z hr ψ hPlateau a b g v hv.1 hvPDE


/-- Actual uniform short-time interior Dirichlet patches. Source Holder data
are used only on the original closed domain, with no initial or corner
vanishing condition. The model and physical lower Holder jets remain small. -/
theorem interiorDirichlet_exists_uniform_short {n : ℕ} {O : Set (Space n)}
    {α M lam upper P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hInside : Metric.closedBall z (4*r) ⊆ O) (ψ : Space n → ℝ)
    (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (ρ T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (g : Point n → ℝ) (F : ℝ),
      0 < ρ → ρ ≤ 1 → 0 < T → T ≤ δ → T ≤ ρ^2 →
      Elliptic (cylinder (closure O) 0 T) a lam upper →
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      HolderBound α (cylinder (closure O) 0 T) g F → ∃ v w : Point n → ℝ,
      w = interiorDirichletPatch z r hr v ∧
      SchauderBound α (cylinder univ 0 T) v (C*F) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) (C*F*ρ^(1-α)) ∧
      (∀ x, v (x,0) = 0) ∧
      (∀ p ∈ cylinder univ 0 T, linearOp (cylinder univ 0 T)
        (interiorDirichletPrincipalExtension z r hr a) (interiorDirichletDriftExtension z r hr b) v p = ψ p.1*g p) ∧
      SchauderBound α (cylinder univ 0 T) w (C*F) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*F*ρ^(1-α)) ∧
      (∀ x, w (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*g p-
          spatialCutoffCommutator a b (outerPatchBump r hr z) v p := by
  obtain ⟨J,hJ,hCoefficients⟩ := interiorDirichlet_coefficient_extension
    (lam := lam) (upper := upper) hα hα1 hM z hr hInside
  obtain ⟨CG,hCG,hTransport⟩ := interiorDirichlet_transport hα hα1 z hr hr1 hInside
  obtain ⟨δ,C0,hδ,hδ1,hC0,hInverse⟩ := exists_uniform_short_schauder_inverse_holder_only
    (M := J) (lam := min lam 1) (upper := max upper 1) hα hα1 (isCompact_closedBall z (3*r))
  let A : ℝ := 1+C0*(2*P)
  let C : ℝ := 1+17*A+17*CG*A
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCGA : 0 ≤ CG*A := mul_nonneg hCG.le hA.le
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  have h16AC : 16*A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  have h17GC : 17*CG*A ≤ C := by dsimp only [C]; linarith only [hA]
  have h16GC : 16*CG*A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro ρ T a b g F hρ hρ1 hT hTδ hTρ hEll ha hb hg
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  have hF : 0 ≤ F := hg.1
  have hCoeff := hCoefficients T a b hEll ha hb
  have hSource := interiorDirichlet_source_holder z hr hInside ψ hψ hPlateau hT1 hg
  obtain ⟨v,hV,hVLow,hV0,hVPDE⟩ := hInverse T
    (interiorDirichletPrincipalExtension z r hr a) (interiorDirichletDriftExtension z r hr b)
    hT hTδ hCoeff.2.1 hCoeff.2.2.1 hCoeff.1
    (fun p hp hOut => (hCoeff.2.2.2.1 p hp hOut).1) (fun p => ψ p.1*g p) (2*P*F) hSource
  have hModelBudget : C0*(2*P*F) ≤ A*F := by dsimp only [A]; nlinarith only [hF]
  have hVA := schauderBound_mono_const hV hModelBudget
  have hSmall := zero_initial_schauder_lowPair_small hα hα1 hT hρ hρ1 hTρ hVA hV0
  have hPatch := hTransport ψ hPlateau T (A*F) (16*(A*F)*ρ^(1-α)) a b g v hT1 hVA hSmall hV0 hVPDE
  have hPower0 : 0 ≤ ρ^(1-α) := Real.rpow_nonneg hρ.le _
  have hPower1 : ρ^(1-α) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith only [hα1])
  have hModelHigh : A*F ≤ C*F := mul_le_mul_of_nonneg_right hAC hF
  have hModelLow : 16*(A*F)*ρ^(1-α) ≤ C*F*ρ^(1-α) := by
    calc
      _ = (16*A)*(F*ρ^(1-α)) := by ring
      _ ≤ C*(F*ρ^(1-α)) := mul_le_mul_of_nonneg_right h16AC (mul_nonneg hF hPower0)
      _ = _ := by ring
  have hSum : A*F+16*(A*F)*ρ^(1-α) ≤ 17*(A*F) := by
    have h := mul_le_mul_of_nonneg_left hPower1 (by positivity : 0 ≤ 16*(A*F))
    nlinarith only [h]
  have hPatchHigh : CG*(A*F+16*(A*F)*ρ^(1-α)) ≤ C*F := by
    calc
      _ ≤ CG*(17*(A*F)) := mul_le_mul_of_nonneg_left hSum hCG.le
      _ = (17*CG*A)*F := by ring
      _ ≤ C*F := mul_le_mul_of_nonneg_right h17GC hF
  have hPatchLow : CG*(16*(A*F)*ρ^(1-α)) ≤ C*F*ρ^(1-α) := by
    calc
      _ = (16*CG*A)*(F*ρ^(1-α)) := by ring
      _ ≤ C*(F*ρ^(1-α)) := mul_le_mul_of_nonneg_right h16GC (mul_nonneg hF hPower0)
      _ = _ := by ring
  exact ⟨v,interiorDirichletPatch z r hr v,rfl,schauderBound_mono_const hVA hModelHigh,
    holderBound_mono_const hSmall hModelLow,hV0,hVPDE,schauderBound_mono_const hPatch.1 hPatchHigh,
    holderBound_mono_const hPatch.2.1 hPatchLow,hPatch.2.2.1,hPatch.2.2.2.1,hPatch.2.2.2.2⟩

end Yau.LeafProofs.L16Aux
