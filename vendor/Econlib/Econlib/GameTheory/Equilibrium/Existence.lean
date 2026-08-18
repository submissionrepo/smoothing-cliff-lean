/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Problem
public import Econlib.Math.Topology.Kakutani
public import Econlib.Optimization.MaximumTheorem

/-!
# Generalized Kakutani-based Nash existence

This file defines a Kakutani fixed-point interface for Nash-like equilibrium existence results
(Nash 1951; Glicksberg 1952). `NashExistenceData` packages a finite player type, compact convex
strategy slices, continuous payoffs, and own-slice affineness, then exposes the induced
`EquilibriumProblem`. `exists_equilibrium` produces a profile satisfying the abstract
`EquilibriumProblem.IsEquilibrium` predicate.

`SymmetricExistenceData` is a single-slice version used for symmetric equilibrium arguments. The
concrete finite strategic-game and Bayesian-game modules instantiate these abstractions with
standard simplices.

## Main definitions

* `NashExistenceData`: Bundled data for per-player slices, payoffs, continuity, and affineness.
* `NashExistenceData.Profile`: Dependent product of subtype slices.
* `NashExistenceData.toEquilibriumProblem`: The matching abstract `EquilibriumProblem`.
* `SymmetricExistenceData`: Data for single-slice symmetric fixed-point arguments.

## Main statements

* `NashExistenceData.exists_equilibrium`: Kakutani-based existence of an equilibrium profile.
* `SymmetricExistenceData.exists_symmetric_fixed_point`: Kakutani-based existence of a symmetric
  fixed point.

## Notes

The packaged hypotheses match the fixed-point requirements for best-response correspondences:
Compact nonempty strategy slices, closed graphs for the argmax correspondence, and convex
best-response sets from own-slice affineness.

## References

* Glicksberg, I. L. 1952. “A Further Generalization of the Kakutani Fixed Point Theorem, With
  Application to Nash Equilibrium Points.” *Proceedings of the American Mathematical Society* 3
  (1): 170. [https://doi.org/10.2307/2032478](https://doi.org/10.2307/2032478).
* Nash, John. 1951. “Non-Cooperative Games.” *The Annals of Mathematics* 54 (2): 286.
  [https://doi.org/10.2307/1969529](https://doi.org/10.2307/1969529).

## Tags

game theory, equilibrium, nash equilibrium, kakutani, fixed point
-/

@[expose] public section

namespace Econlib.GameTheory

universe u v

/-- Data needed to invoke generalized Kakutani for Nash equilibrium existence. Each player `i`
chooses a strategy in a slice `Slice i ⊆ V i`, where `V i` is a finite-dimensional real-normed
space. Players, slices, and the payoff functional are provided by the user; the existence theorem
`NashExistenceData.exists_equilibrium` produces a profile satisfying the abstract
`EquilibriumProblem.IsEquilibrium` predicate associated to the data via `toEquilibriumProblem`. -/
structure NashExistenceData where
  /-- Player index. -/
  Player : Type u
  [instFintypePlayer : Fintype Player]
  [instInhabitedPlayer : Inhabited Player]
  [instDecEqPlayer : DecidableEq Player]
  /-- Per-player ambient strategy space. -/
  V : Player → Type v
  [instNAG : ∀ i, NormedAddCommGroup (V i)]
  [instNS : ∀ i, NormedSpace ℝ (V i)]
  [instFD : ∀ i, FiniteDimensional ℝ (V i)]
  /-- Per-player strategy slice. -/
  Slice : (i : Player) → Set (V i)
  hSlice_convex : ∀ i, Convex ℝ (Slice i)
  hSlice_compact : ∀ i, IsCompact (Slice i)
  hSlice_nonempty : ∀ i, (Slice i).Nonempty
  /-- Per-player payoff. -/
  payoff : (i : Player) → ((j : Player) → ↑(Slice j)) → ℝ
  payoff_continuous : ∀ i, Continuous (payoff i)
  /-- Affine in own slice: For every fixed `σ`, the map `y ↦ payoff i (update σ i y)` is the
  restriction of an affine map on `V i`. This suffices for convexity of the argmax. -/
  payoff_affine_in_own : ∀ (i : Player) (σ : (j : Player) → ↑(Slice j)),
    ∃ aff : V i →ᵃ[ℝ] ℝ,
      ∀ y : ↑(Slice i), aff y.1 = payoff i (Function.update σ i y)

attribute [instance] NashExistenceData.instFintypePlayer NashExistenceData.instInhabitedPlayer
  NashExistenceData.instDecEqPlayer NashExistenceData.instNAG NashExistenceData.instNS
  NashExistenceData.instFD

namespace NashExistenceData

variable (D : NashExistenceData)

/-- Profile space induced by the data: A strategy choice in each slice, dependently. -/
abbrev Profile : Type _ := (i : D.Player) → ↑(D.Slice i)

/-- The equilibrium problem associated to the data. The deviator is the player; the swap relation
is unilateral update of the slice choice; the value is the payoff. -/
def toEquilibriumProblem : EquilibriumProblem where
  S := D.Profile
  I := D.Player
  swap i σ σ' := ∃ y : ↑(D.Slice i), σ' = Function.update σ i y
  value := D.payoff

/-! ### Internal Kakutani proof

The proof works in raw `(i : Player) → V i` space — convenient for Kakutani's
finite-dimensional setup — and lifts back to the subtype profile at the end. -/

/-- Raw strategy set: The dependent product of the slices, viewed as a subset of
`(i : Player) → V i`. -/
def mixedStrategySet : Set ((i : D.Player) → D.V i) :=
  Set.pi Set.univ D.Slice

/-- Bridge: A raw element `x` lying in `mixedStrategySet` corresponds canonically to a subtype-form
profile. -/
def liftToProfile {x : (i : D.Player) → D.V i} (hx : x ∈ D.mixedStrategySet) : D.Profile :=
  fun i => ⟨x i, hx i (Set.mem_univ i)⟩

lemma mixedStrategySet_convex : Convex ℝ D.mixedStrategySet :=
  convex_pi (fun i _ => D.hSlice_convex i)

lemma mixedStrategySet_compact : IsCompact D.mixedStrategySet :=
  isCompact_univ_pi (fun i => D.hSlice_compact i)

lemma mixedStrategySet_nonempty : D.mixedStrategySet.Nonempty := by
  choose y hy using D.hSlice_nonempty
  exact ⟨y, fun i _ => hy i⟩

/-- Best-response correspondence at raw background `x ∈ mixedStrategySet`: Candidates `y` in the
same set such that, for each player `i`, the slice element at `i` extracted from `y` is at least as
good against the lift of `x` as any other slice element. -/
def bestResponseSet (x : ↑D.mixedStrategySet) :
    Set ((i : D.Player) → D.V i) :=
  { y |
    ∃ hy : y ∈ D.mixedStrategySet,
      ∀ i (z : ↑(D.Slice i)),
        D.payoff i (Function.update (D.liftToProfile x.2) i ⟨y i, hy i (Set.mem_univ i)⟩) ≥
        D.payoff i (Function.update (D.liftToProfile x.2) i z) }

lemma bestResponseSet_subset (x : ↑D.mixedStrategySet) :
    D.bestResponseSet x ⊆ D.mixedStrategySet :=
  fun _ hy => hy.1

/-- The payoff to player `i` of deviating to slice element `z` against background `x`. Private
bridge function: Its argmax over the slice subtype is player `i`'s component of the best-response
set (`bestResponseSet_eq`). -/
private def slicePayoff (i : D.Player) (x : ↑D.mixedStrategySet) (z : ↑(D.Slice i)) : ℝ :=
  D.payoff i (Function.update (D.liftToProfile x.2) i z)

/-- Updating a profile at one coordinate is jointly continuous in (profile, new value). -/
private lemma update_continuous (i : D.Player) :
    Continuous fun q : D.Profile × ↑(D.Slice i) => Function.update q.1 i q.2 := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · have hrw : (fun q : D.Profile × ↑(D.Slice i) => Function.update q.1 i q.2 j) =
        fun q => hj ▸ q.2 := by
      funext q
      subst hj
      rw [Function.update_self]
    rw [hrw]
    cases hj
    exact continuous_snd
  · have hrw : (fun q : D.Profile × ↑(D.Slice i) => Function.update q.1 i q.2 j) =
        fun q => q.1 j := by
      funext q
      rw [Function.update_of_ne hj]
    rw [hrw]
    exact (continuous_apply j).comp continuous_fst

private lemma slicePayoff_continuous (i : D.Player) :
    Continuous fun p : ↑D.mixedStrategySet × ↑(D.Slice i) => D.slicePayoff i p.1 p.2 := by
  have h_lift : Continuous fun p : ↑D.mixedStrategySet × ↑(D.Slice i) =>
      D.liftToProfile p.1.2 :=
    continuous_pi fun j => Continuous.subtype_mk
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)) _
  exact (D.payoff_continuous i).comp ((D.update_continuous i).comp (h_lift.prodMk continuous_snd))

/-- The best-response set is the product over players of the (slice-inclusion images of the)
per-player argmax sets. Private bridge to the Berge/argmax engine in `Econlib.Optimization`. -/
private lemma bestResponseSet_eq (x : ↑D.mixedStrategySet) :
    D.bestResponseSet x = Set.univ.pi fun i =>
      Subtype.val '' Optimization.argmax (D.slicePayoff i x) Set.univ := by
  ext y
  simp only [Set.mem_univ_pi]
  constructor
  · rintro ⟨hy, hopt⟩ i
    exact ⟨⟨y i, hy i (Set.mem_univ i)⟩, ⟨Set.mem_univ _, fun z _ => hopt i z⟩, rfl⟩
  · intro h
    have hy : y ∈ D.mixedStrategySet := by
      intro i _
      obtain ⟨w, -, hw⟩ := h i
      exact hw ▸ w.2
    refine ⟨hy, fun i z => ?_⟩
    obtain ⟨w, ⟨-, hw_max⟩, hw⟩ := h i
    have h_wi : (⟨y i, hy i (Set.mem_univ i)⟩ : ↑(D.Slice i)) = w := Subtype.ext hw.symm
    rw [h_wi]
    exact hw_max (Set.mem_univ z)

lemma bestResponseSet_nonempty (x : ↑D.mixedStrategySet) :
    (D.bestResponseSet x).Nonempty := by
  rw [bestResponseSet_eq, Set.univ_pi_nonempty_iff]
  intro i
  haveI : CompactSpace ↑(D.Slice i) := isCompact_iff_compactSpace.mp (D.hSlice_compact i)
  haveI : Nonempty ↑(D.Slice i) := (D.hSlice_nonempty i).to_subtype
  have h_cont : Continuous (D.slicePayoff i x) :=
    (D.slicePayoff_continuous i).comp (continuous_const.prodMk continuous_id)
  exact (Optimization.argmax_nonempty isCompact_univ Set.univ_nonempty h_cont.continuousOn).image _

lemma bestResponseSet_convex (x : ↑D.mixedStrategySet) :
    Convex ℝ (D.bestResponseSet x) := by
  rw [bestResponseSet_eq]
  refine convex_pi fun i _ => ?_
  obtain ⟨aff, h_aff⟩ := D.payoff_affine_in_own i (D.liftToProfile x.2)
  -- An affine objective is concave, hence quasiconcave, on the convex slice.
  have h_conc : ConcaveOn ℝ (D.Slice i) ⇑aff :=
    ⟨D.hSlice_convex i, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).ge⟩
  have h_match : ∀ z : ↑(D.Slice i), D.slicePayoff i x z = aff z.1 := fun z => (h_aff z).symm
  rw [Optimization.image_val_argmax_univ h_match]
  exact Optimization.argmax_convex h_conc.quasiconcaveOn

lemma bestResponseSet_closedGraph :
    IsClosedGraph (fun x : ↑D.mixedStrategySet => D.bestResponseSet x) := by
  -- Per-player: Berge with the constant full-slice constraint gives a UHC, compact-valued argmax
  -- correspondence, hence a closed graph, transferred along the slice inclusion.
  have h_player (i : D.Player) : IsClosed { w : ↑D.mixedStrategySet × D.V i |
      w.2 ∈ Subtype.val '' Optimization.argmax (D.slicePayoff i w.1) Set.univ } := by
    haveI : CompactSpace ↑(D.Slice i) := isCompact_iff_compactSpace.mp (D.hSlice_compact i)
    haveI : Nonempty ↑(D.Slice i) := (D.hSlice_nonempty i).to_subtype
    have hf_cont := D.slicePayoff_continuous i
    have h_uhc : UpperHemicontinuous fun x : ↑D.mixedStrategySet =>
        Optimization.argmax (D.slicePayoff i x) Set.univ :=
      Optimization.argmax_upperHemicontinuous hf_cont .const .const
        (fun _ => isCompact_univ) fun _ => Set.univ_nonempty
    exact (h_uhc.isClosedGraph fun x =>
      (Optimization.argmax_isCompact (f := D.slicePayoff i) hf_cont
        (fun _ => isCompact_univ) x).isClosed).image_subtypeVal (D.hSlice_compact i).isClosed
  -- Assemble: the graph of the product correspondence is the intersection over players of the
  -- preimages of the per-player graphs under the coordinate maps `(x, y) ↦ (x, y i)`.
  have h_graph_eq : { z : ↑D.mixedStrategySet × ((j : D.Player) → D.V j) |
        z.2 ∈ D.bestResponseSet z.1 } =
      ⋂ i, (fun z : ↑D.mixedStrategySet × ((j : D.Player) → D.V j) => (z.1, z.2 i)) ⁻¹'
        { w : ↑D.mixedStrategySet × D.V i |
          w.2 ∈ Subtype.val '' Optimization.argmax (D.slicePayoff i w.1) Set.univ } := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, bestResponseSet_eq,
      Set.mem_univ_pi]
  rw [IsClosedGraph, h_graph_eq]
  exact isClosed_iInter fun i => (h_player i).preimage
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

/-- **Generalized Kakutani-based Nash existence.** -/
theorem exists_equilibrium :
    ∃ σ : D.Profile, D.toEquilibriumProblem.IsEquilibrium σ := by
  letI : NormedAddCommGroup ((i : D.Player) → D.V i) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ ((i : D.Player) → D.V i) := Pi.normedSpace
  letI : FiniteDimensional ℝ ((i : D.Player) → D.V i) :=
    FiniteDimensional.finiteDimensional_pi' ℝ D.V
  have h_convex : Convex ℝ D.mixedStrategySet := D.mixedStrategySet_convex
  obtain ⟨⟨xstar, hxstar⟩, h_fixed⟩ := kakutaniFixedPoint
    D.mixedStrategySet h_convex D.mixedStrategySet_compact
    D.mixedStrategySet_nonempty
    (fun x => D.bestResponseSet x) D.bestResponseSet_closedGraph
    (fun x => ⟨D.bestResponseSet_subset x, D.bestResponseSet_convex x,
      D.bestResponseSet_nonempty x⟩)
  obtain ⟨h_mem, h_opt⟩ := h_fixed
  refine ⟨D.liftToProfile h_mem, ?_⟩
  intro i σ' hswap
  obtain ⟨y, hy⟩ := hswap
  subst hy
  have hopt_i := h_opt i y
  -- The updated profile reinserts the slice element already present at `i`, so it is unchanged.
  have h_lhs : Function.update (D.liftToProfile hxstar) i
      ⟨xstar i, h_mem i (Set.mem_univ i)⟩ = D.liftToProfile hxstar :=
    Function.update_eq_self (β := fun i => ↑(D.Slice i)) i _
  rw [h_lhs] at hopt_i
  exact hopt_i

end NashExistenceData

/-! ### Single-slice (symmetric) Kakutani existence

For symmetric games and other single-player-type setups where the deviator and the opponent
live in the same slice. The fixed-point output is `x ∈ Slice` with `x` being a best response to
itself, i.e. `∀ y ∈ Slice, payoff x x ≥ payoff y x`. -/

/-- Data needed to invoke Kakutani for **symmetric** equilibrium existence on a single slice. The
two-argument payoff `payoff own opp` records the deviator's value when they play `own` against an
opponent at `opp`. Required: Continuity jointly and affineness in `own` for every fixed `opp`. -/
structure SymmetricExistenceData where
  /-- Ambient strategy space. -/
  V : Type v
  [instNAG : NormedAddCommGroup V]
  [instNS : NormedSpace ℝ V]
  [instFD : FiniteDimensional ℝ V]
  /-- Strategy slice. -/
  Slice : Set V
  hSlice_convex : Convex ℝ Slice
  hSlice_compact : IsCompact Slice
  hSlice_nonempty : Slice.Nonempty
  /-- Asymmetric two-argument payoff: `payoff own opp`. -/
  payoff : ↑Slice → ↑Slice → ℝ
  payoff_continuous : Continuous (Function.uncurry payoff)
  /-- For every fixed `opp`, `own ↦ payoff own opp` is the restriction of an affine map on the
  ambient `V`. This suffices for convexity of the argmax. -/
  payoff_affine_in_own : ∀ (opp : ↑Slice),
    ∃ aff : V →ᵃ[ℝ] ℝ, ∀ own : ↑Slice, aff own.1 = payoff own opp

attribute [instance] SymmetricExistenceData.instNAG SymmetricExistenceData.instNS
  SymmetricExistenceData.instFD

namespace SymmetricExistenceData

variable (D : SymmetricExistenceData)

/-- Best-response set: Candidates `y` in `Slice` such that `payoff ⟨y, _⟩ x` dominates `payoff z x`
for every `z ∈ Slice`. -/
def symmetricBR (x : ↑D.Slice) : Set D.V :=
  { y | ∃ hy : y ∈ D.Slice, ∀ z : ↑D.Slice, D.payoff ⟨y, hy⟩ x ≥ D.payoff z x }

lemma symmetricBR_subset (x : ↑D.Slice) : D.symmetricBR x ⊆ D.Slice :=
  fun _ h => h.1

/-- `symmetricBR` is the inclusion image of the argmax of the deviation payoff over the slice
subtype. Private bridge to the Berge/argmax engine in `Econlib.Optimization`. -/
private lemma symmetricBR_eq (x : ↑D.Slice) :
    D.symmetricBR x =
      Subtype.val '' Optimization.argmax (fun z : ↑D.Slice => D.payoff z x) Set.univ := by
  ext y
  constructor
  · rintro ⟨hy, hopt⟩
    exact ⟨⟨y, hy⟩, ⟨Set.mem_univ _, fun z _ => hopt z⟩, rfl⟩
  · rintro ⟨w, ⟨-, hw_max⟩, rfl⟩
    exact ⟨w.2, fun z => hw_max (Set.mem_univ z)⟩

lemma symmetricBR_nonempty (x : ↑D.Slice) : (D.symmetricBR x).Nonempty := by
  haveI : CompactSpace ↑D.Slice := isCompact_iff_compactSpace.mp D.hSlice_compact
  haveI : Nonempty ↑D.Slice := D.hSlice_nonempty.to_subtype
  have h_cont : Continuous fun z : ↑D.Slice => D.payoff z x :=
    D.payoff_continuous.comp (continuous_id.prodMk continuous_const)
  rw [symmetricBR_eq]
  exact (Optimization.argmax_nonempty isCompact_univ Set.univ_nonempty h_cont.continuousOn).image _

lemma symmetricBR_convex (x : ↑D.Slice) : Convex ℝ (D.symmetricBR x) := by
  obtain ⟨aff, h_aff⟩ := D.payoff_affine_in_own x
  -- An affine objective is concave, hence quasiconcave, on the convex slice.
  have h_conc : ConcaveOn ℝ D.Slice ⇑aff :=
    ⟨D.hSlice_convex, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).ge⟩
  rw [symmetricBR_eq, Optimization.image_val_argmax_univ fun z => (h_aff z).symm]
  exact Optimization.argmax_convex h_conc.quasiconcaveOn

lemma symmetricBR_closedGraph : IsClosedGraph D.symmetricBR := by
  haveI : CompactSpace ↑D.Slice := isCompact_iff_compactSpace.mp D.hSlice_compact
  haveI : Nonempty ↑D.Slice := D.hSlice_nonempty.to_subtype
  have hf_cont : Continuous fun p : ↑D.Slice × ↑D.Slice => D.payoff p.2 p.1 :=
    D.payoff_continuous.comp (continuous_snd.prodMk continuous_fst)
  -- Berge with the constant full-slice constraint: the argmax correspondence is UHC with
  -- compact (hence closed) values, so it has a closed graph; transfer along the inclusion.
  have h_uhc : UpperHemicontinuous fun x : ↑D.Slice =>
      Optimization.argmax (fun z : ↑D.Slice => D.payoff z x) Set.univ :=
    Optimization.argmax_upperHemicontinuous hf_cont .const .const
      (fun _ => isCompact_univ) fun _ => Set.univ_nonempty
  have h_graph := (h_uhc.isClosedGraph fun x =>
    (Optimization.argmax_isCompact (f := fun x z => D.payoff z x) hf_cont
      (fun _ => isCompact_univ) x).isClosed).image_subtypeVal D.hSlice_compact.isClosed
  have h_fun_eq : D.symmetricBR = fun x => Subtype.val ''
      Optimization.argmax (fun z : ↑D.Slice => D.payoff z x) Set.univ :=
    funext (symmetricBR_eq D)
  rw [h_fun_eq]
  exact h_graph

/-- **Single-slice Kakutani fixed-point existence.** -/
theorem exists_symmetric_fixed_point :
    ∃ x : ↑D.Slice, ∀ y : ↑D.Slice, D.payoff x x ≥ D.payoff y x := by
  obtain ⟨xstar, hxstar⟩ := kakutaniFixedPoint
    D.Slice D.hSlice_convex D.hSlice_compact D.hSlice_nonempty
    D.symmetricBR D.symmetricBR_closedGraph
    (fun x => ⟨D.symmetricBR_subset x, D.symmetricBR_convex x, D.symmetricBR_nonempty x⟩)
  obtain ⟨_, hopt⟩ := hxstar
  exact ⟨xstar, hopt⟩

end SymmetricExistenceData

end Econlib.GameTheory
